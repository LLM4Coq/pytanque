from .protocol import State, Opts
from .client import Pytanque, PetanqueError
from .search import BFS
from typing import Optional, List, Callable
import re
from dataclasses import dataclass, field


def remove_comments(code):
    """
    Remove coq nested comments, e.g., (* this is a comment (* - induction n *) *).
    """

    # Remove code block delimiter
    code = code.strip()
    if code.startswith("```"):
        code = code[3:]
    if code.endswith("```"):
        code = code[:-3]
    code = code.strip()

    pattern = re.compile(r"\(\*|\*\)")

    start = 0
    nested = 0
    indices_to_remove = []

    for match in pattern.finditer(code):
        if match.group() == "(*":
            nested += 1
            start = match.start()
        elif match.group() == "*)":
            nested -= 1
            if not nested:
                indices_to_remove.append((start, match.end()))

    cleaned_code = ""
    last_index = 0
    for start, end in indices_to_remove:
        cleaned_code += code[last_index:start]
        last_index = end
    cleaned_code += code[last_index:]

    return cleaned_code


def split_proof(proof: str) -> List[str]:
    raw = remove_comments(proof)  # remove comments
    tactics = [
        t
        for b in re.split(r"(\++|\*+|\-+|{|})", raw)  # split proof in bullets
        for s in re.split(r"(?<=\.)\s", b)  # split bullets in tactics
        if (t := s.strip())  # remove empty steps
    ]
    return ["{", *tactics, "}"]


def check_final_state(pet: Pytanque, state: State) -> bool:
    g = pet.goals(state)
    return not g.goals and all(e == ([], []) for e in g.stack)


@dataclass
class Schema:
    tactics: List[str] = field(default_factory=list)
    admit_idx: List[int] = field(default_factory=list)
    admit_states: List[State] = field(default_factory=list)
    admit_errors: List[str | None] = field(default_factory=list)

    def __repr__(self):
        steps = map(
            lambda s: "\n " + s if s.startswith(("+", "-", "*")) else s,
            self.tactics,
        )
        return " ".join(steps)


def fix_proof(
    pet: Pytanque,
    state: State,
    proof: str,
    opts: Optional[Opts] = None,
) -> Schema:

    schema = Schema()

    def fix(state: State, idx: int, tactics: List[str], drop: bool) -> Schema:
        if not tactics:
            return schema

        tac = tactics[0]
        try:
            next_state = pet.run_tac(state, tac, opts)
            schema.tactics.append(tac)
            if tac == "admit.":
                schema.admit_idx.append(idx)
                schema.admit_states.append(state)
            return fix(next_state, idx + 1, tactics[1:], False)

        except PetanqueError as err:
            if drop:  # still invalid, drop tactic.
                return fix(state, idx, tactics[1:], True)
            if m := re.match(
                r"Coq: \[Focus\] Wrong bullet (?:\++|\-+|\*+): Expecting (?P<bullet>\++|\-+|\*+)",
                err.message,
            ):  # refocus on correct bullet
                return fix(state, idx, [m.group("bullet")] + tactics, False)
            if m := re.match(
                r"Coq: No such goal. Focus next goal with bullet (?P<bullet>\++|\-+|\*+)",
                err.message,
            ):  # refocus on correct bullet
                return fix(state, idx, [m.group("bullet")] + tactics, False)
            if re.match(
                r"Coq: \[Focus\] Wrong bullet (?:\++|\-+|\*+): Current bullet (?:\++|\-+|\*+) is not finished.",
                err.message,
            ):  # close previous subgoal and retry.
                schema.admit_errors.append(err.message)
                return fix(state, idx, ["admit."] + tactics, False)
            if re.match(
                r"Coq: This proof is focused, but cannot be unfocused this way",
                err.message,
            ):  # close current goal and try to unfocus
                schema.admit_errors.append(err.message)
                return fix(state, idx, ["admit."] + tactics, False)
            if re.match(
                r"Coq: \[Focus\] Wrong bullet (?:\++|\-+|\*+): No more goals.",
                err.message,
            ):  # Drop bullet
                return fix(state, idx, tactics[1:], True)
            else:  # replace tac by admit and drop until next valid tactic.
                schema.admit_errors.append(err.message)
                return fix(state, idx, ["admit."] + tactics[1:], True)

    tactics = split_proof(proof)
    schema = fix(state, 0, tactics, False)
    match schema.tactics:  # remove nested admit.
        case ["{", "admit.", "}"]:
            schema.tactics = ["admit."]
            schema.admit_idx = [0]
    return schema


from openai import OpenAI

client = OpenAI(
    project="XXXX",
    api_key="XXXX",
)


def init_prompt(context: str, goal: str) -> str:
    return f"""
I want you to prove a theorem using the Coq proof assistant.
I will give you the context and a description of the goal.
Answer with a single code block containing the proof. Do not repeat the context, do no restate the theorem, and don't try to explain the code. Always name hypothesis new equations.  

Here is an example of a response:
```
intros.
induction n.
- lia.
- lia.
```


Ready?

Here is the context with some definitions.
```
{context}
```

And here is the current goal:
```
{goal}
```
"""


def next_prompt(goal: str) -> str:
    return f"""
Now the goal is:
```
{goal}
```
What is the proof?
"""


def tactics_prompt(goal: str, num_samples: int) -> str:
    return f"""
Let's play a game.
We are trying to prove a theorem using the Coq proof assistant.
I will give you the current state of the prover as a code block, and you answer with a list of {num_samples} possible tactics, ordered from the most promising one to the least promising one. Each tactics should be associated to a confidence score, i.e., a positive number.

For instance, here is a possible state:

```
n  : nat
IHn  : 2 * n = n + n
-----------------------------
2 * S n = S n + S n
```

And here is a possible answer:

```
[("lia.", 0.8), ("auto.", 0.6), ("simpl.", 0.4), ...]
```

Answer with a single code block.
Ready? Take a deep breath.

Here is your goal:

```
{goal}
```
"""


import ast


class GPTAgent:
    def __init__(self, pet: Pytanque):
        self.pet = pet
        self.messages = []
        self.schema = Schema()
        self.proof = []

    def ask_gpt(self, prompt: str, n: int = 1) -> str:
        self.messages.append({"role": "user", "content": prompt})
        resp = client.chat.completions.create(
            messages=self.messages, model="gpt-4o", n=n
        )
        content = resp.choices[0].message.content
        if not content:
            raise PetanqueError(1, "GPT Error")
        self.messages.append({"role": "assistant", "content": content})
        return content

    def start(self, context, state) -> Schema:
        current_goal = self.pet.goals(state).goals[0].pp()
        proof = self.ask_gpt(init_prompt(context, current_goal))
        self.schema = fix_proof(self.pet, state, proof)
        return self.schema

    def schema_generator(self, state) -> str:
        current_goal = self.pet.goals(state).goals[0].pp()
        prompt = next_prompt(current_goal)
        return self.ask_gpt(prompt)

    def bfs_generator(self, state) -> str:

        num_samples = 10
        max_iters = 10

        def gen(state, num_samples):
            current_goal = self.pet.goals(state).goals[0].pp()
            code = self.ask_gpt(tactics_prompt(current_goal, num_samples))

            # Remove code block delimiter
            code = code.strip()
            if code.startswith("```"):
                code = code[3:]
            if code.endswith("```"):
                code = code[:-3]
            code = code.strip()

            tactics, scores = list(zip(*ast.literal_eval(code)))
            return (
                list(map(lambda t: f"{t}{'.' if t[-1] != '.' else ''}", tactics)),
                scores,
            )

        bfs = BFS(max_iters, num_samples, pet=self.pet, tactic_generator=gen)
        try:
            proof = bfs.search(state)
            return " ".join(proof)
        except:
            return "admit."

    def next(self, proof_generator: Callable[[State], str]) -> Schema:
        if not self.schema:
            raise PetanqueError(0, "Undefined schema")

        assert len(self.schema.admit_idx) == len(self.schema.admit_states)

        schema = Schema()

        offset = 0
        p_ai = -1

        for state, ai, err in zip(
            self.schema.admit_states, self.schema.admit_idx, self.schema.admit_errors
        ):

            sub_proof = proof_generator(state)
            print(f"Trying:\n {sub_proof}\n")
            sub_schema = fix_proof(self.pet, state, sub_proof)
            print(f"Got:\n {sub_schema}\n")

            schema.tactics += self.schema.tactics[p_ai + 1 : ai] + sub_schema.tactics
            schema.admit_states += sub_schema.admit_states
            schema.admit_errors += sub_schema.admit_errors
            schema.admit_idx += [ai + offset + k for k in sub_schema.admit_idx]

            offset += len(sub_schema.tactics) - 1
            p_ai = ai

        schema.tactics += self.schema.tactics[p_ai + 1 :]

        if schema.tactics == self.schema.tactics:
            raise PetanqueError(0, "No proof found")
        self.schema = schema
        return self.schema

    def recursive_search(
        self, context, file_name: str, thm_name: str, max_depth: int = 5
    ) -> Schema:

        state = self.pet.start(file=file_name, thm=thm_name)
        self.start(context, state)
        print(f"Initial schema\n{self.schema}\n")

        def search(depth: int) -> Schema:
            if depth == 0:
                raise PetanqueError(0, "No proof found")
            if not self.schema.admit_states:
                return self.schema
            self.next(self.schema_generator)
            return search(depth - 1)

        return search(max_depth)

    def schema_best_first(self, context, file_name: str, thm_name: str):
        state = self.pet.start(file=file_name, thm=thm_name)
        self.start(context, state)
        print(f"Initial schema\n{self.schema}\n")
        return self.next(self.bfs_generator)
