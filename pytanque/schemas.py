from .protocol import State, Opts
from .client import Pytanque, PetanqueError
from typing import Optional, List
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
                return fix(state, idx, [m.group("bullet"), "admit."] + tactics, False)
            if re.match(
                r"Coq: \[Focus\] Wrong bullet (?:\++|\-+|\*+): Current bullet (?:\++|\-+|\*+) is not finished.",
                err.message,
            ):  # close previous subgoal and retry.
                return fix(state, idx, ["admit."] + tactics, False)
            if re.match(
                r"Coq: \[Focus\] Wrong bullet (?:\++|\-+|\*+): No more goals.",
                err.message,
            ):
                return fix(state, idx, tactics[1:], True)
            else:  # replace tac by admit and drop until next valid tactic.
                return fix(state, idx, ["admit."] + tactics[1:], True)

    tactics = split_proof(proof)
    schema = fix(state, 0, tactics, False)
    match schema.tactics:  # remove nested admit.
        case ["{", "admit.", "}"]:
            schema.tactics = ["admits"]
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


class GPTAgent:
    def __init__(self, pet: Pytanque):
        self.pet = pet
        self.messages = []
        self.schema = Schema()
        self.proof = []

    def ask_gpt(self, prompt: str) -> str:
        self.messages.append({"role": "user", "content": prompt})
        resp = client.chat.completions.create(
            messages=self.messages,
            model="gpt-4o",
        )
        content = resp.choices[0].message.content
        if not content:
            raise PetanqueError(1, "GPT Error")
        self.messages.append({"role": "assistant", "content": content})
        return content

    def start(self, context, state):
        current_goal = self.pet.goals(state).goals[0].pp()
        proof = self.ask_gpt(init_prompt(context, current_goal))
        print(f"\nAssistant:\n\n {proof}")
        self.schema = fix_proof(self.pet, state, proof)
        return self.schema

    def next(self):
        if not self.schema:
            raise PetanqueError(0, "Undefined schema")

        assert len(self.schema.admit_idx) == len(self.schema.admit_states)

        schema = Schema()

        def update(
            idx: int, admit_states: List[State], admit_inter: List[int]
        ) -> Schema:
            if not admit_states:
                i = admit_inter[0]
                schema.tactics += self.schema.tactics[i + 1 :]
                return schema

            next_state = admit_states[0]
            [i, j, *_] = admit_inter
            current_goal = self.pet.goals(next_state).goals[0].pp()
            prompt = next_prompt(current_goal)
            print(f"\nUser:\n\n {prompt}")
            sub_proof = self.ask_gpt(prompt)
            print(f"\nAssistant:\n\n {sub_proof}")
            sub_schema = fix_proof(self.pet, next_state, sub_proof)
            print(f"\nSubproof:\n{sub_schema}")

            schema.tactics += self.schema.tactics[i + 1 : j] + sub_schema.tactics
            schema.admit_states += sub_schema.admit_states
            schema.admit_idx += [idx + (j - i - 1) + k for k in sub_schema.admit_idx]
            return update(
                idx + (j - i - 1) + len(sub_schema.tactics),
                admit_states[1:],
                admit_inter[1:],
            )

        next_schema = update(0, self.schema.admit_states, [-1] + self.schema.admit_idx)
        if next_schema.tactics == self.schema.tactics:
            raise PetanqueError(0, "No proof found")
        self.schema = next_schema
        return self.schema
