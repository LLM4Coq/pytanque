import os
from openai import OpenAI
from .client import Pytanque, PetanqueError, State
from .schema import Schema, build_schema, fill_schema
from typing import Callable
import re
from copy import deepcopy
import time

client = OpenAI(
    project=os.environ["OPENAI_PROJECT"],
    api_key=os.environ["OPENAI_API_KEY"],
)


init_prompt = """ 
Your task is to prove a theorem using the Coq proof assistant.
For each theorem, I will give you the goal to prove in Coq syntax.

Here are a few examples:

<example>
<goal>
n, m, p : nat
|- nat, n + (m + p) = m + (n + p)
</goal>

<proof>
rewrite Nat.add_assoc. rewrite Nat.add_assoc.
assert (n + m = m + n) as H by apply Nat.add_comm.
rewrite H. reflexivity.
</proof>
</example>


<example>
<context>
<goal>
|- forall n:nat, n + 0 = n
</goal>

<proof>
intros n. induction n as [| n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
</proof>
</example>

<example>
<goal>
f nat -> nat 
I forall n : nat, n = f (f n) 
n1n2 nat 
H f n1 = f n2 
|- n1 = n2
</goal>

<proof>
rewrite (I n1). rewrite H.
rewrite <- I. reflexivity.
</proof>
</example>

Think before you write the proof in <thinking> tags. First explain the goal. Then describe the proof step by step. Finally write the corresponding Coq proof in <proof> tags using your analysis.

Ready? Here is the goal.
<goal>
{goal}
</goal>

Take a deep breath and walk me through the proof.
"""

next_prompt = """  
Now the goal is:
```
{goal}
```
What is the proof?
"""


class GPTAgent:
    def __init__(self, pet: Pytanque, log_prefix):
        self.pet = pet
        self.messages = []
        self.schema = Schema()
        self.log_prefix = log_prefix
        self.logfile_name = f"{log_prefix}_{time.strftime("%y%m%d-%H%M%S")}.log"

    def reset(self):
        self.messages = []
        self.schema = Schema()
        self.logfile_name = f"{self.log_prefix}_{time.strftime("%y%m%d-%H%M%S")}.log"

    def ask_gpt(self, prompt: str, n: int = 1) -> str:
        self.messages.append({"role": "user", "content": prompt})
        resp = client.chat.completions.create(
            messages=self.messages, model="gpt-4o", n=n
        )
        content = resp.choices[0].message.content
        with open(self.logfile_name, "a") as logfile:
            print(f"User: {prompt}\n", file=logfile)
            print(f"GPT: {content}\n\n", file=logfile)
        if not content:
            raise PetanqueError(1, "GPT Error")
        self.messages.append({"role": "assistant", "content": content})
        tag_pattern = r"<proof>(.*?)</proof>"
        if match := re.search(tag_pattern, content, re.DOTALL):
            return match.group(1).strip()
        md_pattern = r"```coq(.*?)```"
        if match := re.search(md_pattern, content, re.DOTALL):
            return match.group(1).strip()
        raise PetanqueError(1, "GPT Error")

    def start(self, state: State) -> Schema:
        current_goal = self.pet.goals(state)[0].pp
        prompt = init_prompt.format(goal=current_goal)
        proof = self.ask_gpt(prompt)
        self.schema = build_schema(self.pet, state, proof)
        return self.schema

    def subproof_generator(self, state: State) -> str:
        current_goal = self.pet.goals(state)[0].pp
        prompt = next_prompt.format(goal=current_goal)
        return self.ask_gpt(prompt)

    def next(self, proof_generator: Callable[[State], str]) -> Schema:
        schema = fill_schema(self.pet, self.schema, proof_generator)
        self.schema = schema
        return self.schema

    def recursive_search(
        self, file_name: str, thm_name: str, max_depth: int = 5
    ) -> Schema:

        state = self.pet.start(file=file_name, thm=thm_name)
        self.start(state)
        # print(f"Initial schema\n{self.schema}\n")

        def search(depth: int) -> Schema:
            if depth == 0:
                raise PetanqueError(0, "No proof found")
            if not self.schema.admit_states:
                return self.schema
            p_proof = deepcopy(self.schema.tactics)
            self.next(self.subproof_generator)
            if p_proof == self.schema.tactics:
                raise PetanqueError(0, "Looping")
            return search(depth - 1)

        return search(max_depth)
