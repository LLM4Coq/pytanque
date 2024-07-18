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


def split_proof(
    proof: str,
    add_delimiter: bool = True,
) -> List[str]:
    raw = remove_comments(proof)  # remove comments
    tactics = [
        t
        for b in re.split(r"(\++|\*+|\-+|{|})", raw)  # split proof in bullets
        for s in re.split(r"(?<=\.)\s", b)  # split bullets in tactics
        if (t := s.strip())  # remove empty steps
    ]
    if add_delimiter:
        return ["{", *tactics, "}"]
    return tactics


def check_final_state(pet: Pytanque, state: State) -> bool:
    goals = pet.goals(state)
    return not goals and all(e == ([], []) for e in goals)


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


def build_schema(
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

    tactics = split_proof(proof, add_delimiter=True)
    schema = fix(state, 0, tactics, False)
    match schema.tactics:  # remove nested admit.
        case ["{", "admit.", "}"]:
            schema.tactics = ["admit."]
            schema.admit_idx = [0]
    return schema


def fill_schema(
    pet: Pytanque, schema: Schema, proof_generator: Callable[[State], str]
) -> Schema:
    assert len(schema.admit_idx) == len(schema.admit_states)

    new_schema = Schema()

    offset = 0
    p_ai = -1

    for state, ai, err in zip(
        schema.admit_states, schema.admit_idx, schema.admit_errors
    ):

        sub_proof = proof_generator(state)
        print(f"Trying:\n {sub_proof}\n")
        sub_schema = build_schema(pet, state, sub_proof)
        print(f"Got:\n {sub_schema}\n")

        new_schema.tactics += schema.tactics[p_ai + 1 : ai] + sub_schema.tactics
        new_schema.admit_states += sub_schema.admit_states
        new_schema.admit_errors += sub_schema.admit_errors
        new_schema.admit_idx += [ai + offset + k for k in sub_schema.admit_idx]

        offset += len(sub_schema.tactics) - 1
        p_ai = ai

    new_schema.tactics += schema.tactics[p_ai + 1 :]

    schema = new_schema
    return schema
