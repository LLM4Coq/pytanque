import logging
from typing import Optional, Tuple, List, Callable, ParamSpec
from .protocol import State, RunOps
from .client import Pytanque, PetanqueError
import heapq

logger = logging.getLogger(__name__)


Tactic = str
Proof = List[Tactic]
Score = float


class Search:
    def __init__(
        self,
        pet: Pytanque,
        tactic_generator: Callable[[State, int], Tuple[List[str], List[float]]],
    ):
        self.pet = pet
        self.generate = tactic_generator

    def search(self, state: State) -> Optional[Proof]:
        return None


class DFS(Search):
    """
    Depth First Search.
    Adapted from the NeurIPS 2024 tutorial: https://github.com/yangky11/ml4tp-tutorial/blob/main/main.ipynb
    """

    def __init__(self, max_depth: int, num_samples: int, **kwargs):
        super().__init__(**kwargs)
        self.max_depth = max_depth
        self.num_samples = num_samples
        self.run_ops = RunOps(memo=False, hash=False)

    def search(self, state: State) -> Optional[Proof]:

        def run(state: State, depth: int) -> Optional[Proof]:
            if depth >= self.max_depth:
                return None
            tactics, _ = self.generate(state, self.num_samples)
            # Run the tactics.
            for tac in tactics:
                logger.info(f"Trying {tac}")
                try:
                    next_state = self.pet.run_tac(state, tac, self.run_ops)
                    if next_state.proof_finished:
                        return [tac]
                    subproof = run(next_state, depth + 1)
                    if subproof:
                        return [tac] + subproof
                except PetanqueError as err:
                    logger.warning(f"Invalid Tactic: {tac} {err}")
            return None

        return run(state, depth=0)


class BFS(Search):
    """
    Best first search.
    Adapted from the 2023 Neural theorem proving tutorial: https://github.com/wellecks/ntptutorial
    """

    def __init__(self, max_iters: int, num_samples: int, **kwargs):
        super().__init__(**kwargs)
        self.max_iters = max_iters
        self.num_samples = num_samples

    def search(self, state: State) -> Optional[Proof]:
        queue = [(0.0, [], state)]
        visited = set()
        for _ in range(self.max_iters):
            if len(queue) == 0:
                break

            total_score, proof, state = heapq.heappop(queue)
            visited.add(state.hash)

            tactics, scores = self.generate(state, self.num_samples)

            for tactic, score in zip(tactics, scores):
                logger.info(f"Trying {tactic}")
                try:
                    next_state = self.pet.run_tac(state, tactic)

                    if next_state.proof_finished:
                        return proof + [tactic]

                    if next_state.hash not in visited:
                        # Score is negative log probability summed across steps
                        new_score = total_score - score
                        heapq.heappush(queue, (new_score, proof + [tactic], next_state))

                except PetanqueError as err:
                    logger.warning(f"Invalid Tactic: {tactic} {err}")
        return None
