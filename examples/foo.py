from pytanque import Pytanque
import logging

logging.basicConfig()
logging.getLogger("pytanque.client").setLevel(logging.INFO)

with Pytanque("127.0.0.1", 8765) as pet:
    pet.init(root="./examples")
    pet.start(file="./examples/foo.v", thm="addnC")
    g = pet.run_tac("timeout 1 induction n.")
    print("Goals:", g)
    # pet.premises()
    pet.run_tac("simpl.")
    print(f"backtrack {pet.backtrack()}")
    print(f"backtrack {pet.backtrack()}")
    g = pet.run_tac("by elim: n => //= ? ->.")
    print("Goals:", g)
