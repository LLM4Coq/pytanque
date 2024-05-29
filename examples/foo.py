from pytanque import Pytanque

with Pytanque("127.0.0.1", 8765) as pet:
    pet.init(root="./examples")
    pet.start(file="./examples/foo.v", thm="addnC")
    pet.run_tac("timeout 1 induction n.")
    pet.goals()
    pet.premises()
    pet.run_tac("simpl.")
    print(f"backtrack {pet.backtrack()}")
    print(f"backtrack {pet.backtrack()}")
    pet.run_tac("by elim: n => //= ? ->.")
