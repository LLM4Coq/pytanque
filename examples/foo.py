from pytanque import Pytanque

with Pytanque("127.0.0.1", 8765) as pet:
    pet.start(file="./examples/foo.v", thm="addnC")
    pet.start(file="./examples/foo.v", thm="addnC")
    pet.run_tac("induction n.")
    pet.run_tac("simpl.")
    pet.run_tac("auto.")
    pet.rollback()
    pet.rollback()
    pet.run_tac("by elim: n => //= ? ->.")
