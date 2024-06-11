from pytanque import Pytanque
import logging

logging.basicConfig()
logging.getLogger("pytanque.client").setLevel(logging.INFO)

with Pytanque("127.0.0.1", 8765) as pet:
    pet.init(root="./examples")
    s0 = pet.start(file="./examples/foo.v", thm="addnC")
    s = pet.run_tac(s0, "timeout 1 induction n.")
    g = pet.goals(s)
    print("Goals:", g.pp()) # type: ignore
    # pet.premises()
    s = pet.run_tac(s, "simpl.")
    g = pet.goals(s)
    print("Goals:", g.pp()) # type: ignore
    s = pet.run_tac(s0, "by elim: n => //= ? ->.")
    print("State:", s)
