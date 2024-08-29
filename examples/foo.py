from pytanque import Pytanque
import logging

logging.basicConfig()
logging.getLogger("pytanque.client").setLevel(logging.INFO)

with Pytanque("127.0.0.1", 8765) as pet:
    pet.set_workspace(debug=False, dir="./examples/")
    print(pet.toc(file="./examples/foo.v"))
    s0 = pet.start(file="./examples/foo.v", thm="addnC")
    s = pet.run_tac(s0, "timeout 1 induction n.", verbose=True)
    g = pet.goals(s)
    # print(pet.premises(s))
    s = pet.run_tac(s, "simpl.", verbose=True)
    g = pet.goals(s)
    s = pet.run_tac(s0, "by elim: n => //= ? ->.", verbose=True)
    print("State:", s)
