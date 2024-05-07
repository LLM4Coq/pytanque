# Pytanque

Lightweight communication with the Petanque TCP server.

## Install

You should setup a virtual env first, e.g., using pyenv virtualenv:

```
pyenv virtualenv 3.12.2 pytanque
pip install -e .
```

## Usage


First start the `pet-server` (https://github.com/gbdrt/coq-lsp/tree/pytanque)
```
cd /path/to/coq-lsp/petanque
dune exec -- pet-server
```

Then, the class Pytanque is the main entry point to communicate with the Petanque server.
Assuming you have a coq file named `tests/foo.v` which contains a theorem `addnC` you can try the following.

```
from pytanque import Pytanque

with Pytanque("127.0.0.1", 8765) as pet:
    pet.start(file="./tests/foo.v", thm="addnC")
    pet.start(file="./tests/foo.v", thm="addnC")
    pet.run_tac("induction n.")
    pet.run_tac("simpl.")
    pet.run_tac("auto.")
    pet.rollback()
    pet.rollback()
    pet.run_tac("by elim: n => //= ? ->.")
```

You can quickly try to run this example with

```
python examples/foo.py
```