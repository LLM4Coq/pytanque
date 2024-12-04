# Pytanque

Pytanque is a Python API for lightweight communication with the Rocq proof assistant.

## Install

### Pétanque

Pytanque requires a recent `coq-lsp` version, as of Dec 1st 2024, we
recommend you install `coq-lsp` `main` in developer mode. To do so, do:

```
git clone https://github.com/ejgallego/coq-lsp /path/to/coq-lsp
cd /path/to/coq-lsp
make submodules-init
make
```

See [petanque's README](https://github.com/ejgallego/coq-lsp/petanque)
for more and updated install methods, including a global Coq +
petanque opam install.

### Pytanque

You should setup a virtual env first, e.g., using pyenv virtualenv:

```
pyenv virtualenv 3.12.2 pytanque
pip install -e .
```

## Usage

First start `pet-server`

- If installed from `coq-lsp` development tree (as per the above instructions):
```
cd /path/to/coq-lsp/petanque
dune exec -- pet-server
```

- If installed via opam, just run `pet-server`

Then, the class `Pytanque` is the main entry point to communicate with
the Petanque server.  Assuming you have a coq file named `tests/foo.v`
which contains a theorem `addnC` you can try the following.

```
from pytanque import Pytanque

with Pytanque("127.0.0.1", 8765) as pet:
    state = pet.start(file="./examples/foo.v", thm="addnC")
    state = pet.run_tac(state, "induction n.", verbose=True)
    state = pet.run_tac(state, "auto.", verbose=True)
    state = pet.run_tac(state, "lia.", verbose=True)
```

You can quickly try a similar example with

```
python examples/foo.py
```
