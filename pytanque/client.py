import socket
import json
import os
import pathlib
from collections import deque
from typing import Union, List, Any
from .protocol import (
    Request,
    Response,
    Failure,
    InitParams,
    StartParams,
    RunParams,
    GoalsParams,
    PremisesParams,
    RunResponse,
    GoalsResponse,
    PremisesResponse,
    CurrentState,
    ProofFinished,
)

type Params = Union[
    InitParams,
    StartParams,
    RunParams,
    GoalsParams,
    PremisesParams,
]


class PetanqueError(Exception):
    pass


def mk_request(id, params: Params) -> Request:
    match params:
        case InitParams():
            return Request(id, "petanque/init", params.to_json())
        case StartParams():
            return Request(id, "petanque/start", params.to_json())
        case RunParams():
            return Request(id, "petanque/run", params.to_json())
        case GoalsParams():
            return Request(id, "petanque/goals", params.to_json())
        case PremisesParams():
            return Request(id, "petanque/premises", params.to_json())
        case _:
            raise PetanqueError("Invalid request params")


class Pytanque:
    def __enter__(self):
        self.socket.connect((self.host, self.port))
        return self

    def __init__(self, host: str, port: int):
        self.host = host
        self.port = port
        self.id = 0
        self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.queue = deque()
        self.env = 0
        self.file = ""
        self.thm = ""

    def query(self, params: Params, size: int = 1024) -> Response:
        self.id += 1
        request = mk_request(self.id, params)
        payload = (json.dumps(request.to_json()) + "\n").encode()
        self.socket.sendall(payload)
        fragments = []
        while True:
            chunk = self.socket.recv(size)
            fragments.append(chunk)
            if len(chunk) < size:
                break
        raw = b"".join(fragments)
        try:
            resp = Response.from_json_string(raw.decode())
            if resp.id != self.id:
                raise PetanqueError(f"Sent request {self.id}, got response {resp.id}")
            return resp
        except ValueError:
            failure = Failure.from_json_string(raw.decode())
            raise PetanqueError(failure.error)

    def current_state(self) -> int:
        return self.queue[-1]

    def init(self, *, root: str):
        path = os.path.abspath(root)
        uri = pathlib.Path(path).as_uri()
        resp = self.query(InitParams(uri))
        self.env = resp.result
        print(f"Init success {self.env=}")

    def start(self, *, file: str, thm: str):
        self.file = file
        self.thm = thm
        self.queue.clear()
        path = os.path.abspath(file)
        uri = pathlib.Path(path).as_uri()
        resp = self.query(StartParams(self.env, uri, self.thm))
        self.queue.append(resp.result)
        print(f"Start success. Current state:{self.current_state()}")

    def run_tac(self, tac: str):
        resp = self.query(RunParams(self.current_state(), tac))
        res = RunResponse.from_json(resp.result)
        print(f"Run tac {tac}.")
        match res.value:
            case CurrentState(st):
                self.queue.append(res.value.value)
                print(f"Current state:{self.current_state()}")
            case ProofFinished(st):
                self.queue.append(res.value.value)
                print(f"Proof finished:{self.current_state()}")
            case _:
                raise PetanqueError("Invalid proof state")

    def goals(self) -> List[Any]:
        resp = self.query(GoalsParams(self.current_state()))
        res = GoalsResponse.from_json(resp.result)
        print(f"Goals: {res.goals}")
        return res.goals

    def premises(self) -> List[Any]:
        resp = self.query(PremisesParams(self.current_state()))
        res = PremisesResponse.from_json(resp.result)
        print(f"Retrieved {len(res.value)} premises")
        return res.value

    def rollback(self):
        self.queue.pop()

    def __exit__(self, exc_type, exc_value, exc_tb):
        self.socket.close()
