import socket
import json
import os
import pathlib
from collections import deque
from typing import Type, Callable
from .protocol import (
    Response,
    Failure,
    InitRequest,
    InitParams,
    StartParams,
    StartRequest,
    RunParams,
    RunRequest,
    RunResponse,
    GoalsParams,
    GoalsRequest,
    GoalsResponse,
    PremisesParams,
    PremisesRequest,
    PremisesResponse,
    CurrentState,
    ProofFinished,
)


class PetanqueError(Exception):
    pass


class Pytanque:
    def __enter__(self):
        self.socket.connect((self.host, self.port))
        return self

    def __init__(self, host: str, port: int, id: int):
        self.host = host
        self.port = port
        self.id = id
        self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.queue = deque()
        self.env = 0
        self.file = ""
        self.thm = ""

    def query(self, request, size: int = 1024):
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
            return Response.from_json_string(raw.decode())
        except ValueError:
            failure = Failure.from_json_string(raw.decode())
            raise PetanqueError(failure.error)

    def current_state(self):
        return self.queue[-1]

    def init(self, *, root: str):
        path = os.path.abspath(root)
        uri = pathlib.Path(path).as_uri()
        req = InitRequest(self.id, InitParams(uri))
        resp = self.query(req)
        self.env = resp.result
        print(f"Init success {self.env=}")

    def start(self, *, file: str, thm: str):
        self.file = file
        self.thm = thm
        self.queue.clear()
        path = os.path.abspath(file)
        uri = pathlib.Path(path).as_uri()
        req = StartRequest(self.id, StartParams(self.env, uri, self.thm))
        resp = self.query(req)
        self.queue.append(resp.result)
        print(f"Start success. Current state:{self.current_state()}")

    def run_tac(self, tac: str):
        req = RunRequest(self.id, RunParams(self.current_state(), tac))
        resp = self.query(req)
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
                raise PetanqueError("Humm!")

    def goals(self):
        req = GoalsRequest(self.id, GoalsParams(self.current_state()))
        resp = self.query(req)
        res = GoalsResponse.from_json(resp.result)
        print(f"Goals: {res.goals}")
        return res.goals

    def premises(self):
        req = PremisesRequest(self.id, PremisesParams(self.current_state()))
        resp = self.query(req)
        res = PremisesResponse.from_json(resp.result)
        print(f"Retrieved {len(res.value)} premises")
        return res.value

    def rollback(self):
        self.queue.pop()

    def __exit__(self, exc_type, exc_value, exc_tb):
        self.socket.close()
