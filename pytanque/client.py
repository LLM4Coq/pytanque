import socket
import json
import os
import pathlib
import logging
from collections import deque
from typing import (
    Union,
    Tuple,
    Any,
    Deque,
    Optional,
    Type,
)
from typing_extensions import Self
from types import TracebackType
from dataclasses import dataclass
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

Params = Union[
    InitParams,
    StartParams,
    RunParams,
    GoalsParams,
    PremisesParams,
]

Env = int
State = Union[CurrentState, ProofFinished]

logger = logging.getLogger(__name__)


class PetanqueError(Exception):
    pass


def mk_request(id: int, params: Params) -> Request:
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
    """
    Petanque client to communicate with the Rocq theorem prover using JSON-RPC over a simple socket.
    """

    def __init__(self, host: str, port: int):
        """
        Open socket given the [host] and [port].
        """
        self.host = host
        self.port = port
        self.id = 0
        self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.env = 0
        self.file = ""
        self.thm = ""

    def connect(self) -> None:
        """
        Connect the socket to the server
        """
        self.socket.connect((self.host, self.port))
        logger.info(f"Connected to the socket")

    def close(self) -> None:
        """
        Close the socket
        """
        self.socket.close()
        logger.info(f"Socket closed")

    def __enter__(self) -> Self:
        self.connect()
        return self

    def query(self, params: Params, size: int = 1024) -> Response:
        """
        Send a query to the server using JSON-RPC protocol.
        """
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

    def init(self, *, root: str) -> Env:
        """
        Initialize Rocq enviorment (must only be called once).
        """
        path = os.path.abspath(root)
        uri = pathlib.Path(path).as_uri()
        resp = self.query(InitParams(uri))
        self.env = resp.result
        logger.info(f"Init success {self.env=}")
        return int(resp.result)

    def start(self, *, file: str, thm: str) -> State:
        """
        Start the proof of [thm] defined in [file].
        """
        self.file = file
        self.thm = thm
        path = os.path.abspath(file)
        uri = pathlib.Path(path).as_uri()
        resp = self.query(StartParams(self.env, uri, self.thm))
        logger.info(f"Start success.")
        return CurrentState(resp.result)

    def run_tac(self, state: State, tac: str) -> State:
        """
        Execute on tactic.
        """
        resp = self.query(RunParams(state.value, tac))
        res = RunResponse.from_json(resp.result)
        logger.info(f"Run tac {tac}.")
        return res.value

    def goals(self, state: State) -> GoalsResponse:
        """
        Return the list of current goals.
        """
        resp = self.query(GoalsParams(state.value))
        res = GoalsResponse.from_json(resp.result)
        logger.info(f"Current goals: {res.goals}")
        return res

    def premises(self, state: State) -> Any:
        """
        Return the list of accessible premises.
        """
        resp = self.query(PremisesParams(state.value))
        res = PremisesResponse.from_json(resp.result)
        logger.info(f"Retrieved {len(res.value)} premises")
        return res.value

    def __exit__(
        self,
        exc_type: Optional[Type[BaseException]],
        exc_val: Optional[BaseException],
        exc_tb: Optional[TracebackType],
    ) -> None:
        """
        Close the socket and exit.
        """
        self.close()
