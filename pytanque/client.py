import socket
import json
import os
import pathlib
import logging
from typing import (
    Union,
    Any,
    Optional,
    Type,
)
from typing_extensions import Self
from types import TracebackType
from .protocol import (
    Request,
    Response,
    Failure,
    StartParams,
    Opts,
    RunParams,
    GoalsParams,
    PremisesParams,
    State,
    GoalsResponse,
    PremisesResponse,
    Inspect,
    InspectPhysical,
    InspectGoals,
    StateEqualParams,
    StateEqualResponse,
    StateHashParams,
    StateHashResponse,
)

Params = Union[
    StartParams,
    RunParams,
    GoalsParams,
    PremisesParams,
    StateEqualParams,
    StateHashParams,
]

logger = logging.getLogger(__name__)


class PetanqueError(Exception):
    def __init__(self, code, message):
        self.code = code
        self.message = message


inspectPhysical = Inspect(InspectPhysical())
inspectGoals = Inspect(InspectGoals())


def mk_request(id: int, params: Params) -> Request:
    match params:
        case StartParams():
            return Request(id, "petanque/start", params.to_json())
        case RunParams():
            return Request(id, "petanque/run", params.to_json())
        case GoalsParams():
            return Request(id, "petanque/goals", params.to_json())
        case PremisesParams():
            return Request(id, "petanque/premises", params.to_json())
        case StateEqualParams():
            return Request(id, "petanque/state/eq", params.to_json())
        case StateHashParams():
            return Request(id, "petanque/state/hash", params.to_json())
        case _:
            raise PetanqueError(-32600, "Invalid request params")


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
        logger.info(f"Query Payload: {payload}")
        self.socket.sendall(payload)
        fragments = []
        while True:
            chunk = self.socket.recv(size)
            fragments.append(chunk)
            if len(chunk) < size:
                break
        raw = b"".join(fragments)
        try:
            logger.info(f"Query Response: {raw}")
            resp = Response.from_json_string(raw.decode())
            if resp.id != self.id:
                raise PetanqueError(
                    -32603, f"Sent request {self.id}, got response {resp.id}"
                )
            return resp
        except ValueError:
            failure = Failure.from_json_string(raw.decode())
            raise PetanqueError(failure.error.code, failure.error.message)

    def start(
        self,
        file: str,
        thm: str,
        pre_commands: Optional[str] = None,
        opts: Optional[Opts] = None,
    ) -> State:
        """
        Start the proof of [thm] defined in [file].
        """
        self.file = file
        self.thm = thm
        path = os.path.abspath(file)
        uri = pathlib.Path(path).as_uri()
        resp = self.query(StartParams(uri, self.thm, pre_commands, opts))
        res = State.from_json(resp.result)
        logger.info(f"Start success.")
        return res

    def run_tac(
        self,
        state: State,
        tac: str,
        opts: Optional[Opts] = None,
        verbose: Optional[bool] = False,
    ) -> State:
        """
        Execute on tactic.
        """
        resp = self.query(RunParams(state.st, tac, opts))
        res = State.from_json(resp.result)
        logger.info(f"Run tac {tac}.")
        if verbose:
            print(self.goals(res).pp())
        return res

    def goals(self, state: State) -> GoalsResponse:
        """
        Return the list of current goals.
        """
        resp = self.query(GoalsParams(state.st))
        res = GoalsResponse.from_json(resp.result)
        logger.info(f"Current goals: {res.goals}")
        return res

    def premises(self, state: State) -> Any:
        """
        Return the list of accessible premises.
        """
        resp = self.query(PremisesParams(state.st))
        res = PremisesResponse.from_json(resp.result)
        logger.info(f"Retrieved {len(res.value)} premises")
        return res.value

    def state_equal(self, st1: State, st2: State, kind: Inspect) -> Any:
        """
        Check if two states are equal.
        """
        resp = self.query(StateEqualParams(kind, st1.st, st2.st))
        res = StateEqualResponse.from_json(resp.result)
        logger.info(f"States equality {st1.st} = {st2.st} : {res.value}")
        return res.value

    def state_hash(self, state: State) -> Any:
        """
        Return the hash of a state.
        """
        resp = self.query(StateHashParams(state.st))
        res = StateHashResponse.from_json(resp.result)
        logger.info(f"States hash {state.st} = {res.value}")
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
