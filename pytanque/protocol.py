"""Generated by atdpy from type definitions in protocol.atd.

This implements classes for the types defined in 'protocol.atd', providing
methods and functions to convert data from/to JSON.
"""

# Disable flake8 entirely on this file:
# flake8: noqa

# Import annotations to allow forward references
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, NoReturn, Optional, Tuple, Union

import json

############################################################################
# Private functions
############################################################################


def _atd_missing_json_field(type_name: str, json_field_name: str) -> NoReturn:
    raise ValueError(
        f"missing field '{json_field_name}'" f" in JSON object of type '{type_name}'"
    )


def _atd_bad_json(expected_type: str, json_value: Any) -> NoReturn:
    value_str = str(json_value)
    if len(value_str) > 200:
        value_str = value_str[:200] + "…"

    raise ValueError(
        f"incompatible JSON value where"
        f" type '{expected_type}' was expected: '{value_str}'"
    )


def _atd_bad_python(expected_type: str, json_value: Any) -> NoReturn:
    value_str = str(json_value)
    if len(value_str) > 200:
        value_str = value_str[:200] + "…"

    raise ValueError(
        f"incompatible Python value where"
        f" type '{expected_type}' was expected: '{value_str}'"
    )


def _atd_read_unit(x: Any) -> None:
    if x is None:
        return x
    else:
        _atd_bad_json("unit", x)


def _atd_read_bool(x: Any) -> bool:
    if isinstance(x, bool):
        return x
    else:
        _atd_bad_json("bool", x)


def _atd_read_int(x: Any) -> int:
    if isinstance(x, int):
        return x
    else:
        _atd_bad_json("int", x)


def _atd_read_float(x: Any) -> float:
    if isinstance(x, (int, float)):
        return x
    else:
        _atd_bad_json("float", x)


def _atd_read_string(x: Any) -> str:
    if isinstance(x, str):
        return x
    else:
        _atd_bad_json("str", x)


def _atd_read_list(read_elt: Callable[[Any], Any]) -> Callable[[List[Any]], List[Any]]:
    def read_list(elts: List[Any]) -> List[Any]:
        if isinstance(elts, list):
            return [read_elt(elt) for elt in elts]
        else:
            _atd_bad_json("array", elts)

    return read_list


def _atd_read_assoc_array_into_dict(
    read_key: Callable[[Any], Any],
    read_value: Callable[[Any], Any],
) -> Callable[[List[Any]], Dict[Any, Any]]:
    def read_assoc(elts: List[List[Any]]) -> Dict[str, Any]:
        if isinstance(elts, list):
            return {read_key(elt[0]): read_value(elt[1]) for elt in elts}
        else:
            _atd_bad_json("array", elts)
            raise AssertionError("impossible")  # keep mypy happy

    return read_assoc


def _atd_read_assoc_object_into_dict(
    read_value: Callable[[Any], Any]
) -> Callable[[Dict[str, Any]], Dict[str, Any]]:
    def read_assoc(elts: Dict[str, Any]) -> Dict[str, Any]:
        if isinstance(elts, dict):
            return {_atd_read_string(k): read_value(v) for k, v in elts.items()}
        else:
            _atd_bad_json("object", elts)
            raise AssertionError("impossible")  # keep mypy happy

    return read_assoc


def _atd_read_assoc_object_into_list(
    read_value: Callable[[Any], Any]
) -> Callable[[Dict[str, Any]], List[Tuple[str, Any]]]:
    def read_assoc(elts: Dict[str, Any]) -> List[Tuple[str, Any]]:
        if isinstance(elts, dict):
            return [(_atd_read_string(k), read_value(v)) for k, v in elts.items()]
        else:
            _atd_bad_json("object", elts)
            raise AssertionError("impossible")  # keep mypy happy

    return read_assoc


def _atd_read_nullable(
    read_elt: Callable[[Any], Any]
) -> Callable[[Optional[Any]], Optional[Any]]:
    def read_nullable(x: Any) -> Any:
        if x is None:
            return None
        else:
            return read_elt(x)

    return read_nullable


def _atd_read_option(
    read_elt: Callable[[Any], Any]
) -> Callable[[Optional[Any]], Optional[Any]]:
    def read_option(x: Any) -> Any:
        if x == "None":
            return None
        elif isinstance(x, List) and len(x) == 2 and x[0] == "Some":
            return read_elt(x[1])
        else:
            _atd_bad_json("option", x)
            raise AssertionError("impossible")  # keep mypy happy

    return read_option


def _atd_write_unit(x: Any) -> None:
    if x is None:
        return x
    else:
        _atd_bad_python("unit", x)


def _atd_write_bool(x: Any) -> bool:
    if isinstance(x, bool):
        return x
    else:
        _atd_bad_python("bool", x)


def _atd_write_int(x: Any) -> int:
    if isinstance(x, int):
        return x
    else:
        _atd_bad_python("int", x)


def _atd_write_float(x: Any) -> float:
    if isinstance(x, (int, float)):
        return x
    else:
        _atd_bad_python("float", x)


def _atd_write_string(x: Any) -> str:
    if isinstance(x, str):
        return x
    else:
        _atd_bad_python("str", x)


def _atd_write_list(
    write_elt: Callable[[Any], Any]
) -> Callable[[List[Any]], List[Any]]:
    def write_list(elts: List[Any]) -> List[Any]:
        if isinstance(elts, list):
            return [write_elt(elt) for elt in elts]
        else:
            _atd_bad_python("list", elts)

    return write_list


def _atd_write_assoc_dict_to_array(
    write_key: Callable[[Any], Any], write_value: Callable[[Any], Any]
) -> Callable[[Dict[Any, Any]], List[Tuple[Any, Any]]]:
    def write_assoc(elts: Dict[str, Any]) -> List[Tuple[str, Any]]:
        if isinstance(elts, dict):
            return [(write_key(k), write_value(v)) for k, v in elts.items()]
        else:
            _atd_bad_python("Dict[str, <value type>]]", elts)
            raise AssertionError("impossible")  # keep mypy happy

    return write_assoc


def _atd_write_assoc_dict_to_object(
    write_value: Callable[[Any], Any]
) -> Callable[[Dict[str, Any]], Dict[str, Any]]:
    def write_assoc(elts: Dict[str, Any]) -> Dict[str, Any]:
        if isinstance(elts, dict):
            return {_atd_write_string(k): write_value(v) for k, v in elts.items()}
        else:
            _atd_bad_python("Dict[str, <value type>]", elts)
            raise AssertionError("impossible")  # keep mypy happy

    return write_assoc


def _atd_write_assoc_list_to_object(
    write_value: Callable[[Any], Any],
) -> Callable[[List[Any]], Dict[str, Any]]:
    def write_assoc(elts: List[List[Any]]) -> Dict[str, Any]:
        if isinstance(elts, list):
            return {_atd_write_string(elt[0]): write_value(elt[1]) for elt in elts}
        else:
            _atd_bad_python("List[Tuple[<key type>, <value type>]]", elts)
            raise AssertionError("impossible")  # keep mypy happy

    return write_assoc


def _atd_write_nullable(
    write_elt: Callable[[Any], Any]
) -> Callable[[Optional[Any]], Optional[Any]]:
    def write_nullable(x: Any) -> Any:
        if x is None:
            return None
        else:
            return write_elt(x)

    return write_nullable


def _atd_write_option(
    write_elt: Callable[[Any], Any]
) -> Callable[[Optional[Any]], Optional[Any]]:
    def write_option(x: Any) -> Any:
        if x is None:
            return "None"
        else:
            return ["Some", write_elt(x)]

    return write_option


############################################################################
# Public classes
############################################################################


@dataclass
class TocResponse:
    """Original type: toc_response"""

    value: List[Tuple[str, Any]]

    @classmethod
    def from_json(cls, x: Any) -> "TocResponse":
        return cls(
            _atd_read_list(
                (
                    lambda x: (
                        (_atd_read_string(x[0]), (lambda x: x)(x[1]))
                        if isinstance(x, list) and len(x) == 2
                        else _atd_bad_json("array of length 2", x)
                    )
                )
            )(x)
        )

    def to_json(self) -> Any:
        return _atd_write_list(
            (
                lambda x: (
                    [_atd_write_string(x[0]), (lambda x: x)(x[1])]
                    if isinstance(x, tuple) and len(x) == 2
                    else _atd_bad_python("tuple of length 2", x)
                )
            )
        )(self.value)

    @classmethod
    def from_json_string(cls, x: str) -> "TocResponse":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class TocParams:
    """Original type: toc_params = { ... }"""

    uri: str

    @classmethod
    def from_json(cls, x: Any) -> "TocParams":
        if isinstance(x, dict):
            return cls(
                uri=(
                    _atd_read_string(x["uri"])
                    if "uri" in x
                    else _atd_missing_json_field("TocParams", "uri")
                ),
            )
        else:
            _atd_bad_json("TocParams", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["uri"] = _atd_write_string(self.uri)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "TocParams":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class StateHashResponse:
    """Original type: state_hash_response"""

    value: int

    @classmethod
    def from_json(cls, x: Any) -> "StateHashResponse":
        return cls(_atd_read_int(x))

    def to_json(self) -> Any:
        return _atd_write_int(self.value)

    @classmethod
    def from_json_string(cls, x: str) -> "StateHashResponse":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class StateHashParams:
    """Original type: state_hash_params = { ... }"""

    st: int

    @classmethod
    def from_json(cls, x: Any) -> "StateHashParams":
        if isinstance(x, dict):
            return cls(
                st=(
                    _atd_read_int(x["st"])
                    if "st" in x
                    else _atd_missing_json_field("StateHashParams", "st")
                ),
            )
        else:
            _atd_bad_json("StateHashParams", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["st"] = _atd_write_int(self.st)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "StateHashParams":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class StateEqualResponse:
    """Original type: state_equal_response"""

    value: bool

    @classmethod
    def from_json(cls, x: Any) -> "StateEqualResponse":
        return cls(_atd_read_bool(x))

    def to_json(self) -> Any:
        return _atd_write_bool(self.value)

    @classmethod
    def from_json_string(cls, x: str) -> "StateEqualResponse":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class InspectPhysical:
    """Original type: inspect = [ ... | InspectPhysical | ... ]"""

    @property
    def kind(self) -> str:
        """Name of the class representing this variant."""
        return "InspectPhysical"

    @staticmethod
    def to_json() -> Any:
        return "Physical"

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class InspectGoals:
    """Original type: inspect = [ ... | InspectGoals | ... ]"""

    @property
    def kind(self) -> str:
        """Name of the class representing this variant."""
        return "InspectGoals"

    @staticmethod
    def to_json() -> Any:
        return "Goals"

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class Inspect:
    """Original type: inspect = [ ... ]"""

    value: Union[InspectPhysical, InspectGoals]

    @property
    def kind(self) -> str:
        """Name of the class representing this variant."""
        return self.value.kind

    @classmethod
    def from_json(cls, x: Any) -> "Inspect":
        if isinstance(x, str):
            if x == "Physical":
                return cls(InspectPhysical())
            if x == "Goals":
                return cls(InspectGoals())
            _atd_bad_json("Inspect", x)
        _atd_bad_json("Inspect", x)

    def to_json(self) -> Any:
        return self.value.to_json()

    @classmethod
    def from_json_string(cls, x: str) -> "Inspect":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class StateEqualParams:
    """Original type: state_equal_params = { ... }"""

    kind: Inspect
    st1: int
    st2: int

    @classmethod
    def from_json(cls, x: Any) -> "StateEqualParams":
        if isinstance(x, dict):
            return cls(
                kind=(
                    Inspect.from_json(x["kind"])
                    if "kind" in x
                    else _atd_missing_json_field("StateEqualParams", "kind")
                ),
                st1=(
                    _atd_read_int(x["st1"])
                    if "st1" in x
                    else _atd_missing_json_field("StateEqualParams", "st1")
                ),
                st2=(
                    _atd_read_int(x["st2"])
                    if "st2" in x
                    else _atd_missing_json_field("StateEqualParams", "st2")
                ),
            )
        else:
            _atd_bad_json("StateEqualParams", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["kind"] = (lambda x: x.to_json())(self.kind)
        res["st1"] = _atd_write_int(self.st1)
        res["st2"] = _atd_write_int(self.st2)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "StateEqualParams":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class State:
    """Original type: state = { ... }"""

    st: int
    proof_finished: bool
    hash: Optional[int] = None

    @classmethod
    def from_json(cls, x: Any) -> "State":
        if isinstance(x, dict):
            return cls(
                st=(
                    _atd_read_int(x["st"])
                    if "st" in x
                    else _atd_missing_json_field("State", "st")
                ),
                proof_finished=(
                    _atd_read_bool(x["proof_finished"])
                    if "proof_finished" in x
                    else _atd_missing_json_field("State", "proof_finished")
                ),
                hash=_atd_read_int(x["hash"]) if "hash" in x else None,
            )
        else:
            _atd_bad_json("State", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["st"] = _atd_write_int(self.st)
        res["proof_finished"] = _atd_write_bool(self.proof_finished)
        if self.hash is not None:
            res["hash"] = _atd_write_int(self.hash)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "State":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class Opts:
    """Original type: opts = { ... }"""

    memo: bool = field(default_factory=lambda: True)
    hash: bool = field(default_factory=lambda: True)

    @classmethod
    def from_json(cls, x: Any) -> "Opts":
        if isinstance(x, dict):
            return cls(
                memo=_atd_read_bool(x["memo"]) if "memo" in x else True,
                hash=_atd_read_bool(x["hash"]) if "hash" in x else True,
            )
        else:
            _atd_bad_json("Opts", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["memo"] = _atd_write_bool(self.memo)
        res["hash"] = _atd_write_bool(self.hash)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "Opts":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class StartParams:
    """Original type: start_params = { ... }"""

    uri: str
    thm: str
    pre_commands: Optional[str] = None
    opts: Optional[Opts] = None

    @classmethod
    def from_json(cls, x: Any) -> "StartParams":
        if isinstance(x, dict):
            return cls(
                uri=(
                    _atd_read_string(x["uri"])
                    if "uri" in x
                    else _atd_missing_json_field("StartParams", "uri")
                ),
                thm=(
                    _atd_read_string(x["thm"])
                    if "thm" in x
                    else _atd_missing_json_field("StartParams", "thm")
                ),
                pre_commands=(
                    _atd_read_string(x["pre_commands"]) if "pre_commands" in x else None
                ),
                opts=Opts.from_json(x["opts"]) if "opts" in x else None,
            )
        else:
            _atd_bad_json("StartParams", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["uri"] = _atd_write_string(self.uri)
        res["thm"] = _atd_write_string(self.thm)
        if self.pre_commands is not None:
            res["pre_commands"] = _atd_write_string(self.pre_commands)
        if self.opts is not None:
            res["opts"] = (lambda x: x.to_json())(self.opts)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "StartParams":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class SetWorkspaceParams:
    """Original type: set_workspace_params = { ... }"""

    debug: bool
    root: str

    @classmethod
    def from_json(cls, x: Any) -> "SetWorkspaceParams":
        if isinstance(x, dict):
            return cls(
                debug=(
                    _atd_read_bool(x["debug"])
                    if "debug" in x
                    else _atd_missing_json_field("SetWorkspaceParams", "debug")
                ),
                root=(
                    _atd_read_string(x["root"])
                    if "root" in x
                    else _atd_missing_json_field("SetWorkspaceParams", "root")
                ),
            )
        else:
            _atd_bad_json("SetWorkspaceParams", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["debug"] = _atd_write_bool(self.debug)
        res["root"] = _atd_write_string(self.root)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "SetWorkspaceParams":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class RunParams:
    """Original type: run_params = { ... }"""

    st: int
    tac: str
    opts: Optional[Opts] = None

    @classmethod
    def from_json(cls, x: Any) -> "RunParams":
        if isinstance(x, dict):
            return cls(
                st=(
                    _atd_read_int(x["st"])
                    if "st" in x
                    else _atd_missing_json_field("RunParams", "st")
                ),
                tac=(
                    _atd_read_string(x["tac"])
                    if "tac" in x
                    else _atd_missing_json_field("RunParams", "tac")
                ),
                opts=Opts.from_json(x["opts"]) if "opts" in x else None,
            )
        else:
            _atd_bad_json("RunParams", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["st"] = _atd_write_int(self.st)
        res["tac"] = _atd_write_string(self.tac)
        if self.opts is not None:
            res["opts"] = (lambda x: x.to_json())(self.opts)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "RunParams":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class Response:
    """Original type: response = { ... }"""

    id: int
    result: Any
    jsonrpc: str = field(default_factory=lambda: "2.0")

    @classmethod
    def from_json(cls, x: Any) -> "Response":
        if isinstance(x, dict):
            return cls(
                id=(
                    _atd_read_int(x["id"])
                    if "id" in x
                    else _atd_missing_json_field("Response", "id")
                ),
                result=(
                    (lambda x: x)(x["result"])
                    if "result" in x
                    else _atd_missing_json_field("Response", "result")
                ),
                jsonrpc=_atd_read_string(x["jsonrpc"]) if "jsonrpc" in x else "2.0",
            )
        else:
            _atd_bad_json("Response", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["id"] = _atd_write_int(self.id)
        res["result"] = (lambda x: x)(self.result)
        res["jsonrpc"] = _atd_write_string(self.jsonrpc)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "Response":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class Request:
    """Original type: request = { ... }"""

    id: int
    method_: str
    params: Any
    jsonrpc: str = field(default_factory=lambda: "2.0")

    @classmethod
    def from_json(cls, x: Any) -> "Request":
        if isinstance(x, dict):
            return cls(
                id=(
                    _atd_read_int(x["id"])
                    if "id" in x
                    else _atd_missing_json_field("Request", "id")
                ),
                method_=(
                    _atd_read_string(x["method"])
                    if "method" in x
                    else _atd_missing_json_field("Request", "method")
                ),
                params=(
                    (lambda x: x)(x["params"])
                    if "params" in x
                    else _atd_missing_json_field("Request", "params")
                ),
                jsonrpc=_atd_read_string(x["jsonrpc"]) if "jsonrpc" in x else "2.0",
            )
        else:
            _atd_bad_json("Request", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["id"] = _atd_write_int(self.id)
        res["method"] = _atd_write_string(self.method_)
        res["params"] = (lambda x: x)(self.params)
        res["jsonrpc"] = _atd_write_string(self.jsonrpc)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "Request":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class PremisesResponse:
    """Original type: premises_response"""

    value: Any

    @classmethod
    def from_json(cls, x: Any) -> "PremisesResponse":
        return cls((lambda x: x)(x))

    def to_json(self) -> Any:
        return (lambda x: x)(self.value)

    @classmethod
    def from_json_string(cls, x: str) -> "PremisesResponse":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class PremisesParams:
    """Original type: premises_params = { ... }"""

    st: int

    @classmethod
    def from_json(cls, x: Any) -> "PremisesParams":
        if isinstance(x, dict):
            return cls(
                st=(
                    _atd_read_int(x["st"])
                    if "st" in x
                    else _atd_missing_json_field("PremisesParams", "st")
                ),
            )
        else:
            _atd_bad_json("PremisesParams", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["st"] = _atd_write_int(self.st)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "PremisesParams":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class GoalHyp:
    """Original type: goal_hyp = { ... }"""

    names: List[str]
    ty: str
    def_: Optional[Any] = None

    @classmethod
    def from_json(cls, x: Any) -> "GoalHyp":
        if isinstance(x, dict):
            return cls(
                names=(
                    _atd_read_list(_atd_read_string)(x["names"])
                    if "names" in x
                    else _atd_missing_json_field("GoalHyp", "names")
                ),
                ty=(
                    _atd_read_string(x["ty"])
                    if "ty" in x
                    else _atd_missing_json_field("GoalHyp", "ty")
                ),
                def_=(lambda x: x)(x["def"]) if "def" in x else None,
            )
        else:
            _atd_bad_json("GoalHyp", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["names"] = _atd_write_list(_atd_write_string)(self.names)
        res["ty"] = _atd_write_string(self.ty)
        if self.def_ is not None:
            res["def"] = (lambda x: x)(self.def_)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "GoalHyp":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class Goal:
    """Original type: goal = { ... }"""

    info: Any
    hyps: List[GoalHyp]
    ty: str
    pp: Optional[str] = None

    @classmethod
    def from_json(cls, x: Any) -> "Goal":
        if isinstance(x, dict):
            return cls(
                info=(
                    (lambda x: x)(x["info"])
                    if "info" in x
                    else _atd_missing_json_field("Goal", "info")
                ),
                hyps=(
                    _atd_read_list(GoalHyp.from_json)(x["hyps"])
                    if "hyps" in x
                    else _atd_missing_json_field("Goal", "hyps")
                ),
                ty=(
                    _atd_read_string(x["ty"])
                    if "ty" in x
                    else _atd_missing_json_field("Goal", "ty")
                ),
                pp=_atd_read_string(x["pp"]) if "pp" in x else None,
            )
        else:
            _atd_bad_json("Goal", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["info"] = (lambda x: x)(self.info)
        res["hyps"] = _atd_write_list((lambda x: x.to_json()))(self.hyps)
        res["ty"] = _atd_write_string(self.ty)
        if self.pp is not None:
            res["pp"] = _atd_write_string(self.pp)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "Goal":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class GoalsResponse:
    """Original type: goals_response = { ... }"""

    goals: List[Goal]
    stack: List[Tuple[List[Any], List[Any]]]
    shelf: List[Any]
    given_up: List[Any]

    @classmethod
    def from_json(cls, x: Any) -> "GoalsResponse":
        if isinstance(x, dict):
            return cls(
                goals=(
                    _atd_read_list(Goal.from_json)(x["goals"])
                    if "goals" in x
                    else _atd_missing_json_field("GoalsResponse", "goals")
                ),
                stack=(
                    _atd_read_list(
                        (
                            lambda x: (
                                (
                                    _atd_read_list((lambda x: x))(x[0]),
                                    _atd_read_list((lambda x: x))(x[1]),
                                )
                                if isinstance(x, list) and len(x) == 2
                                else _atd_bad_json("array of length 2", x)
                            )
                        )
                    )(x["stack"])
                    if "stack" in x
                    else _atd_missing_json_field("GoalsResponse", "stack")
                ),
                shelf=(
                    _atd_read_list((lambda x: x))(x["shelf"])
                    if "shelf" in x
                    else _atd_missing_json_field("GoalsResponse", "shelf")
                ),
                given_up=(
                    _atd_read_list((lambda x: x))(x["given_up"])
                    if "given_up" in x
                    else _atd_missing_json_field("GoalsResponse", "given_up")
                ),
            )
        else:
            _atd_bad_json("GoalsResponse", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["goals"] = _atd_write_list((lambda x: x.to_json()))(self.goals)
        res["stack"] = _atd_write_list(
            (
                lambda x: (
                    [
                        _atd_write_list((lambda x: x))(x[0]),
                        _atd_write_list((lambda x: x))(x[1]),
                    ]
                    if isinstance(x, tuple) and len(x) == 2
                    else _atd_bad_python("tuple of length 2", x)
                )
            )
        )(self.stack)
        res["shelf"] = _atd_write_list((lambda x: x))(self.shelf)
        res["given_up"] = _atd_write_list((lambda x: x))(self.given_up)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "GoalsResponse":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class GoalsParams:
    """Original type: goals_params = { ... }"""

    st: int

    @classmethod
    def from_json(cls, x: Any) -> "GoalsParams":
        if isinstance(x, dict):
            return cls(
                st=(
                    _atd_read_int(x["st"])
                    if "st" in x
                    else _atd_missing_json_field("GoalsParams", "st")
                ),
            )
        else:
            _atd_bad_json("GoalsParams", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["st"] = _atd_write_int(self.st)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "GoalsParams":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class Error:
    """Original type: error = { ... }"""

    code: int
    message: str

    @classmethod
    def from_json(cls, x: Any) -> "Error":
        if isinstance(x, dict):
            return cls(
                code=(
                    _atd_read_int(x["code"])
                    if "code" in x
                    else _atd_missing_json_field("Error", "code")
                ),
                message=(
                    _atd_read_string(x["message"])
                    if "message" in x
                    else _atd_missing_json_field("Error", "message")
                ),
            )
        else:
            _atd_bad_json("Error", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["code"] = _atd_write_int(self.code)
        res["message"] = _atd_write_string(self.message)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "Error":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class Failure:
    """Original type: failure = { ... }"""

    id: int
    error: Error

    @classmethod
    def from_json(cls, x: Any) -> "Failure":
        if isinstance(x, dict):
            return cls(
                id=(
                    _atd_read_int(x["id"])
                    if "id" in x
                    else _atd_missing_json_field("Failure", "id")
                ),
                error=(
                    Error.from_json(x["error"])
                    if "error" in x
                    else _atd_missing_json_field("Failure", "error")
                ),
            )
        else:
            _atd_bad_json("Failure", x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res["id"] = _atd_write_int(self.id)
        res["error"] = (lambda x: x.to_json())(self.error)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> "Failure":
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)
