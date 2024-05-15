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
    raise ValueError(f"missing field '{json_field_name}'"
                     f" in JSON object of type '{type_name}'")


def _atd_bad_json(expected_type: str, json_value: Any) -> NoReturn:
    value_str = str(json_value)
    if len(value_str) > 200:
        value_str = value_str[:200] + '…'

    raise ValueError(f"incompatible JSON value where"
                     f" type '{expected_type}' was expected: '{value_str}'")


def _atd_bad_python(expected_type: str, json_value: Any) -> NoReturn:
    value_str = str(json_value)
    if len(value_str) > 200:
        value_str = value_str[:200] + '…'

    raise ValueError(f"incompatible Python value where"
                     f" type '{expected_type}' was expected: '{value_str}'")


def _atd_read_unit(x: Any) -> None:
    if x is None:
        return x
    else:
        _atd_bad_json('unit', x)


def _atd_read_bool(x: Any) -> bool:
    if isinstance(x, bool):
        return x
    else:
        _atd_bad_json('bool', x)


def _atd_read_int(x: Any) -> int:
    if isinstance(x, int):
        return x
    else:
        _atd_bad_json('int', x)


def _atd_read_float(x: Any) -> float:
    if isinstance(x, (int, float)):
        return x
    else:
        _atd_bad_json('float', x)


def _atd_read_string(x: Any) -> str:
    if isinstance(x, str):
        return x
    else:
        _atd_bad_json('str', x)


def _atd_read_list(
            read_elt: Callable[[Any], Any]
        ) -> Callable[[List[Any]], List[Any]]:
    def read_list(elts: List[Any]) -> List[Any]:
        if isinstance(elts, list):
            return [read_elt(elt) for elt in elts]
        else:
            _atd_bad_json('array', elts)
    return read_list


def _atd_read_assoc_array_into_dict(
            read_key: Callable[[Any], Any],
            read_value: Callable[[Any], Any],
        ) -> Callable[[List[Any]], Dict[Any, Any]]:
    def read_assoc(elts: List[List[Any]]) -> Dict[str, Any]:
        if isinstance(elts, list):
            return {read_key(elt[0]): read_value(elt[1]) for elt in elts}
        else:
            _atd_bad_json('array', elts)
            raise AssertionError('impossible')  # keep mypy happy
    return read_assoc


def _atd_read_assoc_object_into_dict(
            read_value: Callable[[Any], Any]
        ) -> Callable[[Dict[str, Any]], Dict[str, Any]]:
    def read_assoc(elts: Dict[str, Any]) -> Dict[str, Any]:
        if isinstance(elts, dict):
            return {_atd_read_string(k): read_value(v)
                    for k, v in elts.items()}
        else:
            _atd_bad_json('object', elts)
            raise AssertionError('impossible')  # keep mypy happy
    return read_assoc


def _atd_read_assoc_object_into_list(
            read_value: Callable[[Any], Any]
        ) -> Callable[[Dict[str, Any]], List[Tuple[str, Any]]]:
    def read_assoc(elts: Dict[str, Any]) -> List[Tuple[str, Any]]:
        if isinstance(elts, dict):
            return [(_atd_read_string(k), read_value(v))
                    for k, v in elts.items()]
        else:
            _atd_bad_json('object', elts)
            raise AssertionError('impossible')  # keep mypy happy
    return read_assoc


def _atd_read_nullable(read_elt: Callable[[Any], Any]) \
        -> Callable[[Optional[Any]], Optional[Any]]:
    def read_nullable(x: Any) -> Any:
        if x is None:
            return None
        else:
            return read_elt(x)
    return read_nullable


def _atd_read_option(read_elt: Callable[[Any], Any]) \
        -> Callable[[Optional[Any]], Optional[Any]]:
    def read_option(x: Any) -> Any:
        if x == 'None':
            return None
        elif isinstance(x, List) and len(x) == 2 and x[0] == 'Some':
            return read_elt(x[1])
        else:
            _atd_bad_json('option', x)
            raise AssertionError('impossible')  # keep mypy happy
    return read_option


def _atd_write_unit(x: Any) -> None:
    if x is None:
        return x
    else:
        _atd_bad_python('unit', x)


def _atd_write_bool(x: Any) -> bool:
    if isinstance(x, bool):
        return x
    else:
        _atd_bad_python('bool', x)


def _atd_write_int(x: Any) -> int:
    if isinstance(x, int):
        return x
    else:
        _atd_bad_python('int', x)


def _atd_write_float(x: Any) -> float:
    if isinstance(x, (int, float)):
        return x
    else:
        _atd_bad_python('float', x)


def _atd_write_string(x: Any) -> str:
    if isinstance(x, str):
        return x
    else:
        _atd_bad_python('str', x)


def _atd_write_list(
            write_elt: Callable[[Any], Any]
        ) -> Callable[[List[Any]], List[Any]]:
    def write_list(elts: List[Any]) -> List[Any]:
        if isinstance(elts, list):
            return [write_elt(elt) for elt in elts]
        else:
            _atd_bad_python('list', elts)
    return write_list


def _atd_write_assoc_dict_to_array(
            write_key: Callable[[Any], Any],
            write_value: Callable[[Any], Any]
        ) -> Callable[[Dict[Any, Any]], List[Tuple[Any, Any]]]:
    def write_assoc(elts: Dict[str, Any]) -> List[Tuple[str, Any]]:
        if isinstance(elts, dict):
            return [(write_key(k), write_value(v)) for k, v in elts.items()]
        else:
            _atd_bad_python('Dict[str, <value type>]]', elts)
            raise AssertionError('impossible')  # keep mypy happy
    return write_assoc


def _atd_write_assoc_dict_to_object(
            write_value: Callable[[Any], Any]
        ) -> Callable[[Dict[str, Any]], Dict[str, Any]]:
    def write_assoc(elts: Dict[str, Any]) -> Dict[str, Any]:
        if isinstance(elts, dict):
            return {_atd_write_string(k): write_value(v)
                    for k, v in elts.items()}
        else:
            _atd_bad_python('Dict[str, <value type>]', elts)
            raise AssertionError('impossible')  # keep mypy happy
    return write_assoc


def _atd_write_assoc_list_to_object(
            write_value: Callable[[Any], Any],
        ) -> Callable[[List[Any]], Dict[str, Any]]:
    def write_assoc(elts: List[List[Any]]) -> Dict[str, Any]:
        if isinstance(elts, list):
            return {_atd_write_string(elt[0]): write_value(elt[1])
                    for elt in elts}
        else:
            _atd_bad_python('List[Tuple[<key type>, <value type>]]', elts)
            raise AssertionError('impossible')  # keep mypy happy
    return write_assoc


def _atd_write_nullable(write_elt: Callable[[Any], Any]) \
        -> Callable[[Optional[Any]], Optional[Any]]:
    def write_nullable(x: Any) -> Any:
        if x is None:
            return None
        else:
            return write_elt(x)
    return write_nullable


def _atd_write_option(write_elt: Callable[[Any], Any]) \
        -> Callable[[Optional[Any]], Optional[Any]]:
    def write_option(x: Any) -> Any:
        if x is None:
            return 'None'
        else:
            return ['Some', write_elt(x)]
    return write_option


############################################################################
# Public classes
############################################################################


@dataclass
class StartParams:
    """Original type: start_params = { ... }"""

    env: int
    uri: str
    thm: str

    @classmethod
    def from_json(cls, x: Any) -> 'StartParams':
        if isinstance(x, dict):
            return cls(
                env=_atd_read_int(x['env']) if 'env' in x else _atd_missing_json_field('StartParams', 'env'),
                uri=_atd_read_string(x['uri']) if 'uri' in x else _atd_missing_json_field('StartParams', 'uri'),
                thm=_atd_read_string(x['thm']) if 'thm' in x else _atd_missing_json_field('StartParams', 'thm'),
            )
        else:
            _atd_bad_json('StartParams', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['env'] = _atd_write_int(self.env)
        res['uri'] = _atd_write_string(self.uri)
        res['thm'] = _atd_write_string(self.thm)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'StartParams':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class StartRequest:
    """Original type: start_request = { ... }"""

    id: int
    params: StartParams
    method: str = field(default_factory=lambda: 'petanque/start')

    @classmethod
    def from_json(cls, x: Any) -> 'StartRequest':
        if isinstance(x, dict):
            return cls(
                id=_atd_read_int(x['id']) if 'id' in x else _atd_missing_json_field('StartRequest', 'id'),
                params=StartParams.from_json(x['params']) if 'params' in x else _atd_missing_json_field('StartRequest', 'params'),
                method=_atd_read_string(x['method']) if 'method' in x else 'petanque/start',
            )
        else:
            _atd_bad_json('StartRequest', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['id'] = _atd_write_int(self.id)
        res['params'] = (lambda x: x.to_json())(self.params)
        res['method'] = _atd_write_string(self.method)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'StartRequest':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class CurrentState:
    """Original type: run_response = [ ... | Current_state of ... | ... ]"""

    value: int

    @property
    def kind(self) -> str:
        """Name of the class representing this variant."""
        return 'CurrentState'

    def to_json(self) -> Any:
        return ['Current_state', _atd_write_int(self.value)]

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class ProofFinished:
    """Original type: run_response = [ ... | Proof_finished of ... | ... ]"""

    value: int

    @property
    def kind(self) -> str:
        """Name of the class representing this variant."""
        return 'ProofFinished'

    def to_json(self) -> Any:
        return ['Proof_finished', _atd_write_int(self.value)]

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class RunResponse:
    """Original type: run_response = [ ... ]"""

    value: Union[CurrentState, ProofFinished]

    @property
    def kind(self) -> str:
        """Name of the class representing this variant."""
        return self.value.kind

    @classmethod
    def from_json(cls, x: Any) -> 'RunResponse':
        if isinstance(x, List) and len(x) == 2:
            cons = x[0]
            if cons == 'Current_state':
                return cls(CurrentState(_atd_read_int(x[1])))
            if cons == 'Proof_finished':
                return cls(ProofFinished(_atd_read_int(x[1])))
            _atd_bad_json('RunResponse', x)
        _atd_bad_json('RunResponse', x)

    def to_json(self) -> Any:
        return self.value.to_json()

    @classmethod
    def from_json_string(cls, x: str) -> 'RunResponse':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class RunParams:
    """Original type: run_params = { ... }"""

    st: int
    tac: str

    @classmethod
    def from_json(cls, x: Any) -> 'RunParams':
        if isinstance(x, dict):
            return cls(
                st=_atd_read_int(x['st']) if 'st' in x else _atd_missing_json_field('RunParams', 'st'),
                tac=_atd_read_string(x['tac']) if 'tac' in x else _atd_missing_json_field('RunParams', 'tac'),
            )
        else:
            _atd_bad_json('RunParams', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['st'] = _atd_write_int(self.st)
        res['tac'] = _atd_write_string(self.tac)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'RunParams':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class RunRequest:
    """Original type: run_request = { ... }"""

    id: int
    params: RunParams
    method: str = field(default_factory=lambda: 'petanque/run')

    @classmethod
    def from_json(cls, x: Any) -> 'RunRequest':
        if isinstance(x, dict):
            return cls(
                id=_atd_read_int(x['id']) if 'id' in x else _atd_missing_json_field('RunRequest', 'id'),
                params=RunParams.from_json(x['params']) if 'params' in x else _atd_missing_json_field('RunRequest', 'params'),
                method=_atd_read_string(x['method']) if 'method' in x else 'petanque/run',
            )
        else:
            _atd_bad_json('RunRequest', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['id'] = _atd_write_int(self.id)
        res['params'] = (lambda x: x.to_json())(self.params)
        res['method'] = _atd_write_string(self.method)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'RunRequest':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class Response:
    """Original type: response = { ... }"""

    id: int
    result: Any

    @classmethod
    def from_json(cls, x: Any) -> 'Response':
        if isinstance(x, dict):
            return cls(
                id=_atd_read_int(x['id']) if 'id' in x else _atd_missing_json_field('Response', 'id'),
                result=(lambda x: x)(x['result']) if 'result' in x else _atd_missing_json_field('Response', 'result'),
            )
        else:
            _atd_bad_json('Response', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['id'] = _atd_write_int(self.id)
        res['result'] = (lambda x: x)(self.result)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'Response':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class PremisesResponse:
    """Original type: premises_response"""

    value: Any

    @classmethod
    def from_json(cls, x: Any) -> 'PremisesResponse':
        return cls((lambda x: x)(x))

    def to_json(self) -> Any:
        return (lambda x: x)(self.value)

    @classmethod
    def from_json_string(cls, x: str) -> 'PremisesResponse':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class PremisesParams:
    """Original type: premises_params = { ... }"""

    st: int

    @classmethod
    def from_json(cls, x: Any) -> 'PremisesParams':
        if isinstance(x, dict):
            return cls(
                st=_atd_read_int(x['st']) if 'st' in x else _atd_missing_json_field('PremisesParams', 'st'),
            )
        else:
            _atd_bad_json('PremisesParams', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['st'] = _atd_write_int(self.st)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'PremisesParams':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class PremisesRequest:
    """Original type: premises_request = { ... }"""

    id: int
    params: PremisesParams
    method: str = field(default_factory=lambda: 'petanque/premises')

    @classmethod
    def from_json(cls, x: Any) -> 'PremisesRequest':
        if isinstance(x, dict):
            return cls(
                id=_atd_read_int(x['id']) if 'id' in x else _atd_missing_json_field('PremisesRequest', 'id'),
                params=PremisesParams.from_json(x['params']) if 'params' in x else _atd_missing_json_field('PremisesRequest', 'params'),
                method=_atd_read_string(x['method']) if 'method' in x else 'petanque/premises',
            )
        else:
            _atd_bad_json('PremisesRequest', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['id'] = _atd_write_int(self.id)
        res['params'] = (lambda x: x.to_json())(self.params)
        res['method'] = _atd_write_string(self.method)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'PremisesRequest':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class InitResponse:
    """Original type: init_response = { ... }"""

    id: int
    result: int

    @classmethod
    def from_json(cls, x: Any) -> 'InitResponse':
        if isinstance(x, dict):
            return cls(
                id=_atd_read_int(x['id']) if 'id' in x else _atd_missing_json_field('InitResponse', 'id'),
                result=_atd_read_int(x['result']) if 'result' in x else _atd_missing_json_field('InitResponse', 'result'),
            )
        else:
            _atd_bad_json('InitResponse', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['id'] = _atd_write_int(self.id)
        res['result'] = _atd_write_int(self.result)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'InitResponse':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class InitParams:
    """Original type: init_params = { ... }"""

    root: str
    debug: bool = field(default_factory=lambda: False)

    @classmethod
    def from_json(cls, x: Any) -> 'InitParams':
        if isinstance(x, dict):
            return cls(
                root=_atd_read_string(x['root']) if 'root' in x else _atd_missing_json_field('InitParams', 'root'),
                debug=_atd_read_bool(x['debug']) if 'debug' in x else False,
            )
        else:
            _atd_bad_json('InitParams', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['root'] = _atd_write_string(self.root)
        res['debug'] = _atd_write_bool(self.debug)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'InitParams':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class InitRequest:
    """Original type: init_request = { ... }"""

    id: int
    params: InitParams
    method: str = field(default_factory=lambda: 'petanque/init')

    @classmethod
    def from_json(cls, x: Any) -> 'InitRequest':
        if isinstance(x, dict):
            return cls(
                id=_atd_read_int(x['id']) if 'id' in x else _atd_missing_json_field('InitRequest', 'id'),
                params=InitParams.from_json(x['params']) if 'params' in x else _atd_missing_json_field('InitRequest', 'params'),
                method=_atd_read_string(x['method']) if 'method' in x else 'petanque/init',
            )
        else:
            _atd_bad_json('InitRequest', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['id'] = _atd_write_int(self.id)
        res['params'] = (lambda x: x.to_json())(self.params)
        res['method'] = _atd_write_string(self.method)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'InitRequest':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class GoalsResponse:
    """Original type: goals_response = { ... }"""

    goals: List[Any]

    @classmethod
    def from_json(cls, x: Any) -> 'GoalsResponse':
        if isinstance(x, dict):
            return cls(
                goals=_atd_read_list((lambda x: x))(x['goals']) if 'goals' in x else _atd_missing_json_field('GoalsResponse', 'goals'),
            )
        else:
            _atd_bad_json('GoalsResponse', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['goals'] = _atd_write_list((lambda x: x))(self.goals)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'GoalsResponse':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class GoalsParams:
    """Original type: goals_params = { ... }"""

    st: int

    @classmethod
    def from_json(cls, x: Any) -> 'GoalsParams':
        if isinstance(x, dict):
            return cls(
                st=_atd_read_int(x['st']) if 'st' in x else _atd_missing_json_field('GoalsParams', 'st'),
            )
        else:
            _atd_bad_json('GoalsParams', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['st'] = _atd_write_int(self.st)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'GoalsParams':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class GoalsRequest:
    """Original type: goals_request = { ... }"""

    id: int
    params: GoalsParams
    method: str = field(default_factory=lambda: 'petanque/goals')

    @classmethod
    def from_json(cls, x: Any) -> 'GoalsRequest':
        if isinstance(x, dict):
            return cls(
                id=_atd_read_int(x['id']) if 'id' in x else _atd_missing_json_field('GoalsRequest', 'id'),
                params=GoalsParams.from_json(x['params']) if 'params' in x else _atd_missing_json_field('GoalsRequest', 'params'),
                method=_atd_read_string(x['method']) if 'method' in x else 'petanque/goals',
            )
        else:
            _atd_bad_json('GoalsRequest', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['id'] = _atd_write_int(self.id)
        res['params'] = (lambda x: x.to_json())(self.params)
        res['method'] = _atd_write_string(self.method)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'GoalsRequest':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class Error:
    """Original type: error = { ... }"""

    code: int
    message: str

    @classmethod
    def from_json(cls, x: Any) -> 'Error':
        if isinstance(x, dict):
            return cls(
                code=_atd_read_int(x['code']) if 'code' in x else _atd_missing_json_field('Error', 'code'),
                message=_atd_read_string(x['message']) if 'message' in x else _atd_missing_json_field('Error', 'message'),
            )
        else:
            _atd_bad_json('Error', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['code'] = _atd_write_int(self.code)
        res['message'] = _atd_write_string(self.message)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'Error':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)


@dataclass
class Failure:
    """Original type: failure = { ... }"""

    id: int
    error: Error

    @classmethod
    def from_json(cls, x: Any) -> 'Failure':
        if isinstance(x, dict):
            return cls(
                id=_atd_read_int(x['id']) if 'id' in x else _atd_missing_json_field('Failure', 'id'),
                error=Error.from_json(x['error']) if 'error' in x else _atd_missing_json_field('Failure', 'error'),
            )
        else:
            _atd_bad_json('Failure', x)

    def to_json(self) -> Any:
        res: Dict[str, Any] = {}
        res['id'] = _atd_write_int(self.id)
        res['error'] = (lambda x: x.to_json())(self.error)
        return res

    @classmethod
    def from_json_string(cls, x: str) -> 'Failure':
        return cls.from_json(json.loads(x))

    def to_json_string(self, **kw: Any) -> str:
        return json.dumps(self.to_json(), **kw)
