"""Build checked values and run bounded computations from canonical JSON."""

from __future__ import annotations

from dataclasses import dataclass
import json
import struct
from typing import Any, Callable

from .parser import parse_presentation


REQUEST_SCHEMA = "auslander-compute-v1"
RESULT_SCHEMA = "auslander-compute-result-v1"
_MAP_KEYS = ("maps", "sparse_maps")
_RUST_USIZE_MAX = (1 << (8 * struct.calcsize("P"))) - 1


@dataclass(frozen=True)
class _Context:
    algebra: Any
    field: Any
    summary: dict[str, Any]
    modules: dict[str, Any]


def _reject_constant(value: str) -> None:
    raise ValueError(f"JSON constant {value!r} is not allowed")


def _pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON field {key!r}")
        result[key] = value
    return result


def _load_json(text: str) -> Any:
    try:
        return json.loads(
            text,
            object_pairs_hook=_pairs,
            parse_constant=_reject_constant,
        )
    except json.JSONDecodeError as error:
        raise ValueError(f"invalid JSON at line {error.lineno}, column {error.colno}") from None


def _object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError(f"{label} must be an object")
    return value


def _fields(
    value: dict[str, Any],
    required: set[str],
    optional: set[str],
    label: str,
) -> None:
    unknown = sorted(set(value) - required - optional)
    if unknown:
        raise ValueError(f"{label} has unknown fields: {', '.join(unknown)}")
    missing = sorted(required - set(value))
    if missing:
        raise ValueError(f"{label} is missing fields: {', '.join(missing)}")


def _string(value: Any, label: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{label} must be a string")
    return value


def _integer(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{label} must be an integer")
    return value


def _nonnegative(value: Any, label: str) -> int:
    number = _integer(value, label)
    if number < 0:
        raise ValueError(f"{label} must be nonnegative")
    if number > _RUST_USIZE_MAX:
        raise ValueError(f"{label} does not fit Rust usize")
    return number


def _name(value: Any, label: str) -> str:
    name = _string(value, label)
    if not name.isidentifier():
        raise ValueError(f"{label} must be a Python identifier")
    return name


def _dimensions(value: Any, label: str) -> list[int]:
    if not isinstance(value, list):
        raise ValueError(f"{label} must be an array")
    return [_nonnegative(item, f"{label}[{index}]") for index, item in enumerate(value)]


def _rows(value: Any, label: str) -> list[list[int]]:
    if not isinstance(value, list):
        raise ValueError(f"{label} must be an array of rows")
    rows: list[list[int]] = []
    for row_index, row in enumerate(value):
        if not isinstance(row, list):
            raise ValueError(f"{label}[{row_index}] must be an array")
        rows.append(
            [_integer(item, f"{label}[{row_index}][{column}]") for column, item in enumerate(row)]
        )
    return rows


def _dense_maps(value: Any) -> list[list[list[int]]]:
    if not isinstance(value, list):
        raise ValueError("maps must be an array")
    return [_rows(item, f"maps[{index}]") for index, item in enumerate(value)]


def _sparse_entry(value: Any, label: str) -> tuple[int, int, int]:
    if not isinstance(value, list) or len(value) != 3:
        raise ValueError(f"{label} must be [row, column, value]")
    return (
        _nonnegative(value[0], f"{label}[0]"),
        _nonnegative(value[1], f"{label}[1]"),
        _integer(value[2], f"{label}[2]"),
    )


def _sparse_maps(value: Any) -> list[list[tuple[int, int, int]]]:
    if not isinstance(value, list):
        raise ValueError("sparse_maps must be an array")
    maps: list[list[tuple[int, int, int]]] = []
    for map_index, entries in enumerate(value):
        if not isinstance(entries, list):
            raise ValueError(f"sparse_maps[{map_index}] must be an array")
        maps.append(
            [
                _sparse_entry(entry, f"sparse_maps[{map_index}][{entry_index}]")
                for entry_index, entry in enumerate(entries)
            ]
        )
    return maps


def _module_recipe(recipe: Any, name: str) -> tuple[list[int], Any]:
    value = _object(recipe, f"module {name!r}")
    _fields(value, {"dims"}, set(_MAP_KEYS), f"module {name!r}")
    selected = [key for key in _MAP_KEYS if key in value]
    if len(selected) != 1:
        raise ValueError(f"module {name!r} must define exactly one map field")
    dims = _dimensions(value["dims"], f"module {name!r}.dims")
    if selected[0] == "maps":
        return dims, _dense_maps(value["maps"])
    return dims, _sparse_maps(value[selected[0]])


def _build_algebra(spec: Any) -> tuple[Any, Any]:
    value = _object(spec, "algebra")
    _fields(value, set(), {"presentation", "certificate"}, "algebra")
    if len(value) != 1:
        raise ValueError("algebra must define exactly one of presentation or certificate")
    if "presentation" in value:
        presentation = _string(value["presentation"], "algebra.presentation")
        parsed = parse_presentation(presentation)
        return parsed.build(), parsed.field
    certificate = _string(value["certificate"], "algebra.certificate")
    from . import Algebra

    algebra = Algebra.from_certificate(certificate)
    field = algebra.field
    if field is None:
        raise ValueError("algebra certificate does not name a field")
    return algebra, field.p


def _certificate(algebra: Any, field: Any) -> Any:
    from . import PrimeField

    text = algebra.certificate_json(PrimeField(field))
    return _load_json(text)


def _algebra_summary(algebra: Any, field: Any) -> dict[str, Any]:
    certificate = _certificate(algebra, field)
    return {
        "field": field,
        "dimension": algebra.dim,
        "vertices": algebra.num_vertices,
        "arrows": [list(arrow) for arrow in algebra.quiver.arrows],
        "cartan_matrix": algebra.cartan_matrix(),
        "certificate": certificate,
    }


def _build_modules(algebra: Any, field: Any, recipes: Any) -> dict[str, Any]:
    values = _object(recipes, "modules")
    from . import PrimeField

    prime = PrimeField(field)
    modules: dict[str, Any] = {}
    for raw_name in sorted(values):
        name = _name(raw_name, "module name")
        dims, maps = _module_recipe(values[raw_name], name)
        try:
            if "maps" in values[raw_name]:
                module = algebra.module(dims, maps, field=prime)
            else:
                module = algebra.module_sparse(dims, maps, field=prime)
        except (TypeError, ValueError, OverflowError) as error:
            raise ValueError(f"module {name!r} rejected: {error}") from None
        modules[name] = module
    return modules


def _module_summary(module: Any) -> dict[str, Any]:
    return {"dims": module.dims, "total_dim": module.total_dim, "maps": module.maps}


def _module(context: _Context, value: Any, label: str) -> tuple[str, Any]:
    name = _name(value, label)
    try:
        return name, context.modules[name]
    except KeyError:
        raise ValueError(f"unknown module name {name!r}") from None


def _pair(context: _Context, operation: dict[str, Any]) -> tuple[str, Any, str, Any]:
    source_name, source = _module(context, operation["source"], "source")
    target_name, target = _module(context, operation["target"], "target")
    return source_name, source, target_name, target


def _morphism_maps(morphism: Any) -> Any:
    return morphism.maps


def _bounded(value: Any) -> dict[str, Any]:
    exact = value.exact
    if exact is not None:
        return {"kind": "exact", "value": exact}
    lower = value.at_least
    if lower is not None:
        return {"kind": "at_least", "value": lower}
    raise ValueError("core returned an invalid bounded value")


def _resolution_status(status: Any) -> dict[str, Any]:
    if status.at is None:
        return {"kind": "finite"}
    return {"kind": "cut", "at": status.at}


def _op_algebra_summary(context: _Context, operation: dict[str, Any]) -> Any:
    return context.summary


def _op_hom_dim(context: _Context, operation: dict[str, Any]) -> dict[str, Any]:
    source_name, source, target_name, target = _pair(context, operation)
    return {
        "source": source_name,
        "target": target_name,
        "dimension": source.hom_dim(target),
    }


def _op_hom(context: _Context, operation: dict[str, Any]) -> dict[str, Any]:
    source_name, source, target_name, target = _pair(context, operation)
    basis = source.hom(target)
    return {
        "source": source_name,
        "target": target_name,
        "dimension": len(basis),
        "basis": [_morphism_maps(item) for item in basis],
    }


def _op_stable_hom(context: _Context, operation: dict[str, Any]) -> dict[str, Any]:
    source_name, source, target_name, target = _pair(context, operation)
    space = source.stable_hom(target)
    return {
        "source": source_name,
        "target": target_name,
        "dimension": space.dim,
        "projective_factor_dimension": space.projective_factor_dim,
        "basis": [_morphism_maps(item) for item in space.basis],
        "projective_factor_basis": [
            _morphism_maps(item) for item in space.projective_factor_basis
        ],
    }


def _op_stable_hom_dim(context: _Context, operation: dict[str, Any]) -> dict[str, Any]:
    source_name, source, target_name, target = _pair(context, operation)
    return {
        "source": source_name,
        "target": target_name,
        "dimension": source.stable_hom_dim(target),
    }


def _op_ext_table(context: _Context, operation: dict[str, Any]) -> dict[str, Any]:
    source_name, source, target_name, target = _pair(context, operation)
    degree = _nonnegative(operation["max_degree"], "max_degree")
    return {
        "source": source_name,
        "target": target_name,
        "max_degree": degree,
        "dimensions": source.ext_table(target, degree),
    }


def _op_tau(context: _Context, operation: dict[str, Any]) -> dict[str, Any]:
    name, module = _module(context, operation["module"], "module")
    return {"module": name, "tau": _module_summary(module.tau())}


def _resolution_value(resolution: Any, name: str, bound: int) -> dict[str, Any]:
    projective_dimension = getattr(resolution, "projective_dimension", None)
    if projective_dimension is None:
        projective_dimension = resolution.pd(bound)
    return {
        "module": name,
        "status": _resolution_status(resolution.status),
        "projective_dimension": _bounded(projective_dimension),
        "terms": [_module_summary(term) for term in resolution.terms],
        "differentials": [_morphism_maps(item) for item in resolution.maps],
        "augmentation": _morphism_maps(resolution.augmentation),
    }


def _op_resolve(context: _Context, operation: dict[str, Any]) -> dict[str, Any]:
    name, module = _module(context, operation["module"], "module")
    steps = _nonnegative(operation["steps"], "steps")
    return _resolution_value(module.resolve(steps), name, steps)


def _certificate_record(certificate: Any) -> dict[str, Any]:
    record = {"kind": certificate.kind}
    if certificate.attempts is not None:
        record["attempts"] = certificate.attempts
    return record


def _op_decompose(context: _Context, operation: dict[str, Any]) -> dict[str, Any]:
    name, module = _module(context, operation["module"], "module")
    decomposition = module.decompose()
    return {
        "module": name,
        "summands": [_module_summary(item) for item in decomposition.summands],
        "certificates": [_certificate_record(item) for item in decomposition.certificates],
        "inclusions": [_morphism_maps(item) for item in decomposition.inclusions],
        "projections": [_morphism_maps(item) for item in decomposition.projections],
        "idempotents": [
            _morphism_maps(projection.then(inclusion))
            for projection, inclusion in zip(
                decomposition.projections, decomposition.inclusions
            )
        ],
    }


def _optional_nonnegative(value: Any, label: str) -> int | None:
    return None if value is None else _nonnegative(value, label)


def _batch_names(context: _Context, value: Any) -> tuple[list[str], dict[str, int]]:
    if not isinstance(value, list):
        raise ValueError("homological_batch.modules must be an array")
    names = [_name(item, "homological_batch module") for item in value]
    if len(set(names)) != len(names):
        raise ValueError("homological_batch.modules must contain distinct names")
    for name in names:
        if name not in context.modules:
            raise ValueError(f"unknown module name {name!r}")
    return names, {name: index for index, name in enumerate(names)}


def _batch_endpoint(
    value: Any,
    names: list[str],
    indices: dict[str, int],
    label: str,
) -> int:
    if isinstance(value, bool):
        raise ValueError(f"{label} must be a module name or index")
    if isinstance(value, int):
        index = _nonnegative(value, label)
        if index >= len(names):
            raise ValueError(f"{label} index {index} is outside the module list")
        return index
    name = _name(value, label)
    try:
        return indices[name]
    except KeyError:
        raise ValueError(f"{label} name {name!r} is outside the module list") from None


def _batch_pairs(value: Any, names: list[str], indices: dict[str, int]) -> list[tuple[int, int]]:
    if not isinstance(value, list):
        raise ValueError("homological_batch.pairs must be an array")
    pairs: list[tuple[int, int]] = []
    for position, pair in enumerate(value):
        if not isinstance(pair, list) or len(pair) != 2:
            raise ValueError(f"homological_batch.pairs[{position}] must have two endpoints")
        pairs.append(
            (
                _batch_endpoint(pair[0], names, indices, f"pair {position} source"),
                _batch_endpoint(pair[1], names, indices, f"pair {position} target"),
            )
        )
    return pairs


def _batch_limits(operation: dict[str, Any]) -> Any:
    from . import HomologicalBatchLimits

    return HomologicalBatchLimits(
        _optional_nonnegative(operation.get("max_pairs"), "max_pairs"),
        _optional_nonnegative(operation.get("max_ext_cells"), "max_ext_cells"),
    )


def _batch_resolution_records(batch: Any, names: list[str], max_degree: int) -> list[Any]:
    records: list[Any] = []
    for index, name in enumerate(names):
        resolution = batch.resolution(index)
        if resolution is not None:
            record = _resolution_value(resolution, name, max_degree)
            record["source_index"] = index
            records.append(record)
    return records


def _batch_pair_record(pair: Any, names: list[str]) -> dict[str, Any]:
    source = pair.source
    target = pair.target
    return {
        "source": names[source],
        "target": names[target],
        "source_index": source,
        "target_index": target,
        "hom_dim": pair.hom_dim,
        "stable_hom_dim": pair.stable_hom_dim,
        "ext_dimensions": pair.ext_dimensions,
    }


def _op_homological_batch(context: _Context, operation: dict[str, Any]) -> dict[str, Any]:
    from . import HomologicalBatch

    names, indices = _batch_names(context, operation["modules"])
    max_degree = _nonnegative(operation["max_degree"], "max_degree")
    has_pairs = "pairs" in operation
    has_all_pairs = "all_pairs" in operation
    if has_pairs == has_all_pairs:
        raise ValueError("homological_batch needs exactly one of pairs or all_pairs")
    limits = _batch_limits(operation)
    modules = [context.modules[name] for name in names]
    if has_all_pairs:
        if operation["all_pairs"] is not True:
            raise ValueError("homological_batch.all_pairs must be true")
        batch = HomologicalBatch.all_pairs(modules, max_degree, limits)
    else:
        batch = HomologicalBatch(
            modules,
            max_degree,
            _batch_pairs(operation["pairs"], names, indices),
            limits,
        )
    selected = [
        {
            "source": names[source],
            "target": names[target],
            "source_index": source,
            "target_index": target,
        }
        for source, target in batch.selected_pairs
    ]
    return {
        "modules": names,
        "max_degree": max_degree,
        "selected_pairs": selected,
        "pairs": [_batch_pair_record(item, names) for item in batch.pairs],
        "work": {
            "resolutions": batch.work.resolutions,
            "target_covers": batch.work.target_covers,
            "hom_spaces": batch.work.hom_spaces,
            "projective_factor_spaces": batch.work.projective_factor_spaces,
            "ext_tables": batch.work.ext_tables,
        },
        "resolutions": _batch_resolution_records(batch, names, max_degree),
    }


_OPERATION_FIELDS: dict[str, tuple[set[str], set[str]]] = {
    "algebra_summary": (set(), set()),
    "hom_dim": ({"source", "target"}, set()),
    "hom": ({"source", "target"}, set()),
    "stable_hom_dim": ({"source", "target"}, set()),
    "stable_hom": ({"source", "target"}, set()),
    "ext_table": ({"source", "target", "max_degree"}, set()),
    "tau": ({"module"}, set()),
    "resolve": ({"module", "steps"}, set()),
    "decompose": ({"module"}, set()),
    "homological_batch": (
        {"modules", "max_degree"},
        {"pairs", "all_pairs", "max_pairs", "max_ext_cells"},
    ),
}

_HANDLERS: dict[str, Callable[[_Context, dict[str, Any]], Any]] = {
    "algebra_summary": _op_algebra_summary,
    "hom_dim": _op_hom_dim,
    "hom": _op_hom,
    "stable_hom_dim": _op_stable_hom_dim,
    "stable_hom": _op_stable_hom,
    "ext_table": _op_ext_table,
    "tau": _op_tau,
    "resolve": _op_resolve,
    "decompose": _op_decompose,
    "homological_batch": _op_homological_batch,
}


def _validated_operation(operation: Any) -> tuple[str, dict[str, Any]]:
    value = _object(operation, "operation")
    allowed = set().union(
        *(required | optional for required, optional in _OPERATION_FIELDS.values())
    )
    _fields(value, {"op"}, allowed, "operation")
    op = _string(value["op"], "operation.op")
    try:
        required, optional = _OPERATION_FIELDS[op]
    except KeyError:
        raise ValueError(f"unknown operation {op!r}") from None
    _fields(value, {"op", *required}, optional, f"operation {op!r}")
    return op, value


def _run_operations(context: _Context, operations: Any) -> list[dict[str, Any]]:
    if not isinstance(operations, list):
        raise ValueError("operations must be an array")
    results: list[dict[str, Any]] = []
    for index, raw_operation in enumerate(operations):
        op, operation = _validated_operation(raw_operation)
        results.append(
            {
                "index": index,
                "op": op,
                "status": "complete",
                "value": _HANDLERS[op](context, operation),
            }
        )
    return results


def compute_request(document: Any) -> dict[str, Any]:
    """Compute a strict `auslander-compute-v1` request."""
    value = _object(document, "request")
    _fields(value, {"schema", "algebra", "modules", "operations"}, set(), "request")
    if value["schema"] != REQUEST_SCHEMA:
        raise ValueError(f"unsupported request schema {value['schema']!r}")
    algebra, field = _build_algebra(value["algebra"])
    modules = _build_modules(algebra, field, value["modules"])
    context = _Context(algebra, field, _algebra_summary(algebra, field), modules)
    return {
        "schema": RESULT_SCHEMA,
        "request_schema": REQUEST_SCHEMA,
        "algebra": context.summary,
        "modules": {name: _module_summary(module) for name, module in modules.items()},
        "results": _run_operations(context, value["operations"]),
    }


def compute_json(text: str) -> str:
    """Compute one request and return canonical JSON without a trailing newline."""
    if not isinstance(text, str):
        raise TypeError("request must be text")
    result = compute_request(_load_json(text))
    return json.dumps(result, ensure_ascii=True, allow_nan=False, sort_keys=True, separators=(",", ":"))
