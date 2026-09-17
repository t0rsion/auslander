from ._core import (
    _CoreValue,
    ArQuiver,
    BarLimits,
    CatalogEnumeration,
    ClosedSupportTauTiltingGraph,
    HochschildCohomology,
    IncompleteHochschildCohomology,
    IncompleteSupportTauTiltingGraph,
    Module,
    MutationGraphLimits,
    PrimeField,
    Quiver,
)
from ._catalog import IndecomposableCatalog


class Algebra(_CoreValue):
    def __init__(
        self,
        quiver: Quiver,
        forbidden: list[list[int]],
        field: PrimeField | None = ...,
    ) -> None: ...

    @staticmethod
    def from_relations(
        quiver: Quiver,
        relations: list[list[tuple[int, list[int]]]],
        field: PrimeField,
        *,
        max_basis: int | None = ...,
        max_word_len: int | None = ...,
        max_steps: int | None = ...,
        max_origin_terms: int | None = ...,
        max_ambiguities: int | None = ...,
    ) -> Algebra: ...

    @staticmethod
    def from_certificate(
        json: str,
        *,
        field: PrimeField | None = ...,
        max_basis: int | None = ...,
        max_word_len: int | None = ...,
        max_steps: int | None = ...,
        max_origin_terms: int | None = ...,
        max_ambiguities: int | None = ...,
    ) -> Algebra: ...

    @staticmethod
    def linear_an(n: int, field: PrimeField | None = ...) -> Algebra: ...

    @staticmethod
    def kronecker(m: int, field: PrimeField | None = ...) -> Algebra: ...

    @staticmethod
    def dual_numbers(field: PrimeField | None = ...) -> Algebra: ...

    @staticmethod
    def truncated_poly(n: int, field: PrimeField | None = ...) -> Algebra: ...

    @staticmethod
    def linear_nakayama(
        kupisch: list[int], field: PrimeField | None = ...
    ) -> Algebra: ...

    @staticmethod
    def cyclic_nakayama(
        kupisch: list[int], field: PrimeField | None = ...
    ) -> Algebra: ...

    @staticmethod
    def radical_square_zero_cycle(
        n: int, field: PrimeField | None = ...
    ) -> Algebra: ...

    @staticmethod
    def an_with_relations(
        n: int,
        zero_paths: list[tuple[int, int]],
        field: PrimeField | None = ...,
    ) -> Algebra: ...

    def over(self, field: PrimeField) -> Algebra: ...
    def certificate_json(self, field: PrimeField | None = ...) -> str: ...
    def module(
        self,
        dims: list[int],
        maps: list[list[list[int]]],
        field: PrimeField | None = ...,
    ) -> Module: ...
    def module_sparse(
        self,
        dims: list[int],
        maps: list[list[tuple[int, int, int]]],
        field: PrimeField | None = ...,
    ) -> Module: ...
    def simple(self, vertex: int, field: PrimeField | None = ...) -> Module: ...
    def projective(self, vertex: int, field: PrimeField | None = ...) -> Module: ...
    def injective(self, vertex: int, field: PrimeField | None = ...) -> Module: ...
    def catalog(self, field: PrimeField | None = ...) -> IndecomposableCatalog: ...
    def ar_quiver(self, field: PrimeField | None = ...) -> ArQuiver: ...
    def enumerate_over_catalog(self, field: PrimeField | None = ...) -> CatalogEnumeration: ...
    def support_tau_tilting_graph(
        self,
        field: PrimeField | None = ...,
        *,
        limits: MutationGraphLimits | None = ...,
    ) -> ClosedSupportTauTiltingGraph | IncompleteSupportTauTiltingGraph: ...
    def hochschild_cohomology(
        self,
        max_degree: int,
        limits: BarLimits,
        field: PrimeField | None = ...,
    ) -> HochschildCohomology | IncompleteHochschildCohomology: ...

    @property
    def field(self) -> PrimeField | None: ...

    @property
    def quiver(self) -> Quiver: ...

    @property
    def dim(self) -> int: ...

    @property
    def num_vertices(self) -> int: ...

    @property
    def num_arrows(self) -> int: ...

    @property
    def completion_limits(self) -> dict[str, int]: ...

    def cartan_matrix(self) -> list[list[int]]: ...
