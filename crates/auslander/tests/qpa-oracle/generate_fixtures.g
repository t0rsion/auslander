# Builds every auslander v0.1 fixture algebra in QPA and writes fixtures_qpa.json:
# algebra dimension, Cartan matrix (row i = dimension vector of the indecomposable
# projective P_i), dim Ext^k(S_i, S_j) for k = 0..4, and the dimension vector of
# DTr(M) = tau(M) for every simple S_i and every indecomposable injective I_i
# (the zero vector when the module is projective). The injective family supplies
# the non-simple, multi-entry tau cases across the suite; individual I_i may
# still be simple or projective. Also the injective dimension of every simple,
# capped at INJ_BOUND.
#
# Writes into the current working directory; run under GAP with QPA loadable
# (discovery order in README.md):
#
#   gap -q -T generate_fixtures.g
#
# QPA modules are right modules and paths compose left to right (p * q means first
# p, then q), matching auslander's conventions, so the values are written verbatim
# with "convention": "right". If this file is ever produced by a left-module setup,
# set "convention": "left" and the Rust comparator transposes Cartan matrices,
# swaps the (i, j) Ext indices, and reads tau rows as tau computed over the
# opposite algebra (left modules are right modules over A^op). GAP vertices are
# 1-based; the JSON keeps GAP's
# order, so QPA vertex v corresponds to auslander vertex v - 1, and the arrow lists
# below mirror the ArrowId order of the Rust constructors.

LoadPackage("qpa");

K := GF(5);
MAX_EXT := 4;
INJ_BOUND := 6;
OUT := "fixtures_qpa.json";

# dim Ext^k(M, N) via Ext^k(M, N) = Ext^1(Omega^(k-1) M, N); NthSyzygy computes
# minimal syzygies, so no projective summands disturb the isomorphism.
ExtDimension := function(M, N, k)
  local S;
  if k = 0 then
    return Length(HomOverAlgebra(M, N));
  fi;
  if Dimension(M) = 0 then
    return 0;
  fi;
  if k = 1 then
    return Length(ExtOverAlgebra(M, N)[2]);
  fi;
  S := NthSyzygy(M, k - 1);
  if Dimension(S) = 0 then
    return 0;
  fi;
  return Length(ExtOverAlgebra(S, N)[2]);
end;

# DimensionVector(DTr(S)); a projective S gets the zero vector directly, so QPA's
# TransposeOfModule never takes its projective branch (which prints a notice).
TauDimensionVector := function(S)
  if IsProjectiveModule(S) then
    return List(DimensionVector(S), x -> 0);
  fi;
  return DimensionVector(DTr(S));
end;

# InjDimensionOfModule(M, n) returns false when the injective dimension exceeds
# n; that refusal is written as INJ_BOUND + 1, which is the payload of the
# Bounded::AtLeast the library returns for the same bound.
InjDimensionValue := function(M)
  local d;
  d := InjDimensionOfModule(M, INJ_BOUND);
  if d = false then
    return INJ_BOUND + 1;
  fi;
  return d;
end;

FixtureRecord := function(name, A)
  local simples, projs, injs, i, j, ext, row;
  simples := SimpleModules(A);
  projs := IndecProjectiveModules(A);
  injs := IndecInjectiveModules(A);
  ext := [];
  for i in [1 .. Length(simples)] do
    row := [];
    for j in [1 .. Length(simples)] do
      Add(row, List([0 .. MAX_EXT], k -> ExtDimension(simples[i], simples[j], k)));
    od;
    Add(ext, row);
  od;
  return rec(name := name,
             num_vertices := Length(simples),
             dim := Dimension(A),
             cartan := List(projs, DimensionVector),
             tau := List(simples, TauDimensionVector),
             tau_injectives := List(injs, TauDimensionVector),
             injdim := List(simples, InjDimensionValue),
             ext := ext);
end;

JsonIntList := function(l)
  return Concatenation("[", JoinStringsWithSeparator(List(l, String), ", "), "]");
end;

JsonIntMatrix := function(m)
  return Concatenation("[", JoinStringsWithSeparator(List(m, JsonIntList), ", "), "]");
end;

EmitJson := function(fixtures)
  local out, i, j, fx, comma, rowcomma;
  out := OutputTextFile(OUT, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, "{\n");
  AppendTo(out, "  \"schema\": \"auslander-qpa-oracle-v4\",\n");
  AppendTo(out, "  \"convention\": \"right\",\n");
  AppendTo(out, "  \"max_ext_degree\": ", String(MAX_EXT), ",\n");
  AppendTo(out, "  \"injdim_bound\": ", String(INJ_BOUND), ",\n");
  AppendTo(out, "  \"fixtures\": [\n");
  for i in [1 .. Length(fixtures)] do
    fx := fixtures[i];
    AppendTo(out, "    {\n");
    AppendTo(out, "      \"name\": \"", fx.name, "\",\n");
    AppendTo(out, "      \"num_vertices\": ", String(fx.num_vertices), ",\n");
    AppendTo(out, "      \"dim\": ", String(fx.dim), ",\n");
    AppendTo(out, "      \"cartan\": ", JsonIntMatrix(fx.cartan), ",\n");
    AppendTo(out, "      \"tau\": ", JsonIntMatrix(fx.tau), ",\n");
    AppendTo(out, "      \"tau_injectives\": ", JsonIntMatrix(fx.tau_injectives), ",\n");
  AppendTo(out, "      \"injdim\": ", JsonIntList(fx.injdim), ",\n");
    AppendTo(out, "      \"ext\": [\n");
    for j in [1 .. Length(fx.ext)] do
      if j < Length(fx.ext) then rowcomma := ","; else rowcomma := ""; fi;
      AppendTo(out, "        ", JsonIntMatrix(fx.ext[j]), rowcomma, "\n");
    od;
    AppendTo(out, "      ]\n");
    if i < Length(fixtures) then comma := ","; else comma := ""; fi;
    AppendTo(out, "    }", comma, "\n");
  od;
  AppendTo(out, "  ]\n");
  AppendTo(out, "}\n");
  CloseStream(out);
end;

Fixtures := [];

# linear_an(2): 1 -> 2.
Q := Quiver(2, [[1, 2, "a1"]]);
Add(Fixtures, FixtureRecord("linear_an_2", PathAlgebra(K, Q)));

# linear_an(3): 1 -> 2 -> 3.
Q := Quiver(3, [[1, 2, "a1"], [2, 3, "a2"]]);
Add(Fixtures, FixtureRecord("linear_an_3", PathAlgebra(K, Q)));

# D4 star: three arrows into the center vertex 4.
Q := Quiver(4, [[1, 4, "a1"], [2, 4, "a2"], [3, 4, "a3"]]);
Add(Fixtures, FixtureRecord("d4_star", PathAlgebra(K, Q)));

# dual_numbers: k[x]/(x^2).
Q := Quiver(1, [[1, 1, "x"]]);
kQ := PathAlgebra(K, Q);
Add(Fixtures, FixtureRecord("dual_numbers", kQ / [kQ.x * kQ.x]));

# truncated_poly(3): k[x]/(x^3).
Q := Quiver(1, [[1, 1, "x"]]);
kQ := PathAlgebra(K, Q);
Add(Fixtures, FixtureRecord("truncated_poly_3", kQ / [kQ.x * kQ.x * kQ.x]));

# a3_mod_ab: kA_3/(a1 a2).
Q := Quiver(3, [[1, 2, "a1"], [2, 3, "a2"]]);
kQ := PathAlgebra(K, Q);
Add(Fixtures, FixtureRecord("a3_mod_ab", kQ / [kQ.a1 * kQ.a2]));

# kronecker(2): two parallel arrows 1 -> 2.
Q := Quiver(2, [[1, 2, "a1"], [1, 2, "a2"]]);
Add(Fixtures, FixtureRecord("kronecker_2", PathAlgebra(K, Q)));

# radical_square_zero_cycle(3): cycle 1 -> 2 -> 3 -> 1 with rad^2 = 0.
Q := Quiver(3, [[1, 2, "a1"], [2, 3, "a2"], [3, 1, "a3"]]);
kQ := PathAlgebra(K, Q);
Add(Fixtures, FixtureRecord("radical_square_zero_cycle_3",
    kQ / [kQ.a1 * kQ.a2, kQ.a2 * kQ.a3, kQ.a3 * kQ.a1]));

# linear_nakayama([3, 2, 1]): no relations survive; the path algebra of A_3 again,
# kept as its own fixture because the Rust constructor is a separate code path.
Q := Quiver(3, [[1, 2, "a1"], [2, 3, "a2"]]);
Add(Fixtures, FixtureRecord("linear_nakayama_3_2_1", PathAlgebra(K, Q)));

# linear_nakayama([2, 2, 1]) = kA_3/(a1 a2).
Q := Quiver(3, [[1, 2, "a1"], [2, 3, "a2"]]);
kQ := PathAlgebra(K, Q);
Add(Fixtures, FixtureRecord("linear_nakayama_2_2_1", kQ / [kQ.a1 * kQ.a2]));

# cyclic_nakayama([3, 3, 3]): cycle with J^3 = 0.
Q := Quiver(3, [[1, 2, "a1"], [2, 3, "a2"], [3, 1, "a3"]]);
kQ := PathAlgebra(K, Q);
Add(Fixtures, FixtureRecord("cyclic_nakayama_3_3_3",
    kQ / [kQ.a1 * kQ.a2 * kQ.a3, kQ.a2 * kQ.a3 * kQ.a1, kQ.a3 * kQ.a1 * kQ.a2]));

# gentle_tree: a1: 1 -> 2, a2: 2 -> 3, a3: 2 -> 4 with a1 a2 = 0.
Q := Quiver(4, [[1, 2, "a1"], [2, 3, "a2"], [2, 4, "a3"]]);
kQ := PathAlgebra(K, Q);
Add(Fixtures, FixtureRecord("gentle_tree", kQ / [kQ.a1 * kQ.a2]));

EmitJson(Fixtures);
Print("wrote ", OUT, " with ", Length(Fixtures), " fixtures\n");
QUIT;
