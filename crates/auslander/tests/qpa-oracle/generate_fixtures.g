# Builds every auslander v0.3 fixture algebra in QPA and writes fixtures_qpa.json
# with schema auslander-qpa-oracle-v5. Each fixture carries its own prime field
# and its full presentation: the quiver, and relations as integer combinations
# of paths given by arrow indices. The results per fixture: algebra dimension,
# dimension vectors of the indecomposable projectives (the Cartan rows) and
# injectives, projective and injective dimensions of the simples (typed, bounded
# at 6), tau of the simples and of the indecomposable injectives (typed), the
# decomposition of the direct sum of the nonzero radicals of the indecomposable
# projectives (summand dimension vectors with multiplicities, sorted), and
# dim Ext^k(S_i, S_j) for k = 0..4.
#
# Writes into the current working directory; run under GAP with QPA loadable
# (discovery order in README.md):
#
#   gap -q -T generate_fixtures.g
#
# QPA modules are right modules and paths compose left to right (p * q means
# first p, then q), matching auslander's conventions, so the values are written
# verbatim with "convention": "right". GAP vertices and arrows are 1-based; the
# JSON is 0-based throughout. The arrow list order below fixes the ArrowId order
# of the sealed term order "deglex-arrowid-v1" on the Rust side.
#
# Relation coefficients are integers. The consumer reduces them mod the fixture
# field and drops terms that reduce to zero. The characteristic-sensitive family
# depends on that rule: ab - 2cd loses its second term over F_2. GAP applies the
# same reduction when it builds the relation elements, so both sides construct
# the same ideal from the same bytes.

LoadPackage("qpa");

MAX_EXT := 4;
PROJDIM_BOUND := 6;
INJDIM_BOUND := 6;
ORDER_ID := "deglex-arrowid-v1";
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

# A projective module gets the typed marker directly, so QPA's TransposeOfModule
# never takes its projective branch (which prints a notice).
TauJson := function(M)
  if IsProjectiveModule(M) then
    return "{\"projective\": true}";
  fi;
  return Concatenation("{\"dimvec\": [",
      JoinStringsWithSeparator(List(DimensionVector(DTr(M)), String), ", "),
      "]}");
end;

# ProjDimensionOfModule and InjDimensionOfModule return false when the dimension
# exceeds the bound; that refusal is written as {"at_least": bound + 1}, the
# payload of the Bounded::AtLeast the library returns for the same bound.
BoundedJson := function(d, bound)
  if d = false then
    return Concatenation("{\"at_least\": ", String(bound + 1), "}");
  fi;
  return Concatenation("{\"finite\": ", String(d), "}");
end;

# The designated test module is the direct sum of the nonzero radicals of the
# indecomposable projectives. Summands are reported as [dimvec, multiplicity]
# pairs, sorted by dimension vector lexicographically and merged on equal
# dimension vectors, so QPA's decomposition order never reaches the file.
DecompositionPairs := function(projs)
  local rads, pairs, merged, d, i, pr;
  rads := Filtered(List(projs, RadicalOfModule), M -> Dimension(M) > 0);
  if Length(rads) = 0 then
    return [];
  fi;
  d := DecomposeModuleWithMultiplicities(DirectSumOfQPAModules(rads));
  pairs := List([1 .. Length(d[1])],
      i -> [ShallowCopy(DimensionVector(d[1][i])), d[2][i]]);
  Sort(pairs);
  merged := [];
  for pr in pairs do
    if Length(merged) > 0 and merged[Length(merged)][1] = pr[1] then
      merged[Length(merged)][2] := merged[Length(merged)][2] + pr[2];
    else
      Add(merged, pr);
    fi;
  od;
  return merged;
end;

# spec: family, case name, prime, presentation id, ideal id, vertex count,
# arrows as [source, target, name] (1-based), relations as lists of
# [coefficient, arrow index path] terms (1-based).
Spec := function(family, case, p, presid, idealid, nv, arrows, rels)
  return rec(family := family, case := case, p := p, presid := presid,
             idealid := idealid, nv := nv, arrows := arrows, rels := rels);
end;

BuildAlgebra := function(spec)
  local Q, kQ, arrs, elems, r, t, e;
  Q := Quiver(spec.nv, spec.arrows);
  kQ := PathAlgebra(GF(spec.p), Q);
  if Length(spec.rels) = 0 then
    return kQ;
  fi;
  arrs := List(ArrowsOfQuiver(Q), x -> x * One(kQ));
  elems := [];
  for r in spec.rels do
    e := Zero(kQ);
    for t in r do
      e := e + t[1] * Product(List(t[2], i -> arrs[i]));
    od;
    Add(elems, e);
  od;
  return kQ / elems;
end;

FixtureRecord := function(spec)
  local A, simples, projs, injs, i, j, ext, row;
  A := BuildAlgebra(spec);
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
  return rec(spec := spec,
             dim := Dimension(A),
             cartan := List(projs, DimensionVector),
             injectives := List(injs, DimensionVector),
             projdim := List(simples, S -> BoundedJson(
                 ProjDimensionOfModule(S, PROJDIM_BOUND), PROJDIM_BOUND)),
             injdim := List(simples, S -> BoundedJson(
                 InjDimensionOfModule(S, INJDIM_BOUND), INJDIM_BOUND)),
             tau := List(simples, TauJson),
             tau_injectives := List(injs, TauJson),
             decomposition := DecompositionPairs(projs),
             ext := ext);
end;

JsonIntList := function(l)
  return Concatenation("[", JoinStringsWithSeparator(List(l, String), ", "), "]");
end;

JsonIntMatrix := function(m)
  return Concatenation("[", JoinStringsWithSeparator(List(m, JsonIntList), ", "), "]");
end;

JsonFragmentList := function(l)
  return Concatenation("[", JoinStringsWithSeparator(l, ", "), "]");
end;

JsonTerm := function(t)
  return Concatenation("{\"coeff\": ", String(t[1]), ", \"path\": ",
      JsonIntList(List(t[2], i -> i - 1)), "}");
end;

JsonRelation := function(r)
  return Concatenation("{\"terms\": ", JsonFragmentList(List(r, JsonTerm)), "}");
end;

JsonArrow := function(a)
  return Concatenation("{\"name\": \"", a[3], "\", \"source\": ",
      String(a[1] - 1), ", \"target\": ", String(a[2] - 1), "}");
end;

JsonSummand := function(pr)
  return Concatenation("{\"dimvec\": ", JsonIntList(pr[1]),
      ", \"multiplicity\": ", String(pr[2]), "}");
end;

EmitFixture := function(out, fx, last)
  local spec, j, rowcomma, comma;
  spec := fx.spec;
  AppendTo(out, "    {\n");
  AppendTo(out, "      \"family\": \"", spec.family, "\",\n");
  AppendTo(out, "      \"case\": \"", spec.case, "\",\n");
  AppendTo(out, "      \"field\": ", String(spec.p), ",\n");
  AppendTo(out, "      \"presentation_id\": \"", spec.presid, "\",\n");
  AppendTo(out, "      \"ideal_id\": \"", spec.idealid, "\",\n");
  AppendTo(out, "      \"order\": \"", ORDER_ID, "\",\n");
  AppendTo(out, "      \"quiver\": {\n");
  AppendTo(out, "        \"num_vertices\": ", String(spec.nv), ",\n");
  AppendTo(out, "        \"arrows\": [\n");
  for j in [1 .. Length(spec.arrows)] do
    if j < Length(spec.arrows) then rowcomma := ","; else rowcomma := ""; fi;
    AppendTo(out, "          ", JsonArrow(spec.arrows[j]), rowcomma, "\n");
  od;
  AppendTo(out, "        ]\n");
  AppendTo(out, "      },\n");
  if Length(spec.rels) = 0 then
    AppendTo(out, "      \"relations\": [],\n");
  else
    AppendTo(out, "      \"relations\": [\n");
    for j in [1 .. Length(spec.rels)] do
      if j < Length(spec.rels) then rowcomma := ","; else rowcomma := ""; fi;
      AppendTo(out, "        ", JsonRelation(spec.rels[j]), rowcomma, "\n");
    od;
    AppendTo(out, "      ],\n");
  fi;
  AppendTo(out, "      \"dim\": ", String(fx.dim), ",\n");
  AppendTo(out, "      \"cartan\": ", JsonIntMatrix(fx.cartan), ",\n");
  AppendTo(out, "      \"injectives\": ", JsonIntMatrix(fx.injectives), ",\n");
  AppendTo(out, "      \"projdim\": ", JsonFragmentList(fx.projdim), ",\n");
  AppendTo(out, "      \"injdim\": ", JsonFragmentList(fx.injdim), ",\n");
  AppendTo(out, "      \"tau\": ", JsonFragmentList(fx.tau), ",\n");
  AppendTo(out, "      \"tau_injectives\": ", JsonFragmentList(fx.tau_injectives), ",\n");
  AppendTo(out, "      \"decomposition\": {\"module\": \"radicals-of-projectives\", \"summands\": ",
      JsonFragmentList(List(fx.decomposition, JsonSummand)), "},\n");
  AppendTo(out, "      \"ext\": [\n");
  for j in [1 .. Length(fx.ext)] do
    if j < Length(fx.ext) then rowcomma := ","; else rowcomma := ""; fi;
    AppendTo(out, "        ", JsonIntMatrix(fx.ext[j]), rowcomma, "\n");
  od;
  AppendTo(out, "      ]\n");
  if last then comma := ""; else comma := ","; fi;
  AppendTo(out, "    }", comma, "\n");
end;

EmitJson := function(fixtures)
  local out, i;
  out := OutputTextFile(OUT, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, "{\n");
  AppendTo(out, "  \"schema\": \"auslander-qpa-oracle-v5\",\n");
  AppendTo(out, "  \"convention\": \"right\",\n");
  AppendTo(out, "  \"max_ext_degree\": ", String(MAX_EXT), ",\n");
  AppendTo(out, "  \"projdim_bound\": ", String(PROJDIM_BOUND), ",\n");
  AppendTo(out, "  \"injdim_bound\": ", String(INJDIM_BOUND), ",\n");
  AppendTo(out, "  \"provenance\": {\n");
  AppendTo(out, "    \"gap_version\": \"", GAPInfo.Version, "\",\n");
  AppendTo(out, "    \"qpa_version\": \"", InstalledPackageVersion("qpa"), "\",\n");
  AppendTo(out, "    \"command\": \"gap -q -T generate_fixtures.g\"\n");
  AppendTo(out, "  },\n");
  AppendTo(out, "  \"fixtures\": [\n");
  for i in [1 .. Length(fixtures)] do
    EmitFixture(out, fixtures[i], i = Length(fixtures));
  od;
  AppendTo(out, "  ]\n");
  AppendTo(out, "}\n");
  CloseStream(out);
end;

Specs := [];

Add(Specs, Spec("linear-an-2", "f5", 5, "linear-an-2", "linear-an-2",
    2, [[1, 2, "a1"]], []));

Add(Specs, Spec("linear-an-3", "f5", 5, "linear-an-3", "linear-an-3",
    3, [[1, 2, "a1"], [2, 3, "a2"]], []));

Add(Specs, Spec("d4-star", "f5", 5, "d4-star", "d4-star",
    4, [[1, 4, "a1"], [2, 4, "a2"], [3, 4, "a3"]], []));

Add(Specs, Spec("dual-numbers", "f5", 5, "dual-numbers", "dual-numbers",
    1, [[1, 1, "x"]], [[[1, [1, 1]]]]));

Add(Specs, Spec("truncated-poly-3", "f5", 5, "truncated-poly-3", "truncated-poly-3",
    1, [[1, 1, "x"]], [[[1, [1, 1, 1]]]]));

Add(Specs, Spec("a3-mod-ab", "f5", 5, "a3-mod-ab", "a3-mod-ab",
    3, [[1, 2, "a1"], [2, 3, "a2"]], [[[1, [1, 2]]]]));

Add(Specs, Spec("kronecker-2", "f5", 5, "kronecker-2", "kronecker-2",
    2, [[1, 2, "a1"], [1, 2, "a2"]], []));

Add(Specs, Spec("radical-square-zero-cycle-3", "f5", 5,
    "radical-square-zero-cycle-3", "radical-square-zero-cycle-3",
    3, [[1, 2, "a1"], [2, 3, "a2"], [3, 1, "a3"]],
    [[[1, [1, 2]]], [[1, [2, 3]]], [[1, [3, 1]]]]));

# The same presentation as linear-an-3; a separate fixture because a different
# Rust constructor builds it. The shared ids record the identity.
Add(Specs, Spec("linear-nakayama-3-2-1", "f5", 5, "linear-an-3", "linear-an-3",
    3, [[1, 2, "a1"], [2, 3, "a2"]], []));

# The same presentation as a3-mod-ab, from the Nakayama constructor.
Add(Specs, Spec("linear-nakayama-2-2-1", "f5", 5, "a3-mod-ab", "a3-mod-ab",
    3, [[1, 2, "a1"], [2, 3, "a2"]], [[[1, [1, 2]]]]));

Add(Specs, Spec("cyclic-nakayama-3-3-3", "f5", 5,
    "cyclic-nakayama-3-3-3", "cyclic-nakayama-3-3-3",
    3, [[1, 2, "a1"], [2, 3, "a2"], [3, 1, "a3"]],
    [[[1, [1, 2, 3]]], [[1, [2, 3, 1]]], [[1, [3, 1, 2]]]]));

Add(Specs, Spec("gentle-tree", "f5", 5, "gentle-tree", "gentle-tree",
    4, [[1, 2, "a1"], [2, 3, "a2"], [2, 4, "a3"]], [[[1, [1, 2]]]]));

SquareArrows := [[1, 2, "a"], [2, 4, "b"], [1, 3, "c"], [3, 4, "d"]];

# Commutative square: relation ab - cd.
Add(Specs, Spec("commutative-square", "f2", 2,
    "commutative-square", "commutative-square",
    4, SquareArrows, [[[1, [1, 2]], [-1, [3, 4]]]]));
Add(Specs, Spec("commutative-square", "f5", 5,
    "commutative-square", "commutative-square",
    4, SquareArrows, [[[1, [1, 2]], [-1, [3, 4]]]]));

# Preprojective algebra of A3 on the double quiver, relations a abar,
# abar a - b bbar, bbar b.
PreprojArrows := [[1, 2, "a"], [2, 3, "b"], [2, 1, "abar"], [3, 2, "bbar"]];
PreprojRels := [[[1, [1, 3]]], [[1, [3, 1]], [-1, [2, 4]]], [[1, [4, 2]]]];
Add(Specs, Spec("preprojective-a3", "f2", 2,
    "preprojective-a3", "preprojective-a3", 3, PreprojArrows, PreprojRels));
Add(Specs, Spec("preprojective-a3", "f3", 3,
    "preprojective-a3", "preprojective-a3", 3, PreprojArrows, PreprojRels));

# Self-overlap: loops x, y with xx - yy, xy, yx. The leading word yy
# self-overlaps (yy.y = y.yy), and the overlap of yy with yx makes completion
# add xxx to the basis.
Add(Specs, Spec("self-overlap", "f3", 3, "self-overlap", "self-overlap",
    1, [[1, 1, "x"], [1, 1, "y"]],
    [[[1, [1, 1]], [-1, [2, 2]]], [[1, [1, 2]]], [[1, [2, 1]]]]));

# Inclusion ambiguity: the input leading word xyx properly contains the input
# leading word yx; completion reduces xyx - xx to xx.
Add(Specs, Spec("inclusion-ambiguity", "f2", 2,
    "inclusion-ambiguity", "inclusion-ambiguity",
    1, [[1, 1, "x"], [1, 1, "y"]],
    [[[1, [2, 1]]], [[1, [1, 2, 1]], [-1, [1, 1]]], [[1, [2, 2, 2]]]]));

# Inhomogeneous: relation ab - cde mixes path lengths 2 and 3.
Add(Specs, Spec("inhomogeneous", "f5", 5, "inhomogeneous", "inhomogeneous",
    5, [[1, 2, "a"], [2, 5, "b"], [1, 3, "c"], [3, 4, "d"], [4, 5, "e"]],
    [[[1, [1, 2]], [-1, [3, 4, 5]]]]));

# The commutative-square ideal with a redundant second generator (a scalar
# multiple, the only proper redundancy this ideal admits).
Add(Specs, Spec("redundant-presentation", "f5", 5,
    "commutative-square-redundant", "commutative-square",
    4, SquareArrows,
    [[[1, [1, 2]], [-1, [3, 4]]], [[2, [1, 2]], [-2, [3, 4]]]]));

# The commutative-square relation with its terms listed in the other order.
# One generator leaves nothing else to permute.
Add(Specs, Spec("permuted-presentation", "f5", 5,
    "commutative-square-permuted", "commutative-square",
    4, SquareArrows, [[[-1, [3, 4]], [1, [1, 2]]]]));

# Characteristic-sensitive: relation ab - 2cd on the square. Over F_2 the
# second term vanishes and the ideal degenerates to (ab).
Add(Specs, Spec("characteristic-sensitive", "f2", 2,
    "characteristic-sensitive", "characteristic-sensitive",
    4, SquareArrows, [[[1, [1, 2]], [-2, [3, 4]]]]));
Add(Specs, Spec("characteristic-sensitive", "f3", 3,
    "characteristic-sensitive", "characteristic-sensitive",
    4, SquareArrows, [[[1, [1, 2]], [-2, [3, 4]]]]));

EmitJson(List(Specs, FixtureRecord));
Print("wrote ", OUT, " with ", Length(Specs), " fixtures\n");
QUIT;
