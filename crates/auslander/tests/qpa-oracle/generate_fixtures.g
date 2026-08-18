# Builds every auslander fixture algebra in QPA and writes
# qpa_generated.json
# with schema auslander-qpa-oracle-v7. Each fixture carries its own prime field
# and its full presentation: the quiver, and relations as integer combinations
# of paths given by arrow indices. The results per fixture: algebra dimension,
# dimension vectors of the indecomposable projectives (the Cartan rows) and
# injectives, projective and injective dimensions of the simples (typed, bounded
# at 6), tau of the simples and of the indecomposable injectives (typed), the
# decomposition of the direct sum of the nonzero radicals of the indecomposable
# projectives (summand dimension vectors with multiplicities, sorted), and
# dim Ext^k(S_i, S_j) for k = 0..4.
#
# Schema v6 adds the Auslander-Reiten layer on a fixed list of designated
# modules: every simple, then every indecomposable projective, then every
# indecomposable injective, each named by kind and 0-based vertex index. The
# list is built from those three QPA constructors directly, so a module is never
# identified by its dimension vector; on kronecker-2 the dimension vector is not
# an isomorphism invariant. The added results are the almost-split sequence of
# each designated module (typed projective marker or tau, middle term and its
# Krull-Schmidt summands), the irreducible morphisms into and out of it with
# valuations, the Ext algebra of A/rad up to degree 4, the ranks of the Yoneda
# products Ext^1(S_i, S_j) x Ext^1(S_j, S_k) -> Ext^2(S_i, S_k), the stable Hom
# dimensions between all designated modules, the tau-rigid and rigid flags, and
# the tau period bounded at 6 (typed).
#
# Schema v7 is the complete v6 record, unchanged, plus one support tau-tilting
# block per fixture. QPA 1.36 has no support tau-tilting predicate, pair type,
# mutation or enumerator, so every value in that block is built from Hom, tau,
# minimal approximations and TiltingModule. The block leads with a typed closure
# marker from an AR-quiver walk. The pair count, the histogram, the pairs, the
# approximation sample, the one-tilting entries and the exchange graph are
# emitted only when that walk closed: a truncated walk still yields a plausible
# pair count, and an ungated total would be a silent undercount.
#
# Writes into the current working directory; run under GAP with QPA loadable
# (discovery order in README.md):
#
#   gap -q -T -m 1g generate_fixtures.g
#
# gap -q -T with closed stdin exits 0 after an uncaught error, so the exit code
# proves nothing about the run. The output is written in one final statement, so
# a crashed run leaves no file, and the last line of stdout is the sentinel
# qpa-oracle-generator-ok. A harness checks that line and the file, never the
# exit code.
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
TAU_PERIOD_BOUND := 6;
ORDER_ID := "deglex-arrowid-v1";
APPROX_SAMPLE := 12;
SENTINEL := "qpa-oracle-generator-ok";
OUT := "qpa_generated.json";

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

# [dimvec, multiplicity] pairs, sorted by dimension vector lexicographically and
# merged on equal dimension vectors, so QPA's internal order never reaches the
# file. Every list of summands in the output goes through this.
MergedPairs := function(pairs)
  local merged, pr;
  Sort(pairs);
  merged := [];
  for pr in pairs do
    if Length(merged) > 0 and merged[Length(merged)][1] = pr[1] then
      merged[Length(merged)][2] := merged[Length(merged)][2] + pr[2];
    else
      Add(merged, ShallowCopy(pr));
    fi;
  od;
  return merged;
end;

# The designated test module is the direct sum of the nonzero radicals of the
# indecomposable projectives.
DecompositionPairs := function(projs)
  local rads, d, i;
  rads := Filtered(List(projs, RadicalOfModule), M -> Dimension(M) > 0);
  if Length(rads) = 0 then
    return [];
  fi;
  d := DecomposeModuleWithMultiplicities(DirectSumOfQPAModules(rads));
  return MergedPairs(List([1 .. Length(d[1])],
      i -> [ShallowCopy(DimensionVector(d[1][i])), d[2][i]]));
end;

# The fixed list every v6 result field runs over: each simple, each
# indecomposable projective, each indecomposable injective, in vertex order.
# Each entry keeps its kind and its 0-based vertex index, so a module is named
# by construction. A dimension vector never identifies a module here: on
# kronecker-2 two non-isomorphic modules share the dimension vector [1, 1].
DesignatedModules := function(simples, projs, injs)
  local out, i;
  out := [];
  for i in [1 .. Length(simples)] do
    Add(out, rec(kind := "simple", index := i - 1, module := simples[i]));
  od;
  for i in [1 .. Length(projs)] do
    Add(out, rec(kind := "projective", index := i - 1, module := projs[i]));
  od;
  for i in [1 .. Length(injs)] do
    Add(out, rec(kind := "injective", index := i - 1, module := injs[i]));
  od;
  return out;
end;

# AlmostSplitSequence(M, "r") returns fail exactly on the projectives, so the
# typed projective marker comes from QPA's own refusal. ass[1] is the mono
# tau M -> E; its source must be DTr M, which the assertion pins.
ArRecord := function(M)
  local ass, mid, merged, d, i, pr;
  ass := AlmostSplitSequence(M, "r");
  if ass = fail then
    return rec(projective := true);
  fi;
  mid := Range(ass[1]);
  d := DecomposeModuleWithMultiplicities(mid);
  merged := MergedPairs(List([1 .. Length(d[1])],
      i -> [ShallowCopy(DimensionVector(d[1][i])), d[2][i]]));
  if DimensionVector(Source(ass[1])) <> DimensionVector(DTr(M)) then
    Error("AlmostSplitSequence source disagrees with DTr");
  fi;
  return rec(projective := false,
             tau := ShallowCopy(DimensionVector(Source(ass[1]))),
             middle_dimvec := ShallowCopy(DimensionVector(mid)),
             middle := merged,
             num_middle_summands := Sum(merged, pr -> pr[2]));
end;

# IrreducibleMorphismsEndingIn errors on a projective with zero radical, and
# IrreducibleMorphismsStartingIn errors on an injective equal to its socle.
# The guards predict both cases from the module itself. A caught error still
# prints its message, so catching is not an option here.
HasIrrIn := function(M)
  return not (IsProjectiveModule(M) and Dimension(RadicalOfModule(M)) = 0);
end;

HasIrrOut := function(M)
  return not (IsInjectiveModule(M) and Dimension(SocleOfModule(M)) = Dimension(M));
end;

# Each irreducible morphism contributes its endpoint dimension vector; equal
# dimension vectors merge and the merged count is the valuation.
IrrPairs := function(maps, endpoint)
  local f;
  return MergedPairs(List(maps,
      f -> [ShallowCopy(DimensionVector(endpoint(f))), 1]));
end;

IrrRecord := function(M)
  local into, out_of, maps;
  if HasIrrIn(M) then
    maps := IrreducibleMorphismsEndingIn(M);
    into := rec(present := true, total := Length(maps),
                pairs := IrrPairs(maps, Source));
  else
    into := rec(present := false, total := 0, pairs := []);
  fi;
  if HasIrrOut(M) then
    maps := IrreducibleMorphismsStartingIn(M);
    out_of := rec(present := true, total := Length(maps),
                  pairs := IrrPairs(maps, Range));
  else
    out_of := rec(present := false, total := 0, pairs := []);
  fi;
  return rec(into := into, out_of := out_of);
end;

# The Ext algebra of A/rad, the direct sum of all simples. rad End(A/rad) = 0,
# so the minimal generators ExtAlgebraGenerators reports are the genuine
# generators of the Yoneda algebra and dims - min_generators is the rank of the
# multiplication into each degree.
ExtAlgebraRecord := function(simples)
  local r;
  r := ExtAlgebraGenerators(DirectSumOfQPAModules(simples), MAX_EXT);
  return rec(dims := r[1], min_generators := r[2],
             product_rank := r[1] - r[2]);
end;

# Rank of the Yoneda product Ext^1(M, N) x Ext^1(N, L) -> Ext^2(M, L), computed
# the way QPA's own ExtAlgebraGenerators forms products: lift a class through
# the projective cover of N and restrict to the second syzygy. ExtOverAlgebra
# returns the Ext^1 basis in position 2 and the map to coordinates in
# position 3; Ext^2(M, L) is Ext^1(Omega M, L).
YonedaRank11 := function(M, N, L)
  local pM, OM, pOM, pN, e1, e2, e3, K, alpha, beta, lift, om, prods, V, W;
  pM := ProjectiveCover(M);
  OM := Kernel(pM);
  pOM := ProjectiveCover(OM);
  pN := ProjectiveCover(N);
  e1 := ExtOverAlgebra(M, N)[2];
  e2 := ExtOverAlgebra(N, L)[2];
  e3 := ExtOverAlgebra(OM, L);
  if Length(e1) = 0 or Length(e2) = 0 or Length(e3[2]) = 0 then
    return [Length(e1), Length(e2), Length(e3[2]), 0];
  fi;
  K := LeftActingDomain(M);
  prods := [];
  for alpha in e1 do
    lift := LiftingMorphismFromProjective(pN, pOM * alpha);
    om := MorphismOnKernel(pOM, pN, lift, alpha);
    for beta in e2 do
      Add(prods, e3[3](om * beta));
    od;
  od;
  prods := Filtered(prods, x -> x <> Zero(x));
  if Length(prods) = 0 then
    return [Length(e1), Length(e2), Length(e3[2]), 0];
  fi;
  W := FullRowSpace(K, Length(e3[2]));
  V := Subspace(W, prods);
  return [Length(e1), Length(e2), Length(e3[2]), Dimension(V)];
end;

# Every ordered triple of simples whose two Ext^1 factors are both nonzero.
# ext[i][j][2] is dim Ext^1(S_i, S_j): the stored degrees run 0 .. MAX_EXT.
YonedaTriples := function(simples, ext)
  local out, i, j, k, r;
  out := [];
  for i in [1 .. Length(simples)] do
    for j in [1 .. Length(simples)] do
      if ext[i][j][2] > 0 then
        for k in [1 .. Length(simples)] do
          if ext[j][k][2] > 0 then
            r := YonedaRank11(simples[i], simples[j], simples[k]);
            Add(out, rec(i := i - 1, j := j - 1, k := k - 1,
                         dim_ext1_ij := r[1], dim_ext1_jk := r[2],
                         dim_ext2_ik := r[3], yoneda_map_rank := r[4]));
          fi;
        od;
      fi;
    od;
  od;
  return out;
end;

StableHomDim := function(M, N)
  return Length(HomOverAlgebra(M, N))
      - Length(HomFactoringThroughProjOverAlgebra(M, N));
end;

# IsTauPeriodic iterates DTr up to the bound and compares each step with M, so
# its cost follows the tau orbit. On inclusion-ambiguity over F_2 the orbit of
# the simple module grows 1, 8, 26, 86, 284, and the fifth step alone costs over
# a minute; the bound there is 3. Every other fixture keeps TAU_PERIOD_BOUND.
# The bound reached is written into the result, so a value never claims more
# than it checked.
TauPeriodBound := function(spec)
  if spec.family = "inclusion-ambiguity" then
    return 3;
  fi;
  return TAU_PERIOD_BOUND;
end;

# IsTauPeriodic returns the period, or false when no period up to the bound
# exists; both outcomes are written as typed records.
TauPeriodJson := function(M, bound)
  local i;
  i := IsTauPeriodic(M, bound);
  if i = false then
    return Concatenation("{\"none_up_to\": ", String(bound), "}");
  fi;
  return Concatenation("{\"period\": ", String(i), "}");
end;

# The independent enumeration route of schema v7. Seed with the indecomposable
# projectives and injectives, then close under the irreducible morphisms in both
# directions, which walks the arrows of the AR quiver. A finite closure
# certifies the list: a finite AR component over a connected algebra forces
# representation-finiteness, so the component is everything. Returns fail when
# the list passes cap.
#
# Never close under AlmostSplitSequence. A projective-injective has no almost
# split sequence in either direction, and a walk that used it returned 1
# indecomposable instead of 3 on k[x]/(x^3).
#
# IsomorphicModules is the only sound identity test here. On kronecker-2 over
# F_p the dimension vector [1, 1] belongs to p + 1 non-isomorphic modules, and
# even on the representation-finite cyclic-nakayama-3-3-3 the three
# indecomposable projectives are non-isomorphic with the same dimension vector.
# The guards HasIrrIn and HasIrrOut are the ones the v6 fields already use.
KnitIndecomposables := function(A, cap)
  local L, queue, M, nb, X, new;
  L := ShallowCopy(IndecProjectiveModules(A));
  Append(L, IndecInjectiveModules(A));
  new := [];
  for M in L do
    if ForAll(new, N -> not IsomorphicModules(N, M)) then
      Add(new, M);
    fi;
  od;
  L := new;
  queue := ShallowCopy(L);
  while Length(queue) > 0 do
    M := Remove(queue, 1);
    nb := [];
    if HasIrrIn(M) then
      Append(nb, List(IrreducibleMorphismsEndingIn(M), Source));
    fi;
    if HasIrrOut(M) then
      Append(nb, List(IrreducibleMorphismsStartingIn(M), Range));
    fi;
    for X in nb do
      if Dimension(X) > 0 and ForAll(L, N -> not IsomorphicModules(N, X)) then
        Add(L, X);
        Add(queue, X);
        if Length(L) > cap then
          return fail;
        fi;
      fi;
    od;
  od;
  return L;
end;

# The cap is a budget, not a claim, and the not-closed marker records it. Every
# fixture whose walk closes closes at 17 indecomposables or fewer (inhomogeneous
# is the largest), so 40 never binds. Three families never close, and the cost
# of failing grows steeply: at cap 12 the walk fails after 2.0 s on kronecker-2,
# 40.4 s on self-overlap and 4.8 s on inclusion-ambiguity, while at cap 16
# self-overlap alone costs 380 s.
WalkCap := function(spec)
  if spec.family in ["kronecker-2", "self-overlap", "inclusion-ambiguity"] then
    return 12;
  fi;
  return 40;
end;

# The zero module is the module part of the pair (0, A). DecomposeModule and
# NumberOfNonIsoDirSummands both error on it, so summand counts come from the
# chosen index set and never from decomposing a module.
SumOrZero := function(A, L)
  if Length(L) = 0 then
    return ZeroModule(A);
  fi;
  return DirectSumOfQPAModules(L);
end;

# tbl[i][j] = dim Hom(L_i, tau L_j). tau is additive, so a direct sum of the
# L_i over an index set is tau-rigid exactly when every entry over that set
# vanishes.
PairwiseTauTable := function(L)
  local taus, i, j, t;
  taus := List(L, DTr);
  t := [];
  for i in [1 .. Length(L)] do
    Add(t, List([1 .. Length(L)], j -> Length(HomOverAlgebra(L[i], taus[j]))));
  od;
  return t;
end;

# Every basic support tau-tilting pair (M, P), by definition: M a tau-rigid sum
# of |M| = m of the indecomposables, P a sum of n - m indecomposable
# projectives, Hom(P, M) = 0. The projective part is chosen vertex by vertex
# from the vanishing of Hom(P_i, M), which QPA computes; the assertion pins that
# vanishing set against the zero support of M, so the redundancy is checked and
# not assumed. Summand dimension vectors keep their repetitions: a repeated
# entry is a second non-isomorphic summand, not a multiplicity.
EnumeratePairs := function(A, indecs)
  local n, projs, tbl, out, m, s, M, zero, dv, dimvecs, T;
  n := Length(SimpleModules(A));
  projs := IndecProjectiveModules(A);
  tbl := PairwiseTauTable(indecs);
  out := [];
  for m in [0 .. n] do
    for s in Combinations([1 .. Length(indecs)], m) do
      if ForAll(s, i -> ForAll(s, j -> tbl[i][j] = 0)) then
        M := SumOrZero(A, indecs{s});
        zero := Filtered([1 .. n], i -> Length(HomOverAlgebra(projs[i], M)) = 0);
        dv := DimensionVector(M);
        if zero <> Filtered([1 .. n], i -> dv[i] = 0) then
          Error("Hom(P_i, M) vanishing disagrees with the zero support of M");
        fi;
        dimvecs := List(indecs{s}, DimensionVector);
        Sort(dimvecs);
        for T in Combinations(zero, n - m) do
          Add(out, rec(idx := s, m := m, dimvecs := dimvecs, proj := T - 1));
        od;
      fi;
    od;
  od;
  return out;
end;

# The cross-check route. AllIndecModulesOfLengthAtMost errors when a length
# class below the bound is empty, so the call is caught and its outcome typed.
SameIsoSets := function(L1, L2)
  if Length(L1) <> Length(L2) then
    return false;
  fi;
  return ForAll(L1, M -> ForAny(L2, N -> IsomorphicModules(M, N)))
     and ForAll(L2, M -> ForAny(L1, N -> IsomorphicModules(M, N)));
end;

# LowestKnownDegree and HighestKnownDegree return minus infinity and infinity on
# a FiniteComplex, and the range then fails. LowerBound and UpperBound are the
# working accessors, and IsZeroComplex guards the empty case.
ComplexTerms := function(C)
  local lo, hi, i;
  if IsZeroComplex(C) then
    return [];
  fi;
  lo := LowerBound(C);
  hi := UpperBound(C);
  return List([lo .. hi], i -> DimensionVector(ObjectOfComplex(C, i)));
end;

# Approximation invariants at (pair, module summand) slots, never a mutated
# pair: QPA realizes the exchange only when the approximation is injective with
# a nonzero cokernel, which on d4-star holds for 50 of 150 slots, and the other
# branch gives the wrong partner half the time.
#
# The sample is deterministic. Slots are sorted by summand count, then by the
# pair's dimension vectors, its summand dimension vector and its projective
# support, then by discovery order, and want slots are taken at even stride
# through that order.
ApproximationSample := function(A, indecs, pairs, want)
  local slots, keys, j, r, N, K, i, sl, X, rest, f, out;
  slots := [];
  for j in [1 .. Length(pairs)] do
    for i in pairs[j].idx do
      Add(slots, [j, i]);
    od;
  od;
  N := Length(slots);
  if N = 0 then
    return rec(total := 0, entries := []);
  fi;
  keys := List([1 .. N], j -> [pairs[slots[j][1]].m, pairs[slots[j][1]].dimvecs,
      DimensionVector(indecs[slots[j][2]]), pairs[slots[j][1]].proj, j]);
  Sort(keys);
  K := Minimum(want, N);
  out := [];
  for i in [1 .. K] do
    sl := slots[keys[1 + Int((i - 1) * N / K)][5]];
    r := pairs[sl[1]];
    X := indecs[sl[2]];
    rest := Filtered(r.idx, t -> t <> sl[2]);
    f := MinimalLeftApproximation(X, SumOrZero(A, indecs{rest}));
    Add(out, rec(dimvecs := r.dimvecs, proj := r.proj,
                 summand := DimensionVector(X),
                 source := DimensionVector(Source(f)),
                 target := DimensionVector(Range(f)),
                 rank := Dimension(Source(f)) - Dimension(Kernel(f)),
                 kernel := DimensionVector(Kernel(f)),
                 cokernel := DimensionVector(CoKernel(f))));
  od;
  return rec(total := N, entries := out);
end;

# Classical tilting over the enumerated pairs with n summands. TiltingModule
# returns false, or the projective dimension and one coresolution per
# indecomposable projective. IsTiltingModule is an attribute with no computing
# method and a false answer never sets it, so it is never called here.
OneTiltingEntries := function(A, indecs, pairs, n)
  local out, r, M, t;
  out := [];
  for r in Filtered(pairs, x -> x.m = n) do
    M := SumOrZero(A, indecs{r.idx});
    t := TiltingModule(M, 1);
    if t = false then
      Add(out, rec(dimvecs := r.dimvecs, tilting := false));
    else
      Add(out, rec(dimvecs := r.dimvecs, tilting := true, pd := t[1],
                   coresolutions := List(t[2], ComplexTerms)));
    fi;
  od;
  return out;
end;

# A self-consistency check, not external truth: the graph is computed from the
# enumerated set by intersecting labels, so it repeats what the enumeration
# already said. Two pairs are adjacent when they share n - 1 of their n labels,
# a label being a module summand index or a projective vertex.
ExchangeGraph := function(pairs, n)
  local lab, N, adj, seen, queue, i, j;
  N := Length(pairs);
  lab := List(pairs, r -> Concatenation(List(r.idx, i -> ["m", i]),
                                        List(r.proj, v -> ["p", v])));
  adj := List([1 .. N], i -> Filtered([1 .. N],
      j -> j <> i and Length(Intersection(lab[i], lab[j])) = n - 1));
  seen := [1];
  queue := [1];
  while Length(queue) > 0 do
    i := Remove(queue, 1);
    for j in adj[i] do
      if not j in seen then
        Add(seen, j);
        Add(queue, j);
      fi;
    od;
  od;
  return rec(degrees := List([0 .. n + 1], d -> Number(adj, x -> Length(x) = d)),
             edges := Sum(List(adj, Length)) / 2,
             connected := Length(seen) = N);
end;

# The whole v7 block for one fixture. taurigid is the v6 list over the
# designated modules, passed in so both fields report the same computation.
SttRecord := function(spec, A, taurigid)
  local r, L, n, brute, maxlen;
  r := rec(cap := WalkCap(spec), tau_rigid := taurigid);
  L := KnitIndecomposables(A, r.cap);
  if L = fail then
    r.closed := false;
    return r;
  fi;
  r.closed := true;
  r.count := Length(L);
  n := Length(SimpleModules(A));
  maxlen := Maximum(List(L, Dimension));
  brute := CALL_WITH_CATCH(AllIndecModulesOfLengthAtMost, [A, maxlen]);
  r.brute_length := maxlen;
  r.brute_ok := brute[1];
  if brute[1] then
    r.brute_agrees := SameIsoSets(L, brute[2]);
  fi;
  r.pairs := EnumeratePairs(A, L);
  r.total := Length(r.pairs);
  r.histogram := List([0 .. n], m -> Number(r.pairs, x -> x.m = m));
  r.approximations := ApproximationSample(A, L, r.pairs, APPROX_SAMPLE);
  r.one_tilting := OneTiltingEntries(A, L, r.pairs, n);
  r.graph := ExchangeGraph(r.pairs, n);
  return r;
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
  local A, simples, projs, injs, i, j, ext, row, designated, d, e,
        ar, irr, extalg, yoneda, stable, taurigid, rigid, tauperiod;
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
  designated := DesignatedModules(simples, projs, injs);
  ar := List(designated, d -> ArRecord(d.module));
  irr := List(designated, d -> IrrRecord(d.module));
  extalg := ExtAlgebraRecord(simples);
  yoneda := YonedaTriples(simples, ext);
  stable := List(designated,
      d -> List(designated, e -> StableHomDim(d.module, e.module)));
  taurigid := List(designated, d -> IsTauRigidModule(d.module));
  rigid := List(designated, d -> IsRigidModule(d.module));
  tauperiod := List(designated,
      d -> TauPeriodJson(d.module, TauPeriodBound(spec)));
  return rec(spec := spec,
             designated := designated,
             stt := SttRecord(spec, A, taurigid),
             ar_sequences := ar,
             irreducible_maps := irr,
             ext_algebra := extalg,
             yoneda := yoneda,
             stable_hom := stable,
             tau_rigid := taurigid,
             rigid := rigid,
             tau_period := tauperiod,
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

JsonBool := function(b)
  if b then
    return "true";
  fi;
  return "false";
end;

JsonBoolList := function(l)
  return Concatenation("[", JoinStringsWithSeparator(List(l, JsonBool), ", "), "]");
end;

JsonModuleRef := function(d)
  return Concatenation("{\"kind\": \"", d.kind, "\", \"index\": ",
      String(d.index), "}");
end;

JsonValuation := function(pr)
  return Concatenation("{\"dimvec\": ", JsonIntList(pr[1]),
      ", \"valuation\": ", String(pr[2]), "}");
end;

JsonArEntry := function(d, ar)
  local s;
  s := Concatenation("{\"module\": ", JsonModuleRef(d), ", \"projective\": ",
      JsonBool(ar.projective));
  if ar.projective then
    return Concatenation(s, "}");
  fi;
  return Concatenation(s, ", \"tau\": ", JsonIntList(ar.tau),
      ", \"middle_dimvec\": ", JsonIntList(ar.middle_dimvec),
      ", \"middle\": ", JsonFragmentList(List(ar.middle, JsonSummand)),
      ", \"num_middle_summands\": ", String(ar.num_middle_summands), "}");
end;

JsonIrrSide := function(side, key)
  return Concatenation("{\"present\": ", JsonBool(side.present),
      ", \"total\": ", String(side.total), ", \"", key, "\": ",
      JsonFragmentList(List(side.pairs, JsonValuation)), "}");
end;

JsonIrrEntry := function(d, irr)
  return Concatenation("{\"module\": ", JsonModuleRef(d),
      ", \"into\": ", JsonIrrSide(irr.into, "sources"),
      ", \"out_of\": ", JsonIrrSide(irr.out_of, "targets"), "}");
end;

JsonYoneda := function(y)
  return Concatenation("{\"i\": ", String(y.i), ", \"j\": ", String(y.j),
      ", \"k\": ", String(y.k),
      ", \"dim_ext1_ij\": ", String(y.dim_ext1_ij),
      ", \"dim_ext1_jk\": ", String(y.dim_ext1_jk),
      ", \"dim_ext2_ik\": ", String(y.dim_ext2_ik),
      ", \"yoneda_map_rank\": ", String(y.yoneda_map_rank), "}");
end;

JsonSttPair := function(r)
  return Concatenation("{\"module_dimvecs\": ", JsonIntMatrix(r.dimvecs),
      ", \"projective_support\": ", JsonIntList(r.proj), "}");
end;

JsonApproximation := function(a)
  return Concatenation("{\"module_dimvecs\": ", JsonIntMatrix(a.dimvecs),
      ", \"projective_support\": ", JsonIntList(a.proj),
      ", \"summand_dimvec\": ", JsonIntList(a.summand),
      ", \"source_dimvec\": ", JsonIntList(a.source),
      ", \"target_dimvec\": ", JsonIntList(a.target),
      ", \"rank\": ", String(a.rank),
      ", \"kernel_dimvec\": ", JsonIntList(a.kernel),
      ", \"cokernel_dimvec\": ", JsonIntList(a.cokernel), "}");
end;

JsonOneTilting := function(t)
  local s;
  s := Concatenation("{\"module_dimvecs\": ", JsonIntMatrix(t.dimvecs),
      ", \"tilting\": ", JsonBool(t.tilting));
  if not t.tilting then
    return Concatenation(s, "}");
  fi;
  return Concatenation(s, ", \"projective_dimension\": ", String(t.pd),
      ", \"coresolutions\": ", JsonFragmentList(
          List(t.coresolutions, JsonIntMatrix)), "}");
end;

# QPA's list order is discovery order, so every emitted list is sorted by an
# explicit key first. The key is a value, never an isomorphism class: two
# entries with the same key print the same bytes, so their order is free.
SortedFragments := function(items, keyfun, jsonfun)
  local l;
  l := List(items, x -> [keyfun(x), jsonfun(x)]);
  Sort(l);
  return List(l, x -> x[2]);
end;

JsonBruteAgreement := function(stt)
  if not stt.closed then
    return "{\"available\": false, \"reason\": \"walk-not-closed\"}";
  fi;
  if not stt.brute_ok then
    return Concatenation("{\"available\": false, \"reason\": \"gap-error\", ",
        "\"max_length\": ", String(stt.brute_length), "}");
  fi;
  return Concatenation("{\"available\": true, \"max_length\": ",
      String(stt.brute_length), ", \"agrees\": ",
      JsonBool(stt.brute_agrees), "}");
end;

JsonExchangeGraph := function(g)
  return Concatenation("{\"degree_histogram\": ", JsonIntList(g.degrees),
      ", \"edges\": ", String(g.edges),
      ", \"connected\": ", JsonBool(g.connected), "}");
end;

# One JSON fragment per line, so a diff of two generated files points at the
# entry that changed.
EmitFragmentLines := function(out, name, items)
  local j, rowcomma;
  if Length(items) = 0 then
    AppendTo(out, "      \"", name, "\": [],\n");
    return;
  fi;
  AppendTo(out, "      \"", name, "\": [\n");
  for j in [1 .. Length(items)] do
    if j < Length(items) then rowcomma := ","; else rowcomma := ""; fi;
    AppendTo(out, "        ", items[j], rowcomma, "\n");
  od;
  AppendTo(out, "      ],\n");
end;

EmitSttList := function(out, name, items, comma)
  local j, rowcomma;
  if Length(items) = 0 then
    AppendTo(out, "        \"", name, "\": []", comma, "\n");
    return;
  fi;
  AppendTo(out, "        \"", name, "\": [\n");
  for j in [1 .. Length(items)] do
    if j < Length(items) then rowcomma := ","; else rowcomma := ""; fi;
    AppendTo(out, "          ", items[j], rowcomma, "\n");
  od;
  AppendTo(out, "        ]", comma, "\n");
end;

# The closure marker gates the block: without a closed walk there is no total,
# no histogram, no pair list, no approximation sample, no one-tilting list and
# no graph, only the marker, the cross-check status, the designated tau-rigidity
# flags and the typed refusal.
EmitStt := function(out, stt)
  AppendTo(out, "      \"support_tau_tilting\": {\n");
  if stt.closed then
    AppendTo(out, "        \"indecomposables\": {\"closed\": true, ",
        "\"count\": ", String(stt.count), "},\n");
  else
    AppendTo(out, "        \"indecomposables\": {\"closed\": false, ",
        "\"cap\": ", String(stt.cap), "},\n");
  fi;
  AppendTo(out, "        \"brute_agreement\": ", JsonBruteAgreement(stt), ",\n");
  AppendTo(out, "        \"tau_rigid_designated\": ",
      JsonBoolList(stt.tau_rigid), ",\n");
  if not stt.closed then
    AppendTo(out, "        \"not_computed\": ",
        "{\"reason\": \"walk-not-closed\"}\n");
    AppendTo(out, "      }\n");
    return;
  fi;
  AppendTo(out, "        \"total\": ", String(stt.total), ",\n");
  AppendTo(out, "        \"histogram\": ", JsonIntList(stt.histogram), ",\n");
  EmitSttList(out, "pairs",
      SortedFragments(stt.pairs, r -> [r.m, r.dimvecs, r.proj], JsonSttPair),
      ",");
  AppendTo(out, "        \"approximation_slots\": ",
      String(stt.approximations.total), ",\n");
  EmitSttList(out, "approximations",
      List(stt.approximations.entries, JsonApproximation), ",");
  EmitSttList(out, "one_tilting",
      SortedFragments(stt.one_tilting, t -> t.dimvecs, JsonOneTilting), ",");
  AppendTo(out, "        \"exchange_graph_self_consistency\": ",
      JsonExchangeGraph(stt.graph), "\n");
  AppendTo(out, "      }\n");
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
  AppendTo(out, "      ],\n");
  EmitFragmentLines(out, "designated_modules",
      List(fx.designated, JsonModuleRef));
  EmitFragmentLines(out, "ar_sequences",
      List([1 .. Length(fx.designated)],
          t -> JsonArEntry(fx.designated[t], fx.ar_sequences[t])));
  EmitFragmentLines(out, "irreducible_maps",
      List([1 .. Length(fx.designated)],
          t -> JsonIrrEntry(fx.designated[t], fx.irreducible_maps[t])));
  AppendTo(out, "      \"ext_algebra\": {\"module\": \"sum-of-simples\", ",
      "\"max_degree\": ", String(MAX_EXT),
      ", \"dims\": ", JsonIntList(fx.ext_algebra.dims),
      ", \"min_generators\": ", JsonIntList(fx.ext_algebra.min_generators),
      ", \"product_rank\": ", JsonIntList(fx.ext_algebra.product_rank), "},\n");
  EmitFragmentLines(out, "yoneda_products", List(fx.yoneda, JsonYoneda));
  AppendTo(out, "      \"stable_hom\": ", JsonIntMatrix(fx.stable_hom), ",\n");
  AppendTo(out, "      \"tau_rigid\": ", JsonBoolList(fx.tau_rigid), ",\n");
  AppendTo(out, "      \"rigid\": ", JsonBoolList(fx.rigid), ",\n");
  AppendTo(out, "      \"tau_period\": ", JsonFragmentList(fx.tau_period), ",\n");
  EmitStt(out, fx.stt);
  if last then comma := ""; else comma := ","; fi;
  AppendTo(out, "    }", comma, "\n");
end;

# The file is written by the single FileString call at the end, after every
# value is computed and every byte is formatted, so a run that dies leaves no
# file at all. gap -q -T with closed stdin exits 0 after an uncaught error, so
# the absent file and the missing sentinel are the only failure signals.
EmitJson := function(fixtures)
  local buf, out, i;
  buf := "";
  out := OutputTextString(buf, true);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, "{\n");
  AppendTo(out, "  \"schema\": \"auslander-qpa-oracle-v7\",\n");
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
  FileString(OUT, buf);
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
Print(SENTINEL, "\n");
QUIT;
