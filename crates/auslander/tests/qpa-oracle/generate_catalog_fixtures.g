# Generates the independent QPA catalog fixture for the gentle-tree domain.
#
# The script writes catalog_qpa_generated.json in its working directory. It
# enumerates finite-field indecomposables with QPA, then records pair Hom and
# Ext dimensions through degree 3. The last line is the completion sentinel.

if LoadPackage("qpa") <> true then
  Error("QPA package failed to load");
fi;

OUT := "catalog_qpa_generated.json";
SENTINEL := "qpa-catalog-oracle-generator-ok";
MAX_LENGTH := 3;
MAX_CHECK_LENGTH := 4;
MAX_EXT := 3;

JsonInt := function(x)
  return String(IntFFE(x));
end;

JsonIntList := function(l)
  return Concatenation("[", JoinStringsWithSeparator(List(l, String), ", "), "]");
end;

JsonFieldList := function(l)
  return Concatenation("[", JoinStringsWithSeparator(List(l, JsonInt), ", "), "]");
end;

JsonFieldMatrix := function(m)
  return Concatenation("[", JoinStringsWithSeparator(List(m, JsonFieldList), ", "), "]");
end;

JsonMaps := function(m)
  return Concatenation("[", JoinStringsWithSeparator(List(
    MatricesOfPathAlgebraModule(m), x -> JsonFieldMatrix(x)), ", "), "]");
end;

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

JsonModules := function(ms)
  return Concatenation("[",
    JoinStringsWithSeparator(List(ms, m -> Concatenation(
      "{\"dimvec\": ", JsonIntList(DimensionVector(m)),
      ", \"maps\": ", JsonMaps(m), "}")), ", "), "]");
end;

JsonPairMatrix := function(ms, f)
  return Concatenation("[", JoinStringsWithSeparator(List(ms,
    x -> JsonIntList(List(ms, y -> f(x, y)))), ", "), "]");
end;

JsonExt := function(ms)
  return Concatenation("[", JoinStringsWithSeparator(List([0 .. MAX_EXT], k ->
    JsonPairMatrix(ms, function(x, y) return ExtDimension(x, y, k); end)), ", "), "]");
end;

MergedDimensionVectors := function(ms)
  local d, i, row, found;
  d := [];
  for i in [1 .. Length(ms)] do
    row := DimensionVector(ms[i]);
    found := Position(List(d, x -> x[1]), row);
    if found = fail then
      Add(d, [ShallowCopy(row), 1]);
    else
      d[found][2] := d[found][2] + 1;
    fi;
  od;
  Sort(d);
  return d;
end;

JsonSummands := function(ms)
  return Concatenation("[", JoinStringsWithSeparator(List(
    MergedDimensionVectors(ms), x -> Concatenation(
      "{\"dimvec\": ", JsonIntList(x[1]), ", \"multiplicity\": ",
      String(x[2]), "}")), ", "), "]");
end;

# QPA raises on a projective with zero radical or an injective equal to its
# socle. These cases have no incoming or outgoing irreducible maps.
IrreducibleMaps := function(m, incoming)
  if incoming and IsProjectiveModule(m) and
     Dimension(RadicalOfModule(m)) = 0 then
    return [];
  fi;
  if not incoming and IsInjectiveModule(m) and
     Dimension(SocleOfModule(m)) = Dimension(m) then
    return [];
  fi;
  if incoming then
    return IrreducibleMorphismsEndingIn(m);
  fi;
  return IrreducibleMorphismsStartingIn(m);
end;

IrreducibleEndpoints := function(m, incoming)
  local endpoints, f, maps;
  maps := IrreducibleMaps(m, incoming);
  endpoints := [];
  for f in maps do
    if incoming then
      Add(endpoints, DimensionVector(Source(f)));
    else
      Add(endpoints, DimensionVector(Range(f)));
    fi;
  od;
  Sort(endpoints);
  return endpoints;
end;

JsonIrreducibles := function(ms, incoming)
  local records, i;
  records := [];
  for i in [1 .. Length(ms)] do
    Add(records, IrreducibleEndpoints(ms[i], incoming));
  od;
  return Concatenation("[", JoinStringsWithSeparator(List(records,
    JsonIntList), ", "), "]");
end;

JsonAr := function(ms)
  local records, i, ass, middle, tau, decomposition;
  records := [];
  for i in [1 .. Length(ms)] do
    ass := AlmostSplitSequence(ms[i], "r");
    if ass = fail then
      Add(records, "{\"projective\": true}");
    else
      middle := Range(ass[1]);
      tau := DimensionVector(Source(ass[1]));
      decomposition := DecomposeModuleWithMultiplicities(middle);
      Add(records, Concatenation(
        "{\"projective\": false, \"tau\": ", JsonIntList(tau),
        ", \"middle_dimvec\": ", JsonIntList(DimensionVector(middle)),
        ", \"middle\": ", JsonSummands(
          decomposition[1]),
        ", \"middle_summands\": ",
        String(Sum(decomposition[2])), "}"));
    fi;
  od;
  return Concatenation("[", JoinStringsWithSeparator(records, ", "), "]");
end;

# QPA's StringModule helpers require every source leaf to have two outgoing
# arrows. Add killed length-two branches, enumerate with the real transition
# functions, and keep words using the three fixture arrows only. This gives a
# string label without using the library's catalog.
AugmentedAlgebra := function(p)
  local Q, kQ, a, rel;
  Q := Quiver(8, [[1, 2, "a"], [2, 3, "b"], [4, 3, "c"],
                  [1, 5, "d"], [5, 6, "e"], [4, 7, "f"], [7, 8, "g"]]);
  kQ := PathAlgebra(GF(p), Q);
  a := List(ArrowsOfQuiver(Q), x -> x * One(kQ));
  rel := [a[1] * a[2], a[4] * a[5], a[6] * a[7]];
  return kQ / rel;
end;

NormalizeString := function(value)
  local out, ch;
  if IsString(value) then
    return value;
  fi;
  out := "";
  for ch in value do
    if IsChar(ch) then
      Add(out, ch);
    else
      Add(out, String(ch)[1]);
    fi;
  od;
  return out;
end;

InverseString := function(s)
  local out, i, ch;
  if s[1] = '(' then
    if s[Length(s) - 2] = '-' then
      return Concatenation("(", String(SIntChar(s[2]) - SIntChar('0')), ",1)");
    fi;
    return Concatenation("(", String(SIntChar(s[2]) - SIntChar('0')), ",-1)");
  fi;
  out := [];
  for i in [Length(s), Length(s) - 1 .. 1] do
    ch := s[i];
    if SIntChar(ch) >= SIntChar('a') and SIntChar(ch) <= SIntChar('z') then
      Add(out, CharInt(SIntChar(ch) - 32));
    else
      Add(out, CharInt(SIntChar(ch) + 32));
    fi;
  od;
  return Concatenation(out, "");
end;

CanonicalString := function(s)
  local inverse;
  s := NormalizeString(s);
  inverse := InverseString(s);
  if String(inverse) < String(s) then
    return inverse;
  fi;
  return s;
end;

StringSeeds := function()
  local seeds, i;
  seeds := [];
  for i in [1 .. 8] do
    Add(seeds, Concatenation("(", String(i), ",1)"));
    Add(seeds, Concatenation("(", String(i), ",-1)"));
  od;
  return seeds;
end;

StringExtension := function(A, s, se, extender)
  local w;
  w := extender(A, ShallowCopy(s), se[1], se[2]);
  if w = "Cannot Perform The Operation" then
    return w;
  fi;
  w := NormalizeString(w);
  if not IsString(w) then
    Error("normalized string has wrong type");
  fi;
  return w;
end;

ReachableStrings := function(A, se)
  local extenders, next, queue, s, seen, w;
  extenders := [QPAStringDirectLeft, QPAStringInverseLeft,
                QPAStringDirectRight, QPAStringInverseRight];
  seen := [];
  queue := StringSeeds();
  while Length(queue) > 0 do
    s := queue[1];
    Remove(queue, 1);
    if not s in seen then
      Add(seen, s);
      for next in extenders do
        w := StringExtension(A, s, se, next);
        if w <> "Cannot Perform The Operation" and Length(w) <= 12 then
          if not w in seen and not w in queue then Add(queue, w); fi;
        fi;
      od;
    fi;
  od;
  return seen;
end;

StringIsFixtureLabel := function(s)
  return ForAll(List([1 .. Length(s)], i -> s[i]),
    x -> x in "abcABC() ,-1234567890") and
    (not s[1] = '(' or s[2] in "1234");
end;

StringLabels := function(p)
  local A, labels, reachable, s, se;
  A := AugmentedAlgebra(p);
  se := QPAStringSigmaEps(A);
  reachable := ReachableStrings(A, se);
  labels := Filtered(reachable, StringIsFixtureLabel);
  labels := Set(List(labels, CanonicalString));
  Sort(labels);
  return labels;
end;

Fixture := function(p)
  local Q, kQ, a, A, all, check, expected, labels, i;
  Q := Quiver(4, [[1, 2, "a"], [2, 3, "b"], [4, 3, "c"]]);
  kQ := PathAlgebra(GF(p), Q);
  a := List(ArrowsOfQuiver(Q), x -> x * One(kQ));
  A := kQ / [a[1] * a[2]];
  all := AllIndecModulesOfLengthAtMost(A, MAX_LENGTH);
  check := AllIndecModulesOfLengthAtMost(A, MAX_CHECK_LENGTH);
  if Length(all) <> Length(check) then
    Error("the QPA indecomposable count did not stabilize at length 3");
  fi;
  Sort(all, function(x, y) return DimensionVector(x) < DimensionVector(y); end);
  labels := StringLabels(p);
  expected := [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0],
               [0, 0, 0, 1], [1, 1, 0, 0], [0, 1, 1, 0],
               [0, 0, 1, 1], [0, 1, 1, 1]];
  if Set(List(all, DimensionVector)) <> Set(expected) then
    Error("QPA indecomposable dimensions changed");
  fi;
  if Length(labels) <> Length(all) then
    Error("QPA string enumeration did not match the finite module count");
  fi;
  return rec(field := p, algebra_dim := Dimension(A), count := Length(all),
             max_length := MAX_LENGTH, checked_length := MAX_CHECK_LENGTH,
    strings := labels, modules := all,
             hom := JsonPairMatrix(all, function(x, y)
               return Length(HomOverAlgebra(x, y)); end),
             ext := JsonExt(all), ar := JsonAr(all),
             irr_in := JsonIrreducibles(all, true),
             irr_out := JsonIrreducibles(all, false));
end;

JsonFixture := function(fx)
  return Concatenation(
    "    {\"field\": ", String(fx.field), ", \"algebra_dim\": ",
    String(fx.algebra_dim), ", \"count\": ", String(fx.count),
    ", \"max_length\": ", String(fx.max_length),
    ", \"checked_length\": ", String(fx.checked_length),
    ", \"strings\": [", JoinStringsWithSeparator(List(fx.strings,
      s -> Concatenation("\"", s, "\"")), ", "), "]",
    ", \"modules\": ", JsonModules(fx.modules),
    ", \"hom\": ", fx.hom, ", \"ext\": ", fx.ext,
    ", \"ar\": ", fx.ar, ", \"irr_in\": ", fx.irr_in,
    ", \"irr_out\": ", fx.irr_out, "}");
end;

fixtures := List([2, 5], Fixture);
buf := "{\n";
Append(buf, "  \"schema\": \"auslander-catalog-qpa-v1\",\n");
Append(buf, "  \"convention\": \"right\",\n");
Append(buf, Concatenation("  \"max_ext_degree\": ", String(MAX_EXT), ",\n"));
Append(buf, "  \"quiver\": {\"num_vertices\": 4, \"arrows\": ");
Append(buf, "[[0, 1, \"a\"], [1, 2, \"b\"], [3, 2, \"c\"]]},\n");
Append(buf, "  \"relations\": [[[1, [0, 1]]]],\n");
Append(buf, "  \"fixtures\": [\n");
for i in [1 .. Length(fixtures)] do
  Append(buf, JsonFixture(fixtures[i]));
  if i < Length(fixtures) then Append(buf, ","); fi;
  Append(buf, "\n");
od;
Append(buf, "  ],\n");
Append(buf, Concatenation("  \"provenance\": {\"gap_version\": \"", GAPInfo.Version,
       "\", \"qpa_version\": \"", InstalledPackageVersion("qpa"),
       "\", \"command\": \"gap -q -T -m 1g generate_catalog_fixtures.g\"}\n"));
Append(buf, "}\n");
FileString(OUT, buf);
Print("wrote ", OUT, " with ", Length(fixtures), " fixtures\n");
Print(SENTINEL, "\n");
QUIT;
