# Generates the independent QPA census oracle.
#
# The two domains use the commutative square over GF(2), with arrow order
# (a,b,c,d). QPA builds every relation-valid representation, classifies it by
# IsomorphicModules, and computes self-Ext through degree 3. The output is
# qpa_census_generated.json. It never writes the committed expected file.
#
# Run from a temporary directory with QPA loadable:
#
#   gap -q -T -m 1g generate_census_fixtures.g

LoadPackage("qpa");

FIELD := 2;
MAX_EXT := 3;
ORDER_ID := "deglex-arrowid-v1";
OUT := "qpa_census_generated.json";
SENTINEL := "qpa-census-oracle-generator-ok";

Q := Quiver(4, [[1,2,"a"], [2,4,"b"], [1,3,"c"], [3,4,"d"]]);
K := GF(FIELD);
kQ := PathAlgebra(K, Q);
arrows := List(ArrowsOfQuiver(Q), a -> a * One(kQ));
A := kQ / [arrows[1] * arrows[2] + arrows[3] * arrows[4]];

# The raw domain uses arrow-major, row-major coordinates. The final coordinate
# is the least-significant binary digit, matching the Rust census cursor.
CoordinatesAt := function(cursor, count)
  local coordinates, i;
  coordinates := [];
  for i in [count, count - 1 .. 1] do
    Add(coordinates, RemInt(QuoInt(cursor, FIELD ^ (i - 1)), FIELD));
  od;
  return coordinates;
end;

MatrixAt := function(coordinates, offset, rows, columns)
  local matrix, i, j;
  matrix := [];
  for i in [1 .. rows] do
    Add(matrix, []);
    for j in [1 .. columns] do
      Add(matrix[i], coordinates[offset + (i - 1) * columns + j] * One(K));
    od;
  od;
  return matrix;
end;

MatricesAt := function(coordinates, dimensions)
  return [
    MatrixAt(coordinates, 0, dimensions[1], dimensions[2]),
    MatrixAt(coordinates, dimensions[1] * dimensions[2], dimensions[2], dimensions[4]),
    MatrixAt(coordinates,
      dimensions[1] * dimensions[2] + dimensions[2] * dimensions[4],
      dimensions[1], dimensions[3]),
    MatrixAt(coordinates,
      dimensions[1] * dimensions[2] + dimensions[2] * dimensions[4]
        + dimensions[1] * dimensions[3],
      dimensions[3], dimensions[4])
  ];
end;

# RightModuleOverPathAlgebra prints a line for each rejected relation. The
# relation action is evaluated from QPA's own relator before that constructor,
# so only valid matrices reach the constructor and the run stays readable.
RelationZero := function(matrices)
  local relation, terms, action, accumulated, path, i, arrow;
  relation := RelatorsOfFpAlgebra(A)[1];
  terms := CoefficientsAndMagmaElements(relation);
  accumulated := fail;
  for i in [1, 3 .. Length(terms) - 1] do
    path := WalkOfPath(terms[i]);
    action := One(K);
    for arrow in path do
      action := action * matrices[
        arrow!.gen_pos - Length(VerticesOfQuiver(Q))];
    od;
    action := terms[i + 1] * action;
    if accumulated = fail then
      accumulated := action;
    else
      accumulated := accumulated + action;
    fi;
  od;
  return accumulated = NullMat(
    Length(matrices[1]), Length(matrices[2][1]), K);
end;

ExtDimension := function(M, degree)
  local syzygy;
  if degree = 0 then
    return Length(HomOverAlgebra(M, M));
  fi;
  if degree = 1 then
    return Length(ExtOverAlgebra(M, M)[2]);
  fi;
  syzygy := NthSyzygy(M, degree - 1);
  if Dimension(syzygy) = 0 then
    return 0;
  fi;
  return Length(ExtOverAlgebra(syzygy, M)[2]);
end;

SelfExt := function(M)
  return List([0 .. MAX_EXT], degree -> ExtDimension(M, degree));
end;

JsonIntList := function(values)
  return Concatenation("[", JoinStringsWithSeparator(List(values, String), ","), "]");
end;

JsonCoordinates := function(cursor, coordinates, class)
  return Concatenation("{\"cursor\":", String(cursor),
    ",\"coordinates\":", JsonIntList(coordinates),
    ",\"class\":", String(class), "}");
end;

JsonRepresentative := function(record)
  return Concatenation("{\"cursor\":", String(record.cursor),
    ",\"coordinates\":", JsonIntList(record.coordinates),
    ",\"self_ext\":", JsonIntList(record.self_ext), "}");
end;

JsonDomain := function(record)
  local accepted, rejected, representatives, free1, free3, i;
  accepted := List(record.accepted,
    entry -> JsonCoordinates(entry.cursor, entry.coordinates, entry.class));
  rejected := JsonIntList(record.rejected);
  representatives := List(record.representatives, JsonRepresentative);
  free1 := Filtered([0 .. Length(record.representatives) - 1],
    i -> record.representatives[i + 1].self_ext[2] = 0);
  free3 := Filtered(free1,
    i -> ForAll([2 .. MAX_EXT + 1], degree ->
      record.representatives[i + 1].self_ext[degree] = 0));
  return Concatenation(
    "{\"id\":\"", record.id, "\",",
    "\"dimensions\":", JsonIntList(record.dimensions), ",",
    "\"raw_space_size\":", String(record.raw_space_size), ",",
    "\"coordinate_count\":", String(record.coordinate_count), ",",
    "\"candidates\":", String(record.candidates), ",",
    "\"accepted_modules\":", String(record.accepted_modules), ",",
    "\"rejected_candidates\":", String(record.rejected_candidates), ",",
    "\"isomorphism_checks\":", String(record.isomorphism_checks), ",",
    "\"accepted\":[", JoinStringsWithSeparator(accepted, ","), "],",
    "\"rejected\":", rejected, ",",
    "\"representatives\":[",
      JoinStringsWithSeparator(representatives, ","), "],",
    "\"ext1_free\":", JsonIntList(free1), ",",
    "\"ext1_to_3_free\":", JsonIntList(free3), "}"
  );
end;

EnumerateDomain := function(id, dimensions)
  local coordinate_count, raw_space_size, classes, accepted, rejected,
    cursor, coordinates, matrices, M, class, i, checks, representatives;
  coordinate_count := Sum([1, 2, 3, 4], i ->
    dimensions[ [1, 2, 1, 3][i] ] * dimensions[ [2, 4, 3, 4][i] ]);
  raw_space_size := FIELD ^ coordinate_count;
  classes := [];
  accepted := [];
  rejected := [];
  checks := 0;
  for cursor in [0 .. raw_space_size - 1] do
    coordinates := CoordinatesAt(cursor, coordinate_count);
    matrices := MatricesAt(coordinates, dimensions);
    if not RelationZero(matrices) then
      Add(rejected, cursor);
      continue;
    fi;
    M := RightModuleOverPathAlgebra(A, matrices);
    if M = fail then
      Error("QPA rejected a relation-valid census representation");
    fi;
    class := fail;
    for i in [1 .. Length(classes)] do
      checks := checks + 1;
      if IsomorphicModules(classes[i].module, M) then
        class := i;
        break;
      fi;
    od;
    if class = fail then
      Add(classes, rec(cursor := cursor, coordinates := coordinates, module := M));
      class := Length(classes);
    fi;
    Add(accepted, rec(cursor := cursor, coordinates := coordinates, class := class - 1));
  od;
  representatives := List(classes, record -> rec(
    cursor := record.cursor,
    coordinates := record.coordinates,
    self_ext := SelfExt(record.module)));
  return rec(
    id := id,
    dimensions := dimensions,
    raw_space_size := raw_space_size,
    coordinate_count := coordinate_count,
    candidates := raw_space_size,
    accepted_modules := Length(accepted),
    rejected_candidates := Length(rejected),
    isomorphism_checks := checks,
    accepted := accepted,
    rejected := rejected,
    representatives := representatives);
end;

DomainRecords := [
  EnumerateDomain("d1111", [1,1,1,1]),
  EnumerateDomain("d2112", [2,1,1,2])
];

EmitJson := function(records)
  local buffer, output, i, domains;
  buffer := "";
  output := OutputTextString(buffer, true);
  SetPrintFormattingStatus(output, false);
  domains := List(records, JsonDomain);
  AppendTo(output, "{\n");
  AppendTo(output, "  \"schema\": \"auslander-qpa-census-oracle-v1\",\n");
  AppendTo(output, "  \"convention\": \"right\",\n");
  AppendTo(output, "  \"family\": \"commutative-square\",\n");
  AppendTo(output, "  \"field\": 2,\n");
  AppendTo(output, "  \"presentation_id\": \"commutative-square\",\n");
  AppendTo(output, "  \"ideal_id\": \"commutative-square\",\n");
  AppendTo(output, "  \"order\": \"", ORDER_ID, "\",\n");
  AppendTo(output, "  \"quiver\": {\n");
  AppendTo(output, "    \"num_vertices\": 4,\n");
  AppendTo(output, "    \"arrows\": [\n");
  AppendTo(output, "      {\"name\":\"a\",\"source\":0,\"target\":1},\n");
  AppendTo(output, "      {\"name\":\"b\",\"source\":1,\"target\":3},\n");
  AppendTo(output, "      {\"name\":\"c\",\"source\":0,\"target\":2},\n");
  AppendTo(output, "      {\"name\":\"d\",\"source\":2,\"target\":3}\n");
  AppendTo(output, "    ]\n");
  AppendTo(output, "  },\n");
  AppendTo(output, "  \"relations\": [{\"terms\":[");
  AppendTo(output, "{\"coeff\":1,\"path\":[0,1]},");
  AppendTo(output, "{\"coeff\":1,\"path\":[2,3]}]}],\n");
  AppendTo(output, "  \"provenance\": {\n");
  AppendTo(output, "    \"gap_version\": \"", GAPInfo.Version, "\",\n");
  AppendTo(output, "    \"qpa_version\": \"", InstalledPackageVersion("qpa"), "\",\n");
  AppendTo(output, "    \"command\": \"gap -q -T -m 1g generate_census_fixtures.g\"\n");
  AppendTo(output, "  },\n");
  AppendTo(output, "  \"domains\": [\n");
  for i in [1 .. Length(domains)] do
    if i < Length(domains) then
      AppendTo(output, "    ", domains[i], ",\n");
    else
      AppendTo(output, "    ", domains[i], "\n");
    fi;
  od;
  AppendTo(output, "  ]\n");
  AppendTo(output, "}\n");
  CloseStream(output);
  FileString(OUT, buffer);
end;

EmitJson(DomainRecords);
Print("wrote ", OUT, " with ", Length(DomainRecords), " domains\n");
Print(SENTINEL, "\n");
QUIT;
