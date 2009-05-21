function (x) :: (Number -> string) {
  return x.toString();
} @@ succeeds; //:: (Number -> string);

function (x) :: (Number -> string) {
  return x.toString();
} :: (Number -> string);

function (x) :: ({n :: Number, y :: {f :: Number}} -> double) {
  var f1 = x.n.valueOf();
  var f2 = x.y.f.valueOf();
  return f1+f2;
} :: ({n :: Number, y :: {f :: Number}} -> double);

