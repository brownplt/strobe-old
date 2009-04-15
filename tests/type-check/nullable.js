function (a) :: (int? -> int) {
  if (typeof a == "undefined")
    return 0;
  else
    return a * 15;
} :: int? -> int;

function (a) :: (int? -> int) {
  var x :: int?;
  x = undefined;
  x = 5;
  x = undefined;
  if (typeof x == "undefined") {
    return 4;
  }
  else
    return x;
} :: int? -> int;

function (x) :: (int? -> int) {
  if (typeof x == "undefined") {
    return 4;
  }
  else
    return x;
} :: int? -> int;

function (a) :: (int? -> int) {
  var x :: int? = undefined;
  if (typeof x == "undefined") {
    x = undefined;
    return x;
  }
  else
    return 4;
} @@ fails;
function () :: (->) {
  var z :: int = 5;
  z = undefined;
} @@ fails;

//works on unions:
function (a) :: (U(int, bool)? -> U(int, bool)) {
  return a;
} @@ fails;
function (a) :: (U(int, bool)? -> U(int, bool)) {
  if (typeof a != "undefined")
    return a;
  return 5;
} :: (U(int, bool)? -> U(int, bool));


//can't invoke nullable function
function (a) :: (int -> int) {
  var procint :: (int -> int)?;
  return procint(a);
} @@ fails;

//YAY WE OWNED SCHEME:
function (a) :: (int -> int) {
  var procint :: (int -> int)?;
  procint = function (v) :: (int -> int) { return v*2; };
  return procint(a);
} :: (int -> int);

function (a) :: (int -> int) {
  var procint :: (int -> int)?;
  procint = function (v) :: (int -> int) { return v*2; };
  if (typeof procint != "undefined")
      return procint(a);
  return 0;
} :: (int -> int);

//can't declare a function as nullable:
function (a) :: (int -> int) {
  var procint :: (int -> int)?;
  procint = function (v) :: (int -> int)? { return v*2; };
} @@ fails;
