function (a, b, c) :: (int, int, int -> int) {
    return a + b + c;
} :: (int, int, int -> int);
function (i, d, s) :: (int, double, string -> string) {
    var x = d * i; //double
    var f = i + i; //int
    var z = s+s, z2 = s+i, z3 = z+d; //strings
    return z + z2 + z3;
} :: (int, double, string -> string);
function () :: (-> string) {
  function inner(b, d, s) :: (bool, double, string -> string) {
    var x = d * (b ? 5 : 3); //double
    var z = s+s, z2 = s+x, z3 = z+d; //strings
    return z + z2 + z3;
  }
  return inner(true, 3.96, "A STRING!!!");
} :: (-> string);

function (r1, r2, o1, o2) :: (int, int, int, double -> string) {
    return r1+r2+(o1 * 534) + "";
} :: (int, int, int, double -> string);

function() :: (-> string) {
  function inner(r1, r2, o1, o2) :: (double, double, double?, string? -> string) {
    return "cake" + r1+r2+(000 * 534);
  }
  inner(1, 2);
  inner(1, 2, 3);
  return inner(1, 2, 95, "HI");
} :: (-> string);
function() :: (-> string) {
  function inner(r1, r2, o1, o2) :: (double, double, double?, string? -> string) {
    return r1+r2+(o1 * 534) + o2;
  }
  return inner(1);
} @@ fails;
function() :: (-> string) {
  function inner(r1, r2, o1, o2) :: (double, double, double?, string? -> string) {
    return r1+r2+(o1 * 534) + o2;
  }
  return inner();
} @@ fails;

function() :: (-> string) {
  function inner(r1, r2, o1, o2) :: (double, double, double?, string? -> string) {
    return r1+r2+(o1 * 534) + o2;
  }
  return inner(1, 9, "43");
} @@ fails;


function() :: (-> string) {
  function inner(r1, r2, o1, o2) :: (double, double, double?, string? -> string) {
    return r1+r2+(o1 * 534) + o2;
  }
  return inner("43");
} @@ fails;

function(a) :: (string?, int?, double? -> int) {
} @@ fails;
function(a,b) :: (string?, int?, double? -> int) {
} @@ fails;
function(a,b,c,d) :: (string?, int?, double? -> int) {
} @@ fails;
function() :: (string?, int?, double? -> int) {
} @@ fails;
function(a,b,c) :: (string, int, double -> int) {
  var x :: string = a + b + c;
  var f :: int = b * b << b;
  var f2 :: double = b + (c / 3.9);
  return f;
} :: (string, int, double -> int);
function() :: (->) {
  var x :: int = 53;
  function testit(a,b,c) :: (string, int, double -> int) {
    var x :: string = a + b + c;
    var f :: int = b * b << b;
    var f2 :: double = b + (c / 3.9);
    return f;
  }
  var g = 23;
  var g2 = 45;
  var g3 = 356;
  var g9 = 4646;
  var g331 = testit("Ag", g9+g3^g2, x+3.0);
} :: (->);

/* TODO: Lots of undefined here
function() :: (->) {
  function applymaybe(func, arg) :: (int? -> string), int? -> string {
    if (func == undefined) return "no apply";
    return "func called, res = " + func(arg);
  }
  applymaybe();
  applymaybe(undefined);
  applymaybe(null);
  function showmaybe(anint) :: (int? -> string) {
    return "given arg, arg was: " + anint;
  }
  applymaybe(showmaybe);
  applymaybe(showmaybe, undefined);
  applymaybe(showmaybe, 93);
} :: (->);

function() :: (->) {
  function applymaybe(func, arg) :: ((int? -> string)?, int? -> string) {
    if (func == undefined) return "no apply";
    return "func called, res = " + func(arg);
  }
  applymaybe(39, 4);
} @@ fails;

*/
