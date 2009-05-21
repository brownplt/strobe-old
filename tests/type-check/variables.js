function (x) :: (double -> double) {
  var z :: double = 23;
  return z * x;
} :: (double -> double);
//both expr and type:
function (x) :: (double -> double) {
  var z :: double = 13;
  return z * x;
} :: (double -> double);
//mismatching expr and type:
function (x) :: (double -> double) {
  var z :: double = "HAHAHAHAHAHAHA";
  return z * x;
} @@ fails;
//just exprs:
function (x) :: (double -> double) {
  var z = 15;
  return z * x;
} :: (double -> double);
function (x) :: (double -> double) {
  var y = 43;
  var z = y;
  return z * x;
} :: (double -> double);

function (x) :: (double -> double) {
  var z = y;
  var y = 13;
  return z * x;
} @@ fails;

//more complex
function (ignore) :: (int -> string) {
  var a = 3;
  var b = 19 + a;
  var c = "A STRING";
  var d = "ANOTHeR STRING";
  var e = (a*4 == (b - 23)) ? c : d;

  if (a*b == 4)
  {
      if (e == c) {
        return d;
      }
      return c;
  }
  else
      return c+d;
} :: (int -> string);
function (ignore) :: (int -> string) {
  var a = 3;
  var b = 19 + a;
  var c = "A STRING";
  var d = "ANOTHeR STRING";
  var e = (a*4 == (b - 23)) ? c : d;

  if (a*b == 4)
  {
      if (e == c) {
        return d;
      }
      return c;
  }
  return c+d;
} :: (int -> string);

//function variables!!
function (mult) :: (double -> (double -> double)) {
  function inner(a) :: (double -> double) {
      return mult * a;
  }
  return inner;
} :: (double -> (double -> double));

//using variables only declared later:
function (x) :: (double -> double) {
  var z = y + 9;
  var y = 13;
  return y;
} @@ fails;

//repeating a variable:
function (x) :: (double -> string) {
  var y = 5;
  var y = "stringy";
  return y;
} @@ fails;

//javascript doesn't have block scoping, so this also should fail:
function (x) :: (double -> string) {
  var y = 5;
  if (true)
  {
    var y = "stringy";
    y += "4aaa";
  }
  return y; // use before definition here
} @@ fails;

//the next one should fail, since z has type string?
function (x) :: (double -> string) {
  var y = 5;
  var z :: U(string,undefined) = undefined;
  if (true)
  {
    z = "stringy";
    z += y;
  }
  return z;
} @@ fails;

//but the next one should succeed
function (x) :: (double -> string?) {
  var y = 5;
  var z :: U(string,undefined) = undefined;
  if (true)
  {
    var z = "stringy";
    z += y;
  }
  return z;
} :: (double -> string?);

//re-declaring parameter as another type:
function (x) :: (double -> string) {
  var x = "A string it";
  return x;
} @@ fails;

// This is legal JavaScript, and our ANF transformation erases all traces of
// it.  So, we permit it.
function (x) :: (double -> string) {
  var y = "string1";
  var y = "stringy";
  return y;
} @@ succeeds;

function (x) :: (double -> string) {
  var x = x + 9;
  return x + "s";
} @@ fails;

//TODO: this next one works just fine, as it is, but should we allow
//re-declaring variables with differing types / redeclaring them at
//all?
function (x) :: (double -> double) {
  var f :: string = "captain planet";
  function doit(ahahah) :: (string -> double) {
    var f :: double = 15.3;
    return f * 5;
  }
  return doit(f);
} :: (double -> double);


