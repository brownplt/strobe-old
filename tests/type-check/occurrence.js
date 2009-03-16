function (x) :: (U(int, bool) -> bool) {
  //the typed scheme paper example
  return (isInt(x) ? (x<<3)==8 : !x);
} :: (U(int, bool) -> bool);

//make sure we can filter out not only equal types:
function (x) :: (U(int, bool) -> bool) {
  return (typeof x == "number" ? (x<<3)==8 : !x);
} :: (U(int, bool) -> bool);

function (x) :: (U(int, bool, string) -> bool) {
  return (isInt(x) ? (x<<3)==8 : !x);
} @@ fails;

function (x) :: U(string, bool) -> string { return x; } @@ fails;
function (x) :: U(string, bool) -> string {
  if (true) return x;
  return "h";
} @@ fails;

function (x) :: (U(string, bool) -> string) {
  if (typeof x == "string") {
    //TODO: change return stmt checking so that occurrence typing has an effect
    //on it! (i.e. move it into typeCheckStmts)
    return x;
  }
  return "was not a string";
} :: (U(string, bool) -> string);

function (x) :: (U(int, bool) -> bool) {
  if (typeof x == "boolean") {
    if (x) { return false; }
  }
  return true;
} :: (U(int, bool) -> bool);

//!= instead of ==:
function (x) :: (U(int, bool) -> bool) {
  if (typeof x == "boolean") {
    if (x) { return false; }
  }
  return true;
} :: (U(int, bool) -> bool);

function (x) :: (U(int, bool) -> bool) {
  if (typeof x != "boolean") {
    var f :: int = 0;
    f = x >> 3;
    return true;
  }
  else
  {
    if (x) { return false; }
  }
  return true;
} :: (U(int, bool) -> bool);
function (x) :: (U(int, bool) -> bool) {
  if (typeof x != "boolean") {
    var f :: int = 0;
    f = x >> 3;
    return true;
  }
  else
  {
    if (x) { return false; }
    var b :: 'false = false; //'
    b = x; //x should be false here
    return true;
  }
} :: (U(int, bool) -> bool);

function (x) :: (U(int, bool) -> bool) {
  if ((typeof x) != "boolean") {
    var f :: int = 0;
    f = x >> 3;
    return true;
  }
  if (x) { return false; }
  return true;
} :: (U(int, bool) -> bool);
function (x) :: (U(int, bool) -> bool) {
  if (!((typeof x) == "boolean")) {
    var f :: int = 0;
    f = x >> 3;
    return true;
  }
  if (x) { return false; }
  return true;
} :: (U(int, bool) -> bool);

//x shouldn't turn into "false" just because of occurrence typing:
function (x) :: int -> bool {
  if (!x)
    return x;
  return false;
} @@ fails;

//make sure we can filter out not only equal types:
function (x) :: (U(int, bool) -> bool) {
  return (typeof x == "number" ? (x<<3)==8 : !x);
} :: (U(int, bool) -> bool);

function (x) :: (U(int, bool) -> bool) {
  if (typeof x == "boolean") {
    if (x) { return false; }
  }
  return true;
} :: (U(int, bool) -> bool);

function (x) :: (any -> bool) {
  if (typeof x == "boolean") {
    if (x) { return false; }
  }
  return true;
} :: (any -> bool);

//what if we return on the if statement branch?
function (x) :: (U(int, bool) -> string) {
  if (typeof x == "boolean") {
    return "x was a boolean";
  }
  //now, x should be an integer
  var xshift :: int = 5;
  xshift = x >> 3;
  return "x was an int, here it is: " + x;
} :: (U(int, bool) -> string);

//what if we return on the if statement else branch?
function (x) :: (U(int, bool) -> string) {
  var result :: string = "tmp";
  if (typeof x == "number") {
    result = "x is a number.";
  }
  else
  {
    result = "x is a boolean";
    return result;
  }

  //x should be an int here
  var b :: int = 0;
  b = x << 3;
  return result + ", and x is an int here, and it's value * 8 = " + b;
} :: (U(int, bool) -> string);

//these should work even with var decls:
function (x) :: (U(string, bool) -> string) {
  if (typeof x == "string") {
    //TODO: change var processing so that occurrence typing has an effect
    //on it!
    var z = x;
    return z;
  }
  return "was not a string";
} :: (U(string, bool) -> string);

function (x) :: (U(int, bool) -> string) {
  if (typeof x == "boolean") {
    return "x was a boolean";
  }
  //now, x should be an integer
  var xshift :: int = x >> 3;
  return "x was an int, here it is: " + x;
} :: (U(int, bool) -> bool);

function (x) :: (U(int, bool) -> string) {
  var result :: string = "tmp";
  if (typeof x == "number") {
    result = "x is a number.";
  }
  else
  {
    result = "x is a boolean";
    return result;
  }

  //x should be an int here
  var b :: int = x << 3;
  return result + ", and x is an int here, and it's value * 8 = " + b;
} :: (U(int, bool) -> bool);






