function (x) :: (U(int, bool) -> bool) {
  //the typed scheme paper example
  return (typeof x == "number" ? (x<<3)==8 : !x);
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
    var b = false;
    b = x; //x should be false here
    return true;
  }
} :: (U(int, bool) -> bool);

//testing control flow:
function (x) :: (U(int, bool) -> bool) {
   if (typeof x == "number") {
     return false;
   }
   else {
     return x; //x should be bool
   }
} :: U(int, bool) -> bool;

function (x) :: (U(int, bool) -> bool) {
   if (typeof x == "number") {
     return false;
   }
   return x; //x should be bool
} :: U(int, bool) -> bool;

//CATASTROPHIC FAILURES:
//---------------------
function (x) :: (U(int, bool) -> bool) {
   if (typeof x == "number") {
     return false;
   }
   if (x) {}
   return x; //x should be bool
} :: U(int, bool) -> bool;
function (x) :: (U(int, bool) -> bool) {
   if (typeof x == "number") {
     return false;
   }
   if (x) {3;}
   return x; //x should be bool
} :: U(int, bool) -> bool;
//---------------------

//y is not declared, so the following should fail:
function (x) :: (U(int, bool) -> bool) {
   if (typeof x == "number") {
     return false;
   }
   if (x) {
     var z = 9;
     y = z;
   }
   return x; //x should be bool
} @@ fails;
//---------------------

function (x) :: (U(int, bool) -> bool) {
   if (typeof x == "number") {
     return false;
   }
   if (x) {
     var z = 9;
   }
   return x; //x should be bool
} :: U(int, bool) -> bool;
function (x) :: (U(int, bool) -> bool) {
   if (typeof x == "number") {
     var ppzzr = 10;
     return false;
   }
   if (x) {
     var z = 9;
   }
   return x; //x should be bool
} :: U(int, bool) -> bool;

function (x) :: (U(int, bool) -> bool) {
   if (typeof x != "boolean") {
     return false;
   }
   if (x) {
     var z = 9;
   }
   return x; //x should be bool
} :: U(int, bool) -> bool;
function (x) :: (U(int, bool) -> bool) {
   if (typeof x != "boolean") {
     var ppzzr = 9;
     return false;
   }
   if (x) {
     var z = 9;
   }
   return x; //x should be bool
} :: U(int, bool) -> bool;


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
} :: (U(int, bool) -> string);

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
} :: (U(int, bool) -> string);

//magic
//TODO: fix operator precedence
function (x) :: U(int, bool, string) -> U(int, bool) {
  if ((typeof x == "number") || (typeof x == "bool"))
    return x;
  return 4;
} :: U(int, bool, string) -> U(int, bool);

//soundness plz
function (x) :: U(int, bool) -> int {
  var y = typeof x;
  if (y == "number") {
    return x;
  }
  return 10;
} :: U(int, bool) -> int;

function (x) :: U(int, bool) -> double {
  var y = typeof x;
  x = false;
  if (y == "number") {
    return x;
  }
  return 10;
} @@ fails;

//more soundness tyvm
function () :: (-> int) {
  var y :: U(int, string) = 4;
  (function() :: (->) { y = "HAHAHA"; })();
  return y;
} @@ fails;
//but not too restrictive plz
function () :: (-> int) {
  var y :: U(int, string) = 4;
  var z :: U(int, string) = 19;
  (function() :: (->) { z = "HAHAHA"; })();
  return y;
} :: (-> int);





