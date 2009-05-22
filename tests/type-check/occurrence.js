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

//pathological example that no one cares about:
function () :: (-> int) {
  var y :: U(int, string) = 4;
  var z :: U(int, string) = 19;
  (function() :: (->) { z = "HAHAHA"; })();
  return y;
} @@ fails;


function() :: (->) {
  var x :: U(int, string, bool) = "hello";
  var y :: string =
    (typeof ((typeof x == "number") ? "x is a number" : x) == "boolean")
      ? "x is a boolean"
      : x;

} @@ succeeds;

//switch statements:
function (x) :: (U(string, bool) -> string) {
  switch (typeof x) {
    case 'string':
      return x;
    default:
      return "was not a string";
  };
} :: (U(string, bool) -> string);

function (x) :: (U(int, string, bool) -> int) {
  switch (typeof x) {
    case 'number':
     return x;
     break;
    case 'string':
     return 33;
     break;
    case 'bool':
     if (x) return 0; else return 1;
     break;
  };
  //we only get here if something is whacked out
  return 13;
} @@ fails;

function (x) :: (U(int, string, bool) -> int) {
  var z :: int = 1;
  var s :: string = "s";
  var b :: bool = true;
  switch (typeof x) {
    case 'number':
     z = x;
     break;
    case 'string':
     s = x;
     break;
    default:
     b = x;
     break;
  };
  return 13;
} :: U(int, string, bool) -> int;
//if equivalent:
function (x) :: (U(int, string, bool) -> int) {
  var z :: int = 1;
  var s :: string = "s";
  var b :: bool = true;
  if (typeof x == "number") {
    z = x;
  } else {
    if (typeof x == "string") {
      s = x;
    } else {
      b = x;
    }
  }
  return 13;
} :: U(int, string, bool) -> int;


function (x) :: int -> int {
  switch (typeof x) {
    default:
     return x;
  }
} :: int -> int;

function (x) :: (U(int, string, bool) -> int) {
  var z :: int = 1;
  var s :: string = "s";
  var b :: bool = true;
  switch (x) {
    case 3:
     z = x;
     break;
    case 'string':
     s = x;
     break;
  };
  return 13;
} :: U(int, string, bool) -> int;

//VPWeakType:
function (x) :: U(int, bool) -> int {
  var b :: bool = true;
  if (x == 3)
    return x;
  else
  {
    b = x; //x is still U(int, bool) here.
    return 5;
  }
} @@ fails;
function (x) :: U(int, bool) -> int {
  if (x != 3) {
    return 4;
  }
  return x;
} :: U(int, bool) -> int;
function (x) :: U(int, bool) -> int {
  var b :: bool = true;
  if (x == 3)
    return x;
  else {
    if (x == true)
    {
      b = x;
      return 3;
    }
    return 4;
  }
} :: U(int, bool) -> int;

