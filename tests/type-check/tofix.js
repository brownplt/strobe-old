function () :: (->) { //non-existent type names:
  var a :: nonexistent?;
} @@ fails;
function (a) :: (thesetypesdontexist ->) {
}  @@ fails;
function () :: (->) {
  var b :: Array<faketype>?;
} @@ fails;

//kinds:
function () :: (->) {
  var b :: Array<int, int>?;
} @@ fails;
function () :: (->) {
  var b :: Array<>?;
} @@ fails;

//functions are processed before other things:
function () :: (->) {
  var z = myadder(3, 2);
  function myadder(a, b) :: int, int -> int {
    return a+b;
  }
} :: (->);

//variables assignments are not:
function () :: (->) {
  var z = myadder(3, 2);
  var myadder :: int, int -> int = function (a,b) :: int, int -> int {
    return a+b;
  }
} @@ fails;
function () :: (->) {
  var z = myadder(3, 2);
  var myadder = function (a,b) :: int, int -> int {
    return a+b;
  }
} @@ fails;

//recursive function declarations:
function() :: (->) {
  function lawl(x) :: (int -> int) { return lawl(3); }
} :: (->);

//mutually recursive function declarations:
function() :: (->) {
  function lawl1(x) :: (int -> int) { return lawl2(3); }
  function lawl2(x) :: (int -> int) { return lawl1(3); }
} :: (->);

//vars are actually undefined before they are assigned:
function() :: (->) {
  function add(a,b) :: int, int -> int {
    return a + b; //expects int, not int?
  }
  add(v, q);
  var v = 5;
  var q = 6;
} @@ fails;

//vars are nullable if declared inside an if:
function() :: (-> int) {
  function add(a,b) :: int, int -> int {
    return a + b; //expects int, not int?
  }
  if (false) var v = 10;
  if (false) var q = 15;
  return add(v, q);
} @@ fails;

/*also to do:
"1. We need the value restriction implemented.
4. Can a type (TId "a") can leak to a sibling function that accepts
(TId "a") values, creating problems?" */

