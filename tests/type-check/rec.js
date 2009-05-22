function() :: (->) {
  var fac :: int -> int = function(n) :: int -> int {
    if (n == 0) { return 1; }
    else { return n * fac(n-1); }
  }
} @@ succeeds;

function () :: (->) {
  var f :: rec h . int -> h = function(n) :: rec h . int -> h {
    return f; }

  f(10);
  f(10)(11);
  f(10)(11)(12);
} @@ succeeds;

function() :: (->) {
  var fac = function(n) :: int -> int {
     if (n == 0) { return 1; }
    else { return n * fac(n-1); }
  } 
} @@ succeeds;

function() :: (->) {
  var fac = function(n) :: int -> int {
     if (n == 0) { return 1; }
    else { return n * fac("hello"); }
  } 
} @@ fails;

