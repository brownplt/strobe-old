function() :: (->) {
  var x :: int = 5;
  var y = function() :: -> int {
    return x + 5;
  }
} @@ succeeds;
  
function() :: (->) {
  var x = 5;
  var y = function() :: -> int {
    return x + 5;
  }
} @@ succeeds;

function() :: (->) {
  var f = function() :: -> string {
    return x;
  };
  var x :: U(int, string) = 42;
  
  if (typeof x == "number") { x = "make me a string"; } 
	// We type-check f just once.  The type of f should be correct regardless of
	// the context in which it is called.
  // Since x :: U(int, string) is defined in the enclosing
	// environment, even though we know that x :: TRefined U(int, string) string,
	// we should use this assumption to check f.
  f();
} @@ fails;

function() :: (->) {
  function bar() :: -> int { return x; }
  bar();
  var x :: int = 10;
} @@ fails;
