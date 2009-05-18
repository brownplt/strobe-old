// Soundness of assignment

function(obj) :: { either :: U (int, string) } -> undefined {
  // The calling context supplying 'obj' cannot anticipate the type of
  // obj.either changing.
  obj.either = "should fail";
} @@ fails;


function(obj) :: { either :: U (int, string) } -> undefined {
  // Refinement preserve failure here.
  if (typeof obj.either == "number") {
    obj.either = "should fail";
  }
  else {
    obj.either = 42;
  }
} @@ fails;

function() :: (->) {

  // y <: z
  var z :: Array<{ field :: int }> = [ { field: 50 } ];
  var y :: Array<{ field :: int, field2 :: int }> = 
    [ { field: 50, field2: 9000 } ];

  var t :: int = y[0].field2;
  y = z; // this assignment should fail

  // If the assignment does not fail, the following will signal a runtime type
  // error
  //  t = y[0].field2;

} @@ fails;

function() :: (->) {

  // z <: y
  var z :: Array<{ field :: int, field2 :: int }> = 
    [ { field: 50, field2: 9000 } ];
  var y :: Array<{ field :: int }> = [ { field: 50 } ];

  var t :: int = y[0].field2;
  y = z; // this assignment should fail

  // If the assignment does not fail, the following will signal a runtime type
  // error
  //  t = y[0].field2;

} @@ succeeds;

// We simply cannot have int <: double.  They are completely different types
// what JavaScript has are implicit casts, which have nothing to do with
// subtyping.
