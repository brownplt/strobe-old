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

  // z <: y
  var z :: { field :: int, field2 :: int } = { field: 50, field2: 9000 } ;
  var y :: { field :: int } = { field: 50 };

  var t :: int = y.field;
  y = z; // this assignment should succeed 

  t = y.field;
} @@ succeeds;

function() :: (->) {

  // z <: y
  var z :: Array<{ field :: int, field2 :: int }> 
    = [ { field: 50, field2: 9000 }  ];
  var y :: Array<{ field :: int }> = [ { field: 50 } ];

  var t :: int = y[0].field;
  y = z; // this assignment should succeed 

  t = y[0].field;
} @@ succeeds;

function() :: (->) {

  // z <: y
  var z :: Array<{ field :: int, field2 :: int }> 
    = [ { field: 50, field2: 9000 }  ];
  var y :: Array<{ field :: int }> = [ { field: 50 } ];

  var t :: int = y[0].field;
  y = z; // this assignment should succeed 

  t = y[0].field;

  y[1] = {field: 5}; //this should fail
  z[1].field2;
} @@ fails;



// We simply cannot have int <: double.  They are completely different types
// what JavaScript has are implicit casts, which have nothing to do with
// subtyping.
