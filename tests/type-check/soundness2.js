
function() :: (->) {

	// z <: y
	var z :: {x :: { field :: int, field2 :: int }} =
		{x : {field: 50, field2: 9000 } };
	var y :: {x :: { field :: int }} = 
		{x : {field: 50 }};

	var t :: int = y.x.field;
	y = z; // this assignment should succeed 

	t = y.x.field;

  y.x = {field: 30}; //this should fail, because now z.x.field2 is broken.
} @@ fails;

function () :: (->) {
  function oomra(y) :: ({x :: {field :: int}} ->) {
    y.x = {field: 30};
  }

  var z = {x : {field:50, field2: 9000}};
  oomra(z);
  z.x.field2;
} @@ fails;

function() :: (->) {
  function writeToF2(bar) :: ({field::int, field2::int} -> ) {
    bar.field2 = 50;
  };
  
	// z <: y
	var z :: {x :: { field :: int, field2 :: int }} =
		{x : {field: 50, field2: 9000 } };
	var y :: {x :: { field :: int }} = 
		{x : {field: 50 }};

	var t :: int = y.x.field;
	y = z; // this assignment should succeed 
  writeToF2(y.x); //should work
} @@ succeeds;



