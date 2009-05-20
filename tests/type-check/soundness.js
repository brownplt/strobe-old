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

function () :: (->) {
  function oomra(y) :: ({x :: {field :: int}} ->) {
    y.x.field = 30;
  }

  var z = {x : {field:50, field2: 9000}};
  oomra(z);
  z.x.field2;
} @@ succeeds;

function() :: (->) {
  function writeToF2(bar) :: ({field2::int} -> ) {
    bar.field2 = 50;
  };

  // z <: y
  var z :: {x :: { field :: int, field2 :: int }} =
    {x : {field: 50, field2: 9000 } };
  var y :: {x :: { field :: int }} =
    {x : {field: 50 }};

  var t :: int = y.x.field;
  y = z; // this assignment should succeed, cause of subtyping
  writeToF2(y.x); //should work, since y.x, at this point, does have field2
} @@ succeeds;

//int and double subtyping things messing up
function () :: (-> Array<int>) {
  var z :: Array<int> = [1];
  var y :: Array<double> = [2.0];
  y = z; // this assignment is OK as long as you don't mutate anything
  return z;
} @@ succeeds;

function () :: (-> Array<int>) {
  var z :: Array<int> = [1];
  var y :: Array<double> = [2.0];
  y = z; // this assignment is OK as long as you don't mutate anything
  y[0] = 3.1; //this should fail
  return z;
} @@ fails;

//the only way to solve these next two might be to make subtyping immutable!
function () :: (-> ) {
  function inner(x) :: (Array<double> ->) {
    x[0] = 3.1;
  };

  var z :: Array<int> = [1];
  var y :: Array<double> = [2.0];
  y = z;
  inner(y); //this call should fail, cause inner mutates stuff improperly
} @@ fails;

//let's try an equivalent object one:
function () :: (-> ) {
  var z :: {foo :: int} = {foo: 1};
  var y :: {foo :: double} = {foo: 2.0};
  y = z;
  y.foo = 3.1;
} @@ fails;

function () :: (-> ) {
  function inner(x) :: ({foo :: double} ->) {
    x.foo = 3.1;
  };

  var z :: {foo :: int} = {foo: 1};
  var y :: {foo :: double} = {foo: 2.0};
  y = z;
  inner(y);
} @@ fails;
//can't reproduce this bug without int/double subtyping (good sign)!
function () :: (-> ) {
  function inner(x) :: ({foo :: {broohah :: int}} ->) {
    x.foo.broohah = 4;
  };

  var z :: {foo :: {broohah :: int, foohah :: int}} =
    {foo: {broohah: 1, foohah: 2}};
  var y :: {foo :: {broohah :: int}} =
    {foo: {broohah: 3}};
  y = z;
  inner(y);
} @@ succeeds;

//maybe subtyping shouldnt work the same for func calls?

//must make sure block level scoping is ok.
/*
{
  var z :: (-> int) = function() :: (-> int) { return 3; };

  if (false)
  {
    var x :: int = 5;
    z = function() :: (-> int) { return x; };
  }

  z();
}
  */


//declare before use stuff
function () :: (->) {
  var x :: int = 10;
  function zorro() :: (-> int) { return x; }
} @@ succeeds;

function () :: (->) {
  var x = 10;
  function zorro() :: (-> int) { return x; }
} @@ succeeds;

function () :: (->) {
  var x :: int = 10;
  function zorro() :: (-> int) { return x; }
} :: (->);
function () :: (->) {
  function zorro() :: (-> int) { return x; }
  zorro();
  var x = 10;
} @@ fails;

function () :: (->) {
  function zorro() :: (-> int) { return x; }
  zorro();
  var x :: int = 10;
} @@ fails;


//can't assign to global 'anys'
function () :: (-> int) {
  var x :: any = 4;
  function inner() :: (->) {
    x = "AHAH";
  };
  inner();
  return x;
} @@ fails;

function () :: (-> int) {
  var x :: any = 4;
  function inner() :: (->) {
  };
  return x;
} @@ succeeds;

function () :: (-> int) {
  var x :: any = 4;
  function inner(x) :: (any ->) {
    x = "FRFR";
  };
  inner(x);
  return x;
} @@ succeeds;

function () :: (-> int) {
  var x :: any = 4;
  function inner(x) :: (string ->) {
    x = "FRFR";
  };
  x = "he";
  inner(x);
  x = 3;
  return x;
} @@ succeeds;
