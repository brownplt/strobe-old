function(x) :: forall a . a -> a {
  return x;
} :: forall a . a -> a;

function() :: (->) {
  function id(x) :: forall a . a -> a { return x; }

  var id2 = function(x) :: forall b . b -> b {
    return id@[(b)](x);
  };

  var z = id@[(int)](23);

  var g = id@[(string)]("hello claudiu");

  var z1 = id2@[(int)](23);

  var g2 = id2@[(string)]("hello claudiu");

} :: (->);

function()  :: (->) {

  var silly = function() :: forall a . -> unit { return; }

  silly@[(nonexistantType)]();
} @@ fails;

function (o) :: {x :: int} -> int {
  return o.x;
} :: ({x :: int} -> int);

function() :: (->) {

  var sel = function(o) :: { x :: int } -> int {
    return o.x + 1;
  };

  var r1 = sel({ x: 454 });

  // Limited subtyping is possible without constrainted polymorphism
  var r2 = sel({ x: 25234, y: 1231 });

} :: (->);

function(obj) :: forall a : a <: { x :: int } . a -> int {
  return obj.x;
} :: forall a : a <: { x :: int } . a -> int;

// Test cases of map, filter, etc. are in arrays.js
