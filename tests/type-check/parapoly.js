function(x) :: forall a . a -> a {
  return x;
} :: forall a . a -> a;

function() :: (->) {
  var id = function(x) :: forall a . a -> a { return x; }

  var id2 = function(x) :: forall b . b -> b {
    return id@[b](x);
  };

  var z = id@[int](23);

  var g = id@[string]("hello claudiu");
  
  var z1 = id2@[int](23);

  var g2 = id2@[string]("hello claudiu");
  
} :: (->);

function()  :: (->) {

  var silly = function() :: forall a . -> unit { return; }

  silly@[nonexistantType]();
} @@ fails;

// Test cases of map, filter, etc. are in arrays.js
