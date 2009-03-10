function(x) :: forall a . a -> a {
  return x;
} :: forall a . a -> a;

function() :: (->) {
  var id = function(x) :: forall a . a -> a { return x; }

  var z = id@[int](23);

  var g = id@[string]("hello claudiu");
  
} :: (->);
