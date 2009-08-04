relations {
  forall a . a -> a <: forall b . b -> b;
  forall a . a -> Int <: forall a . a -> Double
}

expressions {

  succeed function(x) :: forall a . a -> a {
    return x;
  };

  succeed function() :: -> Undefined {
    function id(x) :: forall a . a -> a { return x; }

    var id2 = function(x) :: forall b . b -> b {
      var r :: b -> b = id@[b];
      return r(x);
    };


    var id3 = function(x) :: forall b . b -> b {
      return id@[b](x);
    };

  var z = id@[Int](23);

  var g = id@[String]("hello claudiu");

  var z1 = id2@[Int](23);

  var g2 = id2@[String]("hello claudiu");

  };

  fail function() :: -> Undefined {

  var silly = function() :: forall a . -> Undefined { return; }

  silly@[nonexistantType]();
  };

  succeed function (o) :: {x :: Int} -> Int {
    return o.x;
  };

  succeed function() :: (-> Undefined) {

    var sel = function(o) :: { x :: Int } -> Int {
      return o.x + 1;
    };
  
    var r1 = sel({ x: 454 });
  
    var r2 = sel({ x: 25234, y: 1231 });
  
  };

  succeed function(a,b) :: forall a b . a, b -> a {
    return a;
  };

  succeed function(f,x) :: forall a b . (a -> b), a -> b {
    return f(x);
  };

  succeed function(f, x, y) :: forall a b . (a, b -> b), a , b -> b {
    return f(x, y);
  };

  fail function(f, x, y) :: forall a b . (a, b -> b), a , b -> b {
    return f(y, x);
  }


}
  
body {
    function id(x) :: forall a . a -> a { return x; }

    var id2 = function(x) :: forall b . b -> b {
      var r :: b -> b = id@[b];
      return r(x);
    };


    var id3 = function(x) :: forall b . b -> b {
      return id@[b](x);
    };

  var z = id(23);

  var g = id("hello claudiu");

  var z1 = id2@[Int](23);

  var g2 = id2("hello claudiu");

}
  
body {
 var foo =  function(f, x, y) :: forall a b . (a, b -> b), a , b -> b {
    return f(x, y);
  };

 var f = function(x,y) :: Int, String -> String { return y + "junta"; };

 foo@[Int, String](f, 99, "helo");

}


body {
 var foo =  function(f, x, y) :: forall a b . (a, b -> b), a , b -> b {
    return f(x, y);
  };

 var f = function(x,y) :: Int, String -> String { return y + "junta"; };

 foo(f, 99, "helo");

}

body fail {
 var foo =  function(f, x, y) :: forall a b . (a, b -> b), a , b -> b {
    return f(x, y);
  };

 var f = function(x,y) :: Int, String -> Int { return x + x; };

 foo(f, 99, "helo");

}
