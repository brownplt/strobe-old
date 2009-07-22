relations {
  exists x . x -> Int = exists y . y -> Int;
  exists x . x -> Int <: exists y . y -> Double
}

expressions {

  function(x) :: Int -> exists x . x {
    return pack Int (exists x . x) in x;
  } :: Int -> exists x . x;

  function(x) :: Int -> exists x . Int -> x {
    return pack Bool (exists x . Int -> x) in function(x) :: Int -> Bool {
      return x == x;
    }
  } :: Int -> exists x . Int -> x;
  
  function(y) :: Int -> Undefined {
    var f = function(x) :: Int -> exists x . x {
      return pack Int (exists x . x) in x;
     };

     var z :: unpack t . t = f(y);
     return;
  } :: Int -> Undefined;

  function(packed) :: (exists x . Int -> x) -> (exists y . Int -> y) {
    var f :: unpack x . Int -> x = packed;
    return pack x (exists y . Int -> y) in function(a) :: Int -> x {
      return f(a + 900);
    }
  } :: (exists x . Int -> x) -> (exists y . Int -> y);

  function(packed) :: (exists x . Int -> x) -> Int {
    var f :: unpack x . Int -> x = packed;
    var z :: x = f(500);
    return 9;
  } :: (exists x . Int -> x) -> Int;
  
  fail function(packed) :: (exists x . Int -> x) -> Double {
    var f :: unpack x . Int -> x = packed;
    var z :: x = f(500);
    // The point is reflection is to discriminate unions, not defeat the
    // type system.
    if (typeof z == "number") {
      return z;
    }
  };

  fail function(packed) :: (exists x . Int -> x) -> Double {
    var f :: unpack x . Int -> x = packed;
    var z :: x = f(500);
    if (typeof z == "number") {
      return z;
    }
    return 900;
  };

  fail function(packed) :: (exists x . Int -> x) -> Double {
    var f :: unpack x . Int -> x = packed;
    var z :: x = f(500);
    if (typeof z == "number") {
      return z;
    }
    else { return 900; }
  }

}
