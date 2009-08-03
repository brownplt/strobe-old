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

// implicit packing on return
expressions { 
  function(x) :: Int -> exists x . x {
    return x;
  } :: Int -> exists x . x;

  function(x) :: Int -> exists x . Int -> x {
    return function(x) :: Int -> Bool {
      return x == x;
    }
  } :: Int -> exists x . Int -> x;
  
  function(y) :: Int -> Undefined {
    var f = function(x) :: Int -> exists x . x {
      return x;
     };

     var z :: unpack t . t = f(y);
     return;
  } :: Int -> Undefined;

  function(packed) :: (exists x . Int -> x) -> (exists y . Int -> y) {
    var f :: unpack x . Int -> x = packed;
    return function(a) :: Int -> x {
      return f(a + 900);
    }
  } :: (exists x . Int -> x) -> (exists y . Int -> y)

}

// explicit/implicit packing of arguments in a call
body {

  var f = function(pkg) 
    :: (exists x . { z :: x, s :: (x -> x), c :: (x -> Int) })
    -> Int {
    var obj :: unpack x . { z :: x, s :: (x -> x), c :: (x -> Int) } = pkg;
    var succ = obj.s; // avoid silly this-type errors
    var toInt = obj.c;
    return toInt(succ(succ(succ(obj.z))));
  }

  f(pack Int exists x . { z :: x, s :: (x -> x), c :: (x -> Int) } in
    { z : 90
    , s : function(x) :: Int -> Int { return x * x; }
    , c : function(x) :: Int -> Int { return -x; }
    });
}

body {

  var f = function(pkg) 
    :: (exists x . { z :: x, s :: (x -> x), c :: (x -> Int) })
    -> Int {
    var obj :: unpack x . { z :: x, s :: (x -> x), c :: (x -> Int) } = pkg;
    var succ = obj.s; // avoid silly this-type errors
    var toInt = obj.c;
    return toInt(succ(succ(succ(obj.z))));
  }

  f({ z : 90
    , s : function(x) :: Int -> Int { return x * x; }
    , c : function(x) :: Int -> Int { return -x; }
    });
}

body {

  var f = function(pkg) 
    :: (exists x y . { z :: y, s :: (y -> x), c :: (x -> Int) })
    -> Int {
    var obj_ :: unpack x . exists y . { z :: y, s :: (y -> x), c :: (x -> Int) } 
             = pkg;
    var obj :: unpack y . { z :: y, s :: (y -> x), c :: (x -> Int) } = obj_;

    var succ = obj.s; // avoid silly this-type errors
    var toInt = obj.c;
    return toInt(succ((obj.z)));
  }

  f({ z : 90
    , s : function(x) :: Int -> Int { return x * x; }
    , c : function(x) :: Int -> Int { return -x; }
    });
}

body {
var f = function(pkg) :: (exists x y . { a :: x, b :: y }) -> Undefined {
  return;
}

f({ a : 90, b : "hello" });
}

body {
var f = function(pkg) :: (exists x . { a :: x }) -> Undefined {
  return;
}

f({ a: 900 });
}
  
