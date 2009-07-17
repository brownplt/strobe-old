relations {
  Int = Int;
  fail Int = Bool;
  Int = U(Int, Int);
  Int = U(Int, Int, Int);
  U(Int, Bool) = U(Bool, Int);
  Int <: Int;
  Int <: U(Int, Int);
  U(Int, Int) <: Int;
  Int <: Double;
  fail Double <: Int;
  Double = U(Double, Int);
  fail Int = U(Double, Int);
  Int <: U(Int, String);
  String <: U(Int, String);
  U(Int, String) <: U(Int, String, Bool);
  fail U(Int, String, Bool) <: U(Int, String)
}

expressions {
  45 :: Double;
  (true ? 4 : 5) :: Double;
  (true ? "hi there" : "bob jones") :: String;
  (true ? "HELLO" : 6) :: U(Int, String);
  (function (a) :: Double -> Double { return a; }) :: Double -> Double;
  (function (a) :: Double -> Double { return a; })(20) :: Double;
  (function (a) :: Double -> Double { return a+5; })(20) :: Double;
  fail (function(x,x) :: Int, Int -> Int { return x; });

  5 + "4" :: String;
  "5" + 34 :: String;
  "blah" + "hoomegl" :: String;
  fail 5.03 >> 3;
  fail 5.0 >> 3;
  fail 5e9 >> 7;
  fail -"arjun";
  -5  :: Int;
  -7.3  :: Double;
  4 / 343 :: Double;
  
  true && false :: Bool;
  true && (false || true) :: Bool;
  true && ((6 == 7) || (9 == 13)) :: Bool;
  fail true && x;
  
  fail 4 / "home";
  fail 4 * "3";
  5 + 4 :: Double; // subtype test
  4 * 3 :: Double;
  fail 4 / "13";
  fail 4 + (function(x) :: Double -> Undefined { return; });
  fail (3 == 0) + 10;
  
  (function (x) :: Double -> Undefined { return; }) :: Double -> Undefined;
  (function (x) :: Double -> Undefined { return; }) :: Double -> Undefined;
  fail (function (x) :: (Double -> Undefined) { return 5; });
  
  fail (function (x) :: -> Undefined { return; });
  fail (function () :: Int -> Undefined { return; });
  fail (function (x) :: Int -> Int { return "HAH"; });
  fail (function (x) :: Int -> Int { return; });

  //-----------------------------
  //Taken from CS173's typecheck:
  //-----------------------------
  3.0 :: Double;
  // (test (type-of (parse 'nempty)) (t-nlist))
  true :: Bool;
  false :: Bool;
  
  fail x ; //unbound ID
  
  (function (a) :: (Double -> Bool) { return a==0; })(20) :: Bool;
  fail (function (a) :: (Double -> Bool) { return a; })(20) ;
  
  (1 + 2) :: Double;
  (1 * 9 + 3) :: Double;
  4 + (9 - 5) :: Double;
  (9 * 10 - 11 - 12 - 13) == 0 :: Bool;

  fail (9 == 0) + (9 - 5);
  
  (0 == 0) ? (10 + 9) : (9 - 30) :: Double;
  (0 ==0 ) ? true : false :: Bool;
  
  fail 0 == 0 ? 10 + 9 : 9 - x ;
  fail 0 == 0 ? (3 == 0) + 10 : 9 - 30 ;
  0 == 0 ? 9 + 10 : 10 == 0 :: U(Bool, Int);
  0 == 0 ? 10 == 0 : 9 + 10 :: U(Bool, Int);
  0 == 0 ? true : 9 - 30 :: U(Bool, Int);
  (4 == 0) == 0 ? 9 + 10 : 9 - 30 :: Double;
  
  fail (function (a) :: (Double -> Bool) { return a == 0; })
    (4 == 0) ? 9 + 10 : 9 - 30;
  (function (a) :: (Double -> Bool) {
     return a == 0; })(4) ? 9 + 10 : "blerK" :: U(Int, String);
  
  
  (function (x) :: (Double -> Double) { return x; }) :: (Double -> Double);
  fail (function (x) :: (String -> Double) { return x; }) ;
  (function (x) :: (String -> Double) { return 43; }) :: (String -> Double);
  
  (function (x) :: (String -> Double) {
      return (x == "") ? 0 : 1; }) :: (String -> Double);
  (function (x) :: (String -> Bool) {
      return (x == "")}) :: (String -> Bool);
  //more complicated functions:
  (function (x) :: (Double -> (Double -> Double)) {
      return (function (y) :: (Double -> Double) {
                return x * y; }); }) :: (Double -> (Double -> Double));
  fail (function (x) :: (Double -> (Double -> Double)) {
      return (function (y) :: (Double -> Double) {
                 return x * z; }); }) ; //z is not defined
  (function (x) :: (Double -> (String -> Double)) {
      return (function (x) :: (String -> Double) {
                return (x=="" ? 5 : 10); }); }) :: (Double -> (String -> Double));
  fail (function (x) :: (String -> Double) {
       return x;}) ; //expected String, got Double
  
  //applying functions
  fail 4 (20) ; //can't apply non-function
  fail "moileben"("Stringy machine") ;
  
  (function (x) :: (Double -> (Double -> Double)) {
      return (function (y) :: (Double -> Double) {
                return x * y; }); })(33) :: (Double -> Double);
  (function (x) :: (Double -> (Double -> Double)) {
      return (function (y) :: (Double -> Double) {
                return x * y; }); })(33)(29) :: Double;
  
  //TODO: add testing w/  arrays, once we get those:
  fail (function (x) :: (Double -> Double) { return x; })("45") ;
  (function (x) :: (String -> Bool) { return x==""; })("45") :: Bool;
  fail (function (x) :: (String -> Bool) { return x==""; })(45) ;
  
  //NOTE: functional programming is ugly in javascript...
  (function (toapp) :: ((Double -> String) -> (Double -> String)) {
      return (function (x) :: (Double -> String) {
                return toapp(x); })}) ::
        ((Double -> String) -> (Double -> String));
  
  (function (toapp) :: ((Double -> String) -> (Double -> String)) {
      return (function (x) :: (Double -> String) { return toapp(x); })})
    (function (n) :: (Double -> String) { return ""+n;}) :: (Double -> String);
  (function (toapp) :: ((Double -> String) -> (Double -> String)) {
      return (function (x) :: (Double -> String) { return toapp(x); })})
    (function (n) :: (Double -> String) { return ""+n;})(93) :: String;
  
  fail (3 == 0)(13) ; //expected a function
  fail (x == 0)(13) ; //x not declared
  
  (function (x) :: (Double -> (Double -> Double)) {
    return (function (z) :: (Double -> Double) {
      return x + z; })})(4)(3) :: Double;
  fail (function (x) :: (Double -> Double) {
    return (function (z) :: (Double -> Double) {
       return x + z; })})(4)(3) ;
  fail (function (x) :: (Double -> Double) {
     return x + x;})(4)(3) ;
  
  fail (function (a) :: (-> Undefined) {return;}) ;
  
  //simple things that should succeed. test for when this doesn't matter
  4 :: Int;
  3 :: Int;
  
  function (x) :: String -> Undefined {
    return;
  } :: String -> Undefined
  
}  

///////////////////////////////////////////////////////////////////////////////
// Runtime type information

expressions {  

  function(x) :: U(Int, Bool) -> Bool {
    if (typeof x == "boolean") {
      return !!x;
    } else {
      return x == 34;
    }
  } :: U(Int, Bool) -> Bool;

  function (x) :: (U(Int, Bool) -> Bool) {
    //the typed scheme paper example
    return (typeof x == "number" ? (x<<3)==8 : !x);
  } :: (U(Int, Bool) -> Bool);
  
  //make sure we can filter out not only equal types:
  function (x) :: (U(Int, Bool) -> Bool) {
    return (typeof x == "number" ? (x<<3)==8 : !x);
  } :: (U(Int, Bool) -> Bool);
  
  function (x) :: (U(Int, Bool, String) -> Bool) {
    return (typeof x == "number" ? (x<<3)==8 : !x);
  } :: U(Int, String, Bool) -> Bool;
  
  fail function (x) :: U(String, Bool) -> String { return x; };
  
  fail function (x) :: U(String, Bool) -> String {
    if (true) return x;
    return "h";
  };
  
  function (x) :: (U(String, Bool) -> String) {
    if (typeof x == "string") {
      return x;
    }
    return "was not a String";
  } :: (U(String, Bool) -> String);
  
  function (x) :: (U(Int, Bool) -> Bool) {
    if (typeof x == "boolean") {
      if (x) { return false; }
    }
    return true;
  } :: (U(Int, Bool) -> Bool);
  
  //!= instead of ==:
  function (x) :: (U(Int, Bool) -> Bool) {
    if (typeof x == "boolean") {
      if (x) { return false; }
    }
    return true;
  } :: (U(Int, Bool) -> Bool);
  
  function (x) :: (U(Int, Bool) -> Bool) {
    if (typeof x != "boolean") {
      var f :: Int = 0;
      f = x >> 3;
      return true;
    }
    else
    {
      if (x) { return false; }
    }
    return true;
  } :: (U(Int, Bool) -> Bool);
  function (x) :: (U(Int, Bool) -> Bool) {
    if (typeof x != "boolean") {
      var f :: Int = 0;
      f = x >> 3;
      return true;
    }
    else
    {
      if (x) { return false; }
      var b = false;
      b = x; //x should be false here
      return true;
    }
  } :: (U(Int, Bool) -> Bool);
  
  //testing control flow:
  function (x) :: (U(Int, Bool) -> Bool) {
     if (typeof x == "number") {
       return false;
     }
     else {
       return x; //x should be Bool
     }
  } :: U(Int, Bool) -> Bool;
  
  function (x) :: (U(Int, Bool) -> Bool) {
     if (typeof x == "number") {
       return false;
     }
     return x; //x should be Bool
  } :: U(Int, Bool) -> Bool;
  
  //CATASTROPHIC FAILURES:
  //---------------------
  function (x) :: (U(Int, Bool) -> Bool) {
     if (typeof x == "number") {
       return false;
     }
     if (x) {}
     return x; //x should be Bool
  } :: U(Int, Bool) -> Bool;
  function (x) :: (U(Int, Bool) -> Bool) {
     if (typeof x == "number") {
       return false;
     }
     if (x) {3;}
     return x; //x should be Bool
  } :: U(Int, Bool) -> Bool;
  
  //y is not declared, so the following should fail:
  fail function (x) :: (U(Int, Bool) -> Bool) {
     if (typeof x == "number") {
       return false;
     }
     if (x) {
       var z = 9;
       y = z;
     }
     return x; //x should be Bool
  };

  function (x) :: (U(Int, Bool) -> Bool) {
     if (typeof x == "number") {
       return false;
     }
     if (x) {
       var z = 9;
     }
     return x; //x should be Bool
  } :: U(Int, Bool) -> Bool;
  function (x) :: (U(Int, Bool) -> Bool) {
     if (typeof x == "number") {
       var ppzzr = 10;
       return false;
     }
     if (x) {
       var z = 9;
     }
     return x; //x should be Bool
  } :: U(Int, Bool) -> Bool;
  
  function (x) :: (U(Int, Bool) -> Bool) {
     if (typeof x != "boolean") {
       return false;
     }
     if (x) {
       var z = 9;
     }
     return x; //x should be Bool
  } :: U(Int, Bool) -> Bool;
  function (x) :: (U(Int, Bool) -> Bool) {
     if (typeof x != "boolean") {
       var ppzzr = 9;
       return false;
     }
     if (x) {
       var z = 9;
     }
     return x; //x should be Bool
  } :: U(Int, Bool) -> Bool;
  
  
  function (x) :: (U(Int, Bool) -> Bool) {
    if ((typeof x) != "boolean") {
      var f :: Int = 0;
      f = x >> 3;
      return true;
    }
    if (x) { return false; }
    return true;
  } :: (U(Int, Bool) -> Bool);
  
  function (x) :: (U(Int, Bool) -> Bool) {
    if (!((typeof x) == "boolean")) {
      var f :: Int = 0;
      f = x >> 3;
      return true;
    }
    if (x) { return false; }
    return true;
  } :: (U(Int, Bool) -> Bool);
  
  //x shouldn't turn Into "false" just because of occurrence typing:
  fail function (x) :: Int -> Bool {
    if (!x)
      return x;
    return false;
  };
  
  //make sure we can filter out not only equal types:
  function (x) :: (U(Int, Bool) -> Bool) {
    return (typeof x == "number" ? (x<<3)==8 : !x);
  } :: (U(Int, Bool) -> Bool);
  
  function (x) :: (U(Int, Bool) -> Bool) {
    if (typeof x == "boolean") {
      if (x) { return false; }
    }
    return true;
  } :: (U(Int, Bool) -> Bool);
  
  function (x) :: (any -> Bool) {
    if (typeof x == "boolean") {
      if (x) { return false; }
    }
    return true;
  } :: (any -> Bool);
  
  //what if we return on the if statement branch?
  function (x) :: (U(Int, Bool) -> String) {
    if (typeof x == "boolean") {
      return "x was a Boolean";
    }
    //now, x should be an Integer
    var xshift :: Int = 5;
    xshift = x >> 3;
    return "x was an Int, here it is: " + x;
  } :: (U(Int, Bool) -> String);
  
  //what if we return on the if statement else branch?
  function (x) :: (U(Int, Bool) -> String) {
    var result :: String = "tmp";
    if (typeof x == "number") {
      result = "x is a number.";
    }
    else
    {
      result = "x is a Boolean";
      return result;
    }
  
    //x should be an Int here
    var b :: Int = 0;
    b = x << 3;
    return result + ", and x is an Int here, and it's value * 8 = " + b;
  } :: (U(Int, Bool) -> String);
  
  //these should work even with var decls:
  function (x) :: (U(String, Bool) -> String) {
    if (typeof x == "string") {
      //TODO: change var processing so that occurrence typing has an effect
      //on it!
      var z = x;
      return z;
    }
    return "was not a String";
  } :: (U(String, Bool) -> String);
  
  function (x) :: (U(Int, Bool) -> String) {
    if (typeof x == "boolean") {
      return "x was a Boolean";
    }
    //now, x should be an Integer
    var xshift :: Int = x >> 3;
    return "x was an Int, here it is: " + x;
  } :: (U(Int, Bool) -> String);
  
  function (x) :: (U(Int, Bool) -> String) {
    var result :: String = "tmp";
    if (typeof x == "number") {
      result = "x is a number.";
    }
    else
    {
      result = "x is a Boolean";
      return result;
    }
  
    //x should be an Int here
    var b :: Int = x << 3;
    return result + ", and x is an Int here, and it's value * 8 = " + b;
  } :: (U(Int, Bool) -> String);
  
  //magic
  fail function (x) :: U(Int, Bool, String) -> U(Int, Bool) {
    if ((typeof x == "number") || (typeof x == "boolean"))
    var isInt :: Int = 3;
    if ((typeof x == "number") || 3) //(typeof x == "Bool"))
    {
      isInt = x;
      return x;
    }
    return 4;
  };
  
  function (x) :: U(Int, Bool, String) -> U(Int, Bool) {
    var isUIntBool :: U(Int, Bool) = 3;
    if ((typeof x == "number") || (typeof x == "boolean"))
    {
      isUIntBool = x;
      return x;
    }
    return 4;
  } :: U(Int, Bool, String) -> U(Int, Bool);
  function (x) :: U(Int, Bool, String) -> U(Int, Bool) {
    var isUIntBool :: U(Int, Bool) = 3;
    var isStr :: String = "HAHA";
    if ((typeof x == "number") || (typeof x == "boolean"))
    {
      isUIntBool = x;
      return x;
    }
    else
      isStr = x;
    return 4;
  } :: U(Int, Bool, String) -> U(Int, Bool);
  
  //soundness plz
  function (x) :: U(Int, Bool) -> Int {
    var y = typeof x;
    if (y == "number") {
      return x;
    }
    return 10;
  } :: U(Int, Bool) -> Int;
  
  fail function (x) :: U(Int, Bool) -> Double {
    var y = typeof x; // testing y refines the type of x
    x = false; // testing y no longer refines the type of x
    if (y == "number") { // testing y should not refine the type of x
      return x; // x is still U(Int, Bool)
    }
    return 10; // this is fine
  };
  
  //more soundness tyvm
  fail function () :: (-> Int) {
    var y :: U(Int, String) = 4;
    (function() :: (-> Undefined) { y = "HAHAHA"; })();
    return y;
  };
  
  //pathological example that no one cares about:
  fail function () :: (-> Int) {
    var y :: U(Int, String) = 4;
    var z :: U(Int, String) = 19;
    (function() :: (-> Undefined) { z = "HAHAHA"; })();
    return y;
  };
  
  
  function() :: (-> Undefined) {
    var x :: U(Double, String, Bool) = "hello";
    var y :: String =
      (typeof ((typeof x == "number") ? "x is a number" : x) == "boolean")
        ? "x is a Boolean"
        : x;
  
  } :: -> Undefined;
  
  //switch statements:
  function (x) :: (U(String, Bool) -> String) {
    switch (typeof x) {
      case 'string':
        return x;
      default:
        return "was not a String";
    };
  } :: (U(String, Bool) -> String);
  
  fail function (x) :: (U(Int, String, Bool) -> Int) {
    switch (typeof x) {
      case 'number':
       return x;
       break;
      case 'string':
       return 33;
       break;
      case 'bool':
       if (x) return 0; else return 1;
       break;
    };
    return 13; // this statement is unreachable
  };
  
  function (x) :: (U(Int, String, Bool) -> Int) {
    var z :: Int = 1;
    var s :: String = "s";
    var b :: Bool = true;
    switch (typeof x) {
      case 'number':
       z = x;
       break;
      case 'string':
       s = x;
       break;
      default:
       b = x;
       break;
    };
    return 13;
  } :: U(Int, String, Bool) -> Int;
  //if equivalent:
  function (x) :: (U(Int, String, Bool) -> Int) {
    var z :: Int = 1;
    var s :: String = "s";
    var b :: Bool = true;
    if (typeof x == "number") {
      z = x;
    } else {
      if (typeof x == "string") {
        s = x;
      } else {
        b = x;
      }
    }
    return 13;
  } :: U(Int, String, Bool) -> Int;
  
  
  function (x) :: Int -> Int {
    switch (typeof x) {
      default:
       return x;
    }
  } :: Int -> Int;
  
  function (x) :: (U(Int, String, Bool) -> Int) {
    var z :: Int = 1;
    var s :: String = "s";
    var b :: Bool = true;
    switch (x) {
      case 3:
       z = x;
       break;
      case 'String':
       s = x;
       break;
    };
    return 13;
  } :: U(Int, String, Bool) -> Int;
  
  fail function (x) :: U(Int, Bool) -> Int {
    var b :: Bool = true;
    if (x == 3)
      return x;
    else
    {
      b = x; //x is still U(Int, Bool) here.
      return 5;
    }
  };

  function (x) :: U(Int, Bool) -> Int {
    if (x != 3) {
      return 4;
    }
    return x;
  } :: U(Int, Bool) -> Int;

  function (x) :: U(Int, Bool) -> Int {
    var b :: Bool = true;
    if (x == 3)
      return x;
    else {
      if (x == true)
      {
        b = x;
        return 3;
      }
      return 4;
    }
  } :: U(Int, Bool) -> Int;
  
  function(x) :: U(Int, Undefined) -> Int {
    if (typeof(x) == "undefined") {
      x = 0;
    }
    return x;
  } :: U(Int, Undefined) -> Int;
  
  //this should work!!! =(
  /*
  function (x) :: (U(Int->Bool, Bool->Int) -> Bool) {
    function Int2Bool(a) :: (Int->Bool) {
      return true;
    }
    if (x == Int2Bool)
      return x(100);
    return false;
  } :: (U(Int->Bool, Bool->Int) -> Bool);*/
  
  //&&
  function (dubfun, x) :: ((Double -> Bool), U(Double,String) -> Bool) {
    return ((typeof(x)=='number') && isNaN(x)) || false;
  } :: ((Double -> Bool), U(Double, String) -> Bool);
  function (dubfun, x) :: ((Double -> Bool), any -> Bool) {
    return ((typeof(x)=='number') && isNaN(x)) || false;
  } :: ((Double -> Bool), any -> Bool);
  
  //restricting 'any':
  function (x) :: (any -> Bool) {
    var rez :: Bool = false;
    if (typeof x == "boolean")
      rez = x;
    return rez;
  } :: (any -> Bool);
  
  function (x) :: (any -> Bool) {
    var tx = typeof x;
    if (typeof tx == "string")
      return false;
    return false;
  } :: any -> Bool
}

// type-systems 101
expressions {

  function() :: (-> Undefined) {
    var x :: Int = 5;
    var y = function() :: -> Int { return x + 5; }
  } :: -> Undefined;
  
  function() :: -> Undefined {
    var x = 5;
    var y = function() :: -> int { return x + 5; }
  } :: -> Undefined;
  
  fail function() :: -> Undefined {
    var f = function() :: -> String {
      return x;
    };
    
    var x :: U(Int, String) = 42;
  
    if (typeof x == "number") { x = "make me a string"; }
    f();
  }
}

// variables
expressions {

  function (x) :: (Double -> Double) {
    var z :: Double = 23;
    return z * x;
  } :: (Double -> Double);

  //both expr and type:
  function (x) :: (Double -> Double) {
    var z :: Double = 13;
    return z * x;
  } :: (Double -> Double);

  //mismatching expr and type:
  fail function (x) :: (Double -> Double) {
    var z :: Double = "HAHAHAHAHAHAHA";
    return z * x;
  };

  //just exprs:
  function (x) :: (Double -> Double) {
    var z = 15;
    return z * x;
  } :: (Double -> Double);

  function (x) :: (Double -> Double) {
    var y = 43;
    var z = y;
    return z * x;
  } :: (Double -> Double);
  
  fail function (x) :: (Double -> Double) {
    var z = y; // free
    var y = 13;
    return z * x;
  };
  
  function (ignore) :: (Int -> String) {
    var a = 3;
    var b = 19 + a;
    var c = "A String";
    var d = "ANOTHeR String";
    var e = (a*4 == (b - 23)) ? c : d;
  
    if (a*b == 4)
    {
        if (e == c) {
          return d;
        }
        return c;
    }
    else
        return c+d;
  } :: (Int -> String);

  function (ignore) :: (Int -> String) {
    var a = 3;
    var b = 19 + a;
    var c = "A String";
    var d = "ANOTHeR String";
    var e = (a*4 == (b - 23)) ? c : d;
  
    if (a*b == 4)
    {
        if (e == c) {
          return d;
        }
        return c;
    }
    return c+d;
  } :: (Int -> String);
  
  function (mult) :: (Double -> (Double -> Double)) {
    function inner(a) :: (Double -> Double) {
        return mult * a;
    }
    return inner;
  } :: (Double -> (Double -> Double));
  
  fail function (x) :: (Double -> Double) {
    var z = y + 9; // use-before-define error
    var y = 13;
    return y;
  };
  
  fail function (x) :: (Double -> String) {
    var y = 5;
    var y = "Stringy";
    return y;
  };
  
  fail function (x) :: (Double -> String) {
    var y = 5;
    if (true)
    {
      var y = "Stringy"; // { } do not introduce a new block
      y += "4aaa";
    }
    return y; // use before definition here
  };
  
  fail function (x) :: (Double -> String) {
    var y = 5;
    var z :: U(String,Undefined) = Undefined;
    if (true) // our dataflow analysis does not determine that the branch
              // is always taken ...
    {
      z = "Stringy";
      z += y;
    }
    // ... so, here z :: U(String, Undefined)
    return z;
  };
  
  fail function (x) :: (Double -> String?) {
    var y = 5;
    var z :: U(String,Undefined);
    if (true)
    {
      var z = "Stringy"; // duplicate declaration!
      z += y;
    }
    return z;
  };
  
  fail function (x) :: (Double -> String) {
    var x = "A String it";
    return x;
  };
  
  fail function (x) :: (Double -> String) {
    var y = "String1";
    var y = "Stringy";
    return y;
  };
  
  fail function (x) :: (Double -> String) {
    var x = x + 9;
    return x + "s";
  };
  
  function (x) :: (Double -> Double) {
    var f :: String = "captain planet";
    function doit(ahahah) :: (String -> Double) {
      var f :: Double = 15.3;
      return f * 5;
    }
    return doit(f);
  } :: (Double -> Double)
}

expressions {
  1 :: U(Int, Double);

  "hey" :: U(Double, Bool, String);
  
  function(x) :: (U(Int, Bool) -> Undefined) {
    var z = x;
    z = 34;
    z = true;
    z = false;
    z = 19;
  } :: (U(Int, Bool) -> Undefined);
  
  //magical local inference infers "bool", not "true"!
  function() :: (-> Undefined) {
    var z = true;
    z = false;
  } :: -> Undefined
}

// control flow
expressions {
  
  function() :: (-> Undefined) {
    {
      var x = 5;;;;
      var z :: Int = 23;;;
      z = x + 39;;;
    };;;;{};;{;;{;;{};}};;
  } :: (-> Undefined);

  function() :: (-> Undefined) {
    3; 9; 4 > 5; 6; 17; "string";
  } :: (-> Undefined);

  function(loop) :: (Bool -> Undefined) {
    while (loop) {
      if (4 == 9) loop = false;
      loop = true;
    }
    while(true);
    while(true){}
  } :: (Bool -> Undefined);

  function() :: (-> Undefined) {
    do { var x = 39 + 14 + "strnk"; } while (4==5 ? true : false);
  } :: (-> Undefined);

  function() :: (-> Undefined) {
    for (var i = 0; i < 2000; ++i)
    {
      //Hi Bob!
      0-0|    808;
    }
  } :: (-> Undefined);
  
  fail function() :: -> Undefined { break; };
  
  fail function() :: (-> Undefined) { stmt: for (;;) { break invalid; }};

  function() :: (-> Undefined) { 
    stmt: for (;;) { break stmt; }} :: (-> Undefined);

  fail function() :: (-> Undefined) { 
    stmt: for (;;) { continue invalid; }};

 function() :: (-> Undefined) { 
    stmt: for (;;) { continue stmt; }} :: (-> Undefined);
  
  function() :: (-> Undefined) {
    for (var a=1,b=2,c=false; c; a+=1, b-=2)
    {
      if (b < 300 && a > 45) c = true;
      if (b+a==5) continue;
      var pyu = a*b-3;
      if (pyu+"string" == "49string") break;   
    }
  } :: (-> Undefined);

  fail function() :: (-> Undefined) {
    for (i = 0; i < 300; ++i) {}
  }
}

// nullable
expressions {
  function (a) :: (Int? -> Int) {
    if (typeof a == "undefined")
      return 0;
    else
      return a * 15;
  } :: Int? -> Int;
  
  function (a) :: (Int? -> Int) {
    var x :: Int?;
    x = undefined;
    x = 5;
    x = undefined;
    if (typeof x == "undefined") {
      return 4;
    }
    else
      return x;
  } :: Int? -> Int;
  
  function (x) :: (Int? -> Int) {
    if (typeof x == "undefined") {
      return 4;
    }
    else
      return x;
  } :: Int? -> Int;
  
  fail function (a) :: (Int? -> Int) {
    var x :: Int?;
    if (typeof x == "undefined") {
      x = undefined;
      return x;
    }
    else
      return 4;
  };

  fail function () :: (-> Undefined) {
    var z :: Int = 5;
    z = undefined;
  };
  
  //works on unions:
  fail function (a) :: (U(Int, Bool)? -> U(Int, Bool)) {
    return a;
  };

  function (a) :: (U(Int, Bool)? -> U(Int, Bool)) {
    if (typeof a != "undefined")
      return a;
    return 5;
  } :: (U(Int, Bool)? -> U(Int, Bool));
  
  fail function (a) :: (Int -> Int) {
    var procInt :: (Int -> Int)?;
    return procInt(a);
  };
  
  function (a) :: (Int -> Int) {
    var procInt :: (Int -> Int)?;
    procInt = function (v) :: (Int -> Int) { return v*2; };
    return procInt(a);
  } :: (Int -> Int);
  
  function (a) :: (Int -> Int) {
    var procInt :: (Int -> Int)?;
    procInt = function (v) :: (Int -> Int) { return v*2; };
    if (typeof procInt != "undefined")
        return procInt(a);
    return 0;
  } :: (Int -> Int);
  
  //can't declare a function as nullable:
  fail function (a) :: (Int -> Int) {
    var procInt :: (Int -> Int)?;
    procInt = function (v) :: (Int -> Int)? { return v*2; };
  }
}

expressions {

  //declare before use stuff
  function () :: (-> Undefined) {
    var x :: Int = 10;
    function zorro() :: (-> Int) { return x; }
  } :: -> Undefined;
  
  function () :: (-> Undefined) {
    var x = 10;
    function zorro() :: (-> Int) { return x; }
  } :: -> Undefined;
  
  function () :: (-> Undefined) {
    var x :: Int = 10;
    function zorro() :: (-> Int) { return x; }
  } :: -> Undefined;

  fail function () :: (-> Undefined) {
    function zorro() :: (-> Int) { return x; }
    zorro();
    var x = 10;
  };
  
  fail function () :: (-> Undefined) {
    function zorro() :: (-> Int) { return x; }
    zorro();
    var x :: Int = 10;
  }

}

expressions {

  //can't assign to global 'anys'
  fail function () :: (-> Int) {
    var x :: any = 4;
    function inner() :: (-> Undefined) {
      x = "AHAH";
    };
    inner();
    return x;
  };
  
  function () :: (-> Int) {
    var x :: any = 4;
    function inner() :: (-> Undefined) {
    };
    return x;
  } :: -> Int;
  
  function () :: (-> Int) {
    var x :: any = 4;
    function inner(x) :: (any -> Undefined) {
      x = "FRFR";
    };
    inner(x);
    return x;
  } :: -> Int;
  
  function () :: (-> Int) {
    var x :: any = 4;
    function inner(x) :: (string -> Undefined) {
      x = "FRFR";
    };
    x = "he";
    inner(x);
    x = 3;
    return x;
  } :: -> Int;
  
  function () :: (-> Int) {
    var x :: U(Int, string) = 4;
    return x;
  } :: -> Int;
  
  function () :: (-> Int) {
    var x :: any = 4;
    return x;
  } :: -> Int
}

// function subtyping
expressions {
  function (b,a) :: ((Int -> Int), (Int -> Int) -> Undefined) { a = b; }
  :: (Int -> Int), (Int -> Int) -> Undefined;

  function (b,a) :: ((Int -> Int), (Int -> Double) -> Undefined) { a = b; }
  :: ((Int -> Int), (Int -> Double) -> Undefined);
  
  fail function (b,a) :: ((Int -> Double), (Int -> Int) -> Undefined) { a = b; }
}

expressions {
  function (x) :: (Double -> Double) {
  	if (x == 0)
  		return 49;
  	else if (x == 12)
  		return 15;
  	else
  		return 5;
  } :: (Double -> Double);
  
  function (x) :: (Double -> Undefined ) {
  	if (x == 0)
  		return;
  	else if (x == 12)
  		return;
  	else
  		return;
  } :: (Double -> Undefined );
  
  fail function (x) :: (Double -> Double) {
  	if (x == 0)
  		return 49;
  	else if (x == 12)
  		return;
  	else
  		return 5;
  };
  
  fail function (x) :: (Double -> Undefined ) {
  	if (x == 0)
  		return;
  	else if (x == 12)
  		return;
  	else
  		return 5;
  };
  
  function (x) :: (Double -> Undefined ) {
  } :: (Double -> Undefined );
  
  function (x) :: (Double -> Undefined ) {
  	return;
  } :: (Double -> Undefined );
  
  function (x) :: (Double -> Double ) {
  	if (x == 12)
  		x++;
  	if (x == 9)
  		--x;
  
  	return x;
  } :: (Double -> Double);
  
  function (x) :: (Double -> Undefined ) {
  } :: (Double -> Undefined);
  
  fail function (x) :: (Double -> Double ) {
  };
  
  fail function (x) :: (Double -> Double ) {
  	return;
  };
  
  fail function (x) :: (Double -> Double ) {
  	if (x == 5) return 20;
  };
  
  fail function(x) :: (Double -> Int) {
   // the type of the function is irrelevant when a path does not return
  };
  
  fail function(x) :: (Double -> Int) {
  foo: {
  	if (x == 12.0) { return 500; }
  	else { break; }
  	return 700; // unreachable, but we do not care about that right now
  }
  };
  
  fail function(x) :: (Double -> Int) {
  bar: { break;
  			 return 500; }
  };
  
  fail function (x) :: (Double -> Double ) {
  	switch (x) {
  		case 3: return 2;
  		case 4: return 12;
  	}
  };
  
  fail function (x) :: (U(Int, bool) -> bool) {
  	 if (typeof x == "number") {
  		 return false;
  	 }
  };
  
  fail function (ignore) :: (Int -> String) {
  	var a = 3;
  	var b = 19 + a;
  	var c = "A STRING";
  	var d = "ANOTHeR STRING";
  	var e = (a*4 == (b - 23)) ? c : d;
  
  	if (a*b == 4)
  	{
  			if (e == c) {
  				return d;
  			}
  			return c;
  	}
  };
  
  fail function (x) :: (Double -> Undefined ) {
  	return;
  	return;
  };
  
  fail function (x) :: (Double -> Undefined ) {
  	return;
  	return;
  	("hithere"=="" ? 'how' : 'areyou?');
  } ;
  
  fail function (x) :: (Double -> Double) {
  	if (x==3)
  		return 4;
  	else
  		return 3;
  	("hithere"=="" ? 'how' : 'areyou?');
  } ;
  
  fail function (x) :: (Double -> Double) {
  	if (x==3)
  		return 4;
  	else
  		return 3;
  	("hithere"=="" ? 'how' : 'areyou?');
  	return 2;
  } ;

  fail function (x) :: (Double -> Undefined ) {
  	if (x==3)
  		return;
  	else
  		return;
  	("hithere"=="" ? 'how' : 'areyou?');
  }
}

expressions {

  fail function () ::  -> Undefined {
    var z = myadder(3, 2);
    function myadder(a, b) :: Int, Int -> Int {
      return a+b;
    }
  };
  
  //variables assignments are not:
  fail function () ::  -> Undefined {
    var z = myadder(3, 2);
    var myadder :: Int, Int -> Int = function (a,b) :: Int, Int -> Int {
      return a+b;
    }
  };

  fail function () ::  -> Undefined {
    var z = myadder(3, 2);
    var myadder = function (a,b) :: Int, Int -> Int {
      return a+b;
    }
  };
  
  function(x) :: U(Int, String) -> String {
    var y = x;
    if (typeof y == "number")
      y = "bookr";
    return y;
  } :: U(Int, String) -> String;
  
  
  //recursive function declarations:
  function() ::  -> Undefined {
    function lawl(x) :: (Int -> Int) { return lawl(3); }
  } ::  -> Undefined;
  
  //mutually recursive function declarations:
  function() ::  -> Undefined {
    function lawl1(x) :: (Int -> Int) { return lawl2(3); }
    function lawl2(x) :: (Int -> Int) { return lawl1(3); }
  } ::  -> Undefined;
  
  fail function() ::  -> Undefined {
    function lawl1(x) :: (Int -> Int) { return lawl2(3); }
    lawl1(3);
    function lawl2(x) :: (Int -> Int) { return lawl1(3); }
  };
  
  fail function() ::  -> Undefined {
    function add(a,b) :: Int, Int -> Int {
      return a + b;
    }
    add(v, q); // use before definition
    var v = 5;
    var q = 6;
  };
  
  //vars are nullable if declared inside an if:
  fail function() :: (-> Int) {
    function add(a,b) :: Int, Int -> Int {
      return a + b;
    }
    if (false)
      var v = 10;
    if (false)
      var q = 15;
    return add(v, q);
  };
  
  function () :: -> Undefined { 
    function () ::  -> Undefined { var a = 4; }; 
  } :: -> Undefined;
  
  
  function () :: -> Undefined { 
    function () ::  -> Undefined { var a = 4; }();
  } :: -> Undefined
}
