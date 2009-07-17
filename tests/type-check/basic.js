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
    //we only get here if something is whacked out
    return 13;
  };
  
  function (x) :: (U(Int, String, Bool) -> Int) {
    var z :: Int = 1;
    var s :: String = "s";
    var b :: Bool = true;
    switch (typeof x) {
      case 'number':
       z = x;
       break;
      case 'String':
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
