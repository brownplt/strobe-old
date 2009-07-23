relations {
  { z :: String } <: { z :: String };
  Object:{z :: String } <: Object:{ z :: String };
  { x :: Int, y :: Bool } <: { x :: Int };
  { x :: Int, y :: String } = { y :: String, x :: Int };
  // Fields are mutable by default.
  fail { x :: { f1 :: Int, f2 :: String } } 
       <: { x :: { f1 :: Int } };
  { readonly x :: { f1 :: Int, f2 :: String } } 
  <: { readonly x :: { f1 :: Int } };
  fail { readonly x :: { f :: Int } }
  <: { x :: { f :: Int } };
  { x :: { f :: Int } }
  <: { readonly x :: { f :: Int } }
  
}

expressions {
  { } :: {};
  { x: 5 } :: {x :: Int};
  { x: 5 } :: {x :: Int};
  { x: 5.0 } :: {x :: Double};
  fail { x : 9, x : 10 };
  
  { point: { x:5, y: 3} } :: {point :: {x::Int,y::Int}};


  function (point) :: {x::Int, y::Int} -> Double {
    var sqrt = function(x) :: Double -> Double { return x*x; }; // lol not
    var magnitude = point.x * point.x + point.y * point.y;
    return sqrt(magnitude);
  } :: {x :: Int, y :: Int} -> Double;


  fail function (pt) :: ({x::Int, y::Int} -> Double) {
    var sqrt = function(x) :: Double -> Double { return x*x; }; // lol not
    var magnitude = pt.x * pt.x + pt.y * pt.y + pt.z * pt.z; // z does not exist
    return sqrt(magnitude);
  };

  function() :: -> Undefined {
    var gadget = {
      debug : { error: function(s) :: String -> Undefined { return; },
                trace: function(s) :: (String -> Undefined) { return; },
                warning: function(s) :: (String -> Undefined) { return; } },
      storage : { extract: function(s) :: (String -> String) { return s; },
                  openText: function(s) :: (String -> String) { return s; } } };
  
    var debugfunc = gadget.debug.warning;
    var extractfunc = gadget.storage.extract;
    debugfunc(extractfunc("NUMBER_PROCESSORS"));
    debugfunc("The number of RAMs is: " + extractfunc("MEMORY_SIZE"));
    gadget.debug.warning("You are being warned.");
    gadget.debug.trace = gadget.debug.error;
    gadget.debug.trace("This is showing an error, because I messed around with the functions.");
  } :: -> Undefined

}

expressions {
  
  function (obj) :: {readonly x :: Int} -> Int {
    return obj.x;
  } :: {readonly x :: Int} -> Int;

  fail function (obj) :: {readonly x :: Int} -> Int {
    obj.x = 3;
    return obj.x;
  };
  
  function (obj) :: { x :: Int } -> Int {
    obj.x  = 900;
    return obj.x;
  } :: { x :: Int} -> Int
  
}

expressions {

  succeed function (b,a) :: (Int -> {x::String}), (Int -> { }) -> Undefined
          { a = b; };

  fail function (b,a) :: (Int -> {}), (Int -> {x::String}) -> Undefined
  { a = b; };

  succeed function (b,a) :: ((Double -> Int), (Int -> Int) -> Undefined) 
  { a = b; };
  
  fail function (b,a) :: ((Int -> Int), (Double -> Int) -> Undefined)
  { a = b; }
}
