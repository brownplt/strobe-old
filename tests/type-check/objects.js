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
                trace: function(s) :: this :: Object:, String -> Undefined { 
                         return; },
                warning: function(s) :: this :: Object:, String -> Undefined { 
                           return; } },
      storage : { extract: function(s) :: (String -> String) { return s; },
                  openText: function(s) :: (String -> String) { return s; } } };
  
    var debugfunc = gadget.debug.warning;
    var extractfunc = gadget.storage.extract;
    // debugfunc(extractfunc("NUMBER_PROCESSORS"));
    // debugfunc("The number of RAMs is: " + extractfunc("MEMORY_SIZE"));
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

body { Object.prototype.x = 93 }

body {
  Object.prototype.x = 93;
  var v :: Int = (5).x.x.x.x.x.x.x;
}
  
body {
    Object.prototype.x = 93;
    var v :: Int = (5).x.x.x.x.x.x.x.x.x.x.x;
}
  
body {
  Object.prototype.x = 93;
  var v :: Int = (5).x.x.x.x.x.x.x + (12).x.x;
}

body {
  Object.prototype.x = 93;
  var obj :: { x :: Int, y :: Int } = { y : 900 };
  var z :: Int = obj.x;
}

body {
  Object.prototype.x = 93;
  var obj = { y : 900 };
  var z :: Int = obj.x;
}

body {
  Object.prototype.x = 93;
  var obj :: { x :: Int } = { y : 900 }; 
  var z :: Int = obj.x;
}

body {
  Object.prototype.x = 93;
  var obj :: { } = { y : 900 }; 
  var z :: Int = obj.x;
}

body {
  Object.prototype.x = { z : 3.14159 };
  var s :: Double = (10).x.z.x.z.x.z.x.z;
}

body {
  Object.prototype.x = { z : 3.14159 };
  var obj = (10).x; 
  var s :: Double = obj.z;
}

body {
  Object.prototype.x = { z : 3.14159 };
  var obj :: { z :: Double } = (10).x; 
  var s :: Double = obj.z;
}

body fail {
  Object.prototype.x = { z : 3.14159 };
  var obj :: {} = (10).x; 
  // The Object brand does not have a field z.  So, if obj is declared to 
  // have type  {}, that field is effectively hidden and obj.z fails below.
  var s :: Double = obj.z;
}

body {
  var obj :: { y :: Int } = { y : 900 };
  Object.prototype.x = 93;
  var z :: Int = obj.x; // requires an intersection
}

body fail {
  var obj :: { y :: Int } = { y : 900 };
  var g :: Int = obj.x; // hasn't been added yet
  Object.prototype.x = 93;
  var z :: Int = obj.x;
}

body {
  var f = function(obj) :: { x :: Int, y :: String } -> String {
    return obj.y;
  };

  f({ x : 45, y : "hello" });
  Object.prototype.y = "I AM THE PROTOTYPE";
  f({ x : 90 });
}

body fail {
  var f = function(obj) :: { x :: Int, y :: String } -> String {
    return obj.y;
  };

  f({ x : 90 }); // y not added yet
  Object.prototype.y = "I AM THE PROTOTYPE";
}

body {
  var f = function(obj) :: { x :: Int, y :: String } -> String {
    return obj.y;
  };

  Object.prototype.y = 92;
  f({ x : 70, y : "field override, or something" });
}

body fail {
  var f = function(obj) :: { x :: Int, y :: String } -> String {
    return obj.y;
  };

  Object.prototype.y = 92;
  f({ x : 70 }); // prototype.y has the wrong type
}


body fail {
  var f = function(obj) :: { x :: Int, y :: String } -> String {
    return obj.y;
  };

  Object.prototype.y = 92;
  Object.prototype.y = "we could support this if we wanted to";
  f({ x : 70 });
}

body {
   Object.prototype.x = 34;
   // Without constraints, x :: Int is filled in.
   var f = function(obj) :: {} -> Int {
     return obj.x;
   }
}

body {
   Object.prototype.x = 34;
   // same as above
   var f = function(obj) :: Object: -> Int {
     return obj.x;
   }
}

body {
   Object.prototype.x = 34;
   // explicit constraint override the prototype
   var f = function(obj) :: { x :: String } -> String {
     return obj.x;
   }
}

body fail {
   // x :: Int is not declared yet, so it is not filled in.
   var f = function(obj) :: {} -> Int {
     return obj.x;
   }
   Object.prototype.x = 34;
}

expressions {

  succeed function(obj) :: { either :: U (Int, String) } -> Undefined {
    obj.either = "should win";
  };

  // Type refinement does not work within mutable record fields ...
  fail function() :: -> Undefined {
    var x :: U(Int, String) = 42;
    var foo :: { either :: U(Int, String) } = { either: x };
    if (typeof (foo.x) == "string") {
      var y :: String = foo.x;
    }
  };

  // ... therefore, the following example is okay
  succeed function() :: -> Undefined {
    var changeType = function(o) :: { either :: U(Int, String) } -> Undefined {
      o.either = "string.i.am";
    };

    var x :: U(Int, String) = 42;
    var foo :: { either :: U(Int, String) } = { either: x };

    changeType(foo);
  };

  succeed function() :: (-> Undefined) {
  
    // z <: y
    var z :: { field :: Int, field2 :: Int } = { field: 50, field2: 9000 } ;
    var y :: { field :: Int } = { field: 50 };
  
    var t :: Int = y.field;
    y = z; // this assignment should succeed
  
    t = y.field;
  };

  fail function() :: (-> Undefined) {
  
    // we do not have z <: y, since subtyping of array elements is invariant
    var z :: [{ field :: Int, field2 :: Int }]
      = [ { field: 50, field2: 9000 }  ];
    var y :: [{ field :: Int }] = [ { field: 50 } ];
  
    var t :: Int = y[0].field;
    y = z; // this assignment fails
  };


  fail function() :: (-> Undefined) {
  
  	// we do not have z <: y, since mutable fields are invariant for subtyping.
  	var z :: {x :: { field :: Int, field2 :: Int }} =
  		{x : {field: 50, field2: 9000 } };
  	var y :: {x :: { field :: Int }} =
  		{x : {field: 50 }};
  
  	var t :: Int = y.x.field;
  	y = z; // this assignment fails  
  };
  
  succeed function() :: (-> Undefined) {
  
  	// we have z <: y
  	var z :: {readonly x :: { field :: Int, field2 :: Int }} =
  		{x : {field: 50, field2: 9000 } };
  	var y :: {readonly x :: { field :: Int }} =
  		{x : {field: 50 }};
  
  	var t :: Int = y.x.field;
  	y = z; // this assignment succeeds
  };

  succeed function() :: (-> Undefined) {
  
  	// we have z <: y
  	var z :: {readonly x :: { field :: Int, field2 :: Int }} =
  		{x : {field: 50, field2: 9000 } };
  	var y :: {readonly x :: { field :: Int }} =
  		{x : {field: 50 }};
  
  	var t :: Int = y.x.field;
  	y = z;
    y.x.field = 999;
  
  };

  fail function() :: (-> Undefined) {
  
  	// we have z <: y
  	var z :: {readonly x :: { field :: Int, field2 :: Int }} =
  		{x : {field: 50, field2: 9000 } };
  	var y :: {readonly x :: { field :: Int }} =
  		{x : {field: 50 }};
  
  	var t :: Int = y.x.field;
  	y = z;
    y.x = { field : 999 }; 
  
  }

}


body {
    Object.prototype.x = { };
    var x :: {} = {};
}


body {
    Object.prototype.x = { };
    var x :: {} =  {}.x.x.x.x.x;
}

body {
    Object.prototype.x = { };
    var obj = {};
    while (obj.x) { 
      obj = obj.x;
    }
}

body {
    Object.prototype.x = { };
    var obj = {};
    do {
      obj = obj.x;
    } while (obj.x);
}

