expressions {
    
  succeed function() :: (-> Undefined) {
    var x :: [Int] = [ ];
  };

  succeed function(arr) :: [Int] -> Int {
    return arr.length;
  };
  
  succeed function(arr) :: [Int] -> Int {
    return arr[9000];
  };
    
  succeed function() :: (-> Undefined) {
    var x :: [Int] = [1, 2, 3, 4, 5];
    var y = x[23];
    var l = x.length;
  };
  
  fail function (arry) :: [Int] -> Int {
    return (5)[13];
  };

  fail function (arry) :: ([Int] -> Int) {
    return arry[arry];
  };

  succeed function (arry) :: [Int] -> Int {
    return arry[arry[0]];
  };

  succeed function (arry) :: ([Int] -> Int) {
    var sum :: Int = 0;
    for (var indx = 0; indx < arry.length; ++indx) {
      sum += arry[indx];
    }
    return sum;
  };

  succeed function (Int2str, arry) :: ((Int -> String), [Int] -> [String]) {
    var rezarray :: [String] = ["mercury","venus","earth","...","pluto"];
    for (var i=0; i < arry.length; ++i) {
      rezarray[i] = Int2str(arry[i]);
    }
    return rezarray;
  }

}

// map and various incorrect definitions of map
expressions {

  succeed function (f,src) :: forall a b . (a -> b), [a] -> [b] {
    var dest :: [b] = [ ];
    for (var i = 0; i < src.length; i++) {
      dest[i] = f(src[i]);
    };
    return dest;
  };
  
  fail function (f,src) :: forall a b . (a -> b), [a] -> [b] {
    var dest :: [b] = [ ];
    for (var i = 0; i < src.length; i++) {
      dest[i] = f(src[i]);
    };
    return src;
  };

  fail function (f,src) :: forall a b . (a -> b), [a] -> [b] {
    var dest :: [b] = [ ];
    for (var i = 0; i < src.length; i++) {
      dest[i] = f(dest[i]);
    };
    return dest;
  }

}

expressions {
  
  succeed function (Int2bool, arry) :: ((Int -> Bool), [Int] -> [Int])  {
    var rezarray :: [Int] = [];
    var ri = 0;
    for (var i=0; i < arry.length; ++i) {
      if (Int2bool(arry[i]))
        rezarray[ri++] = arry[i];
    }
    return rezarray;
  };

  fail function () :: (-> [Int]) {
    var z :: [Int] = [1];
    var y :: [Double] = [2.0];
    y = z;
    // The assignment above should fail.  Suppose we had the following code:
    //
    //   y[0] = 7.3
    //
    // Since y and z are now aliased, z[0] = 7.3, violating the type z :: [Int].
    return z;
  };

  //array literals
  succeed function () :: (-> Undefined) {
    var z :: [Int] = [1];
  };

  succeed function () :: (-> Undefined) {
    var z :: [Int] = [1, 2];
  };

  succeed function () :: (-> Undefined) {
    var z :: [Int] = [1, 3, 5, 19];
  };

  succeed function () :: (-> Undefined) {
    var z :: [Int] = [];
  };

  succeed function() :: -> [Int] {
    return [1, 2, 3, 4, 5];
  };
  
  // Testing canonical union.
  [1, 2, 3, 4, 5] :: [Int];
  [1.2, 3, 5] :: [U(Int, Double)];

  fail function () :: (-> Undefined) {
    var z :: [Int] = [1, 3, 5.94, 19];
  };

  succeed function () :: (-> Double) {
    var z :: [Double] = [1, 3, 5.94, 19];
    return z[0];
  };

  succeed function () :: (-> Undefined) {
    var z :: [Double] = [1.4, 3.1, 5.94, 19.23];
  };

  succeed function () :: (-> Int) {
    var z :: [{x::Int}] = [{x: 5}, {x: 12}, {x: 93}];
    return z[0].x + z[1].x;
  };

  fail function () :: (-> Int) {
    var z :: [{x::Int}] = [{x: 5.7}, {x: 12}, {x: 93}];
    return z[0].x + z[1].x;
  };

  fail function () :: (-> Int) {
    var z :: [{x::Int}] = [{x: "error will robinson"}, {x: 12}, {x: 93}];
    return z[0].x + z[1].x;
  };

  succeed function () :: (-> Int) {
    var z :: [{ x::Int }] = [{x: 5, z: "hiroxlmen"}, {x: 46, y: "dont matter"},
                             {x: 12}, {x: 93}];
    return z[0].x + z[1].x;
  };

  succeed function () :: (-> Double) {
    var z :: [Double] = [1, 3.0];
    return z[0];
  };
  
  succeed function () :: (-> Undefined) {
    var x :: Int = 5;
    var y :: [Int] = [x, x, x, 3];
    return;
  };
  
  succeed function (start, end) :: (Int, Int -> [Int]) {
    var r :: [Int] = [];
    for (var i = start; i < end; i++) {
      r.push(i);
      r[0] = r[i] + r[0];
    }
    return r;
  }
    
}
