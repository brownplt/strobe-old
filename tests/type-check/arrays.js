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
  }
}
  
