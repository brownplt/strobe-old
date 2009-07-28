expressions {
    
  succeed function() :: (-> Undefined) {
    var x :: Array[Int] = [ ];
  };
  
  succeed function() :: (-> Undefined) {
    var x :: Array[Int] = [1, 2, 3, 4, 5];
    var y = x[23];
    var l = x.length;
  };
  
  fail function (arry) :: Array[Int] -> Int {
    return (5)[13];
  };

  fail function (arry) :: (Array[Int] -> Int) {
    return arry[arry];
  };

  succeed function (arry) :: Array[Int] -> Int {
    return arry[arry[0]];
  }
}
  
