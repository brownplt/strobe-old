function () :: (-> int) {
    function inner(arry) :: (int... -> int) {
        var sum :: int = 0;
        for (var indx = 0; indx < arry.length; ++indx) {
            sum += arry[indx];
        }
        return sum;
    }
    inner(1, 2, 3, 4, 5);
    inner(9, 2, 3);
    inner();
    return inner(1,1,1,1,1,12,4342,424,24354,54,4324234,34234,3);
} :: (-> int);

//sum the 'x' values:
function (withx) :: ({x :: double}... -> double) {
  var rez = 0.0;
  for (var i=0; i < withx.length; ++i)
    rez += withx[i].x;
  return rez;
} :: ({x :: double}... -> double);
function (withx) :: ({x :: double} -> double) {
  var rez = 0.0;
  for (var i=0; i < withx.length; ++i)
    rez += withx[i].x;
  return rez;
} @@ fails;

//due to object fields being invariant, this next case now fails:
function () :: (-> double) {
  var ultrarez :: double = 0;
  function sumx(withx) :: ({x :: double}... -> double) {
    var rez = 0.0;
    for (var i=0; i < withx.length; ++i)
      rez += withx[i].x;
    return rez;
  };

  ultrarez += sumx();
  ultrarez += sumx({x: 13});
  ultrarez += sumx({x: 3.2});
  ultrarez += sumx({x: 1}, {x: 3.2}, {x: -43.1e2});
  ultrarez += sumx({x: 1, y: 41}, {x: 3.2, z: (3 + "string")}, {x: -43e2, ijustdont: "giveadarn"});
  return ultrarez;
} @@ fails;

function () :: (-> double) {
  var ultrarez :: double = 0;
  function sumx(withx) :: ({x :: double}... -> double) {
    var rez = 0.0;
    for (var i=0; i < withx.length; ++i)
      rez += withx[i].x;
    return rez;
  };

  ultrarez += sumx();
  ultrarez += sumx({x: 13.1});
  ultrarez += sumx({x: 3.2});
  ultrarez += sumx({x: 1.41}, {x: 3.2}, {x: -43.1e2});
  ultrarez += sumx({x: 1.31, y: 41}, {x: 3.2, z: (3 + "string")}, {x: -43e2, ijustdont: "giveadarn"});
  return ultrarez;
} :: ( -> double);



(function (withx) :: ({x :: double} -> double) {
  var rez = 0.0;
  for (var i=0; i < withx.length; ++i)
    rez += withx[i].x;
  return rez;
})({y: 19}) @@ fails;
(function (withx) :: ({x :: double} -> double) {
  var rez = 0.0;
  for (var i=0; i < withx.length; ++i)
    rez += withx[i].x;
  return rez;
})({x: 4}, {x: "stringy"}) @@ fails;

//apply a series of math functions to a number
//TODO: function supertypes
(function (num, funcs) :: (double, (double -> double)... -> double) {
  for (var i = 0; i < funcs.length; ++i) {
    num = funcs[i](num);
  }

  return num;
})(39.4,
   function (x) :: (double -> double) { return x*2; },
   function (x) :: (double -> double) { return x / x + 9; },
   function (x) :: (double -> double) { return -x; },
   function (x) :: (double -> double) { return -(-2 * (-3 - (-4 * x)))},
   function (x) :: (double -> double) { return 21.0; },
   function (x) :: (double -> double) { return 2*x; }) :: double;