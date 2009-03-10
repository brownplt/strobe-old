{} :: {}; //TODO: fix testcase parser so you can have a comment on the first 
          //      line.  No, you!
//TODO: add support for new Array<int>, etc.

function (arry) :: (Array<int> -> int) {
  return (5)[13];
} @@ fails;
function (arry) :: (Array<int> -> int) {
  return arry[arry];
} @@ fails;
function (arry) :: Array<int> -> int {
  return arry[arry[0]];
} :: (Array<int>->int);

//sum:
function (arry) :: (Array<int> -> int) {
  var sum :: int = 0;
  for (var indx = 0; indx < arry.length; ++indx) {
    sum += arry[indx];
  }
  return sum;
} :: (Array<int> -> int);

//monomorphic map:
function (int2str, arry) :: ((int -> string), Array<int> -> Array<string>) {
  var rezarray :: Array<string> = ["mercury","venus","earth","...","pluto"];
  for (var i=0; i < arry.length; ++i) {
    rezarray[i] = int2str(arry[i]);
  }
  return rezarray;
} :: ((int -> string), Array<int> -> Array<string>);

//monomorphic filter:
function (int2bool, arry) :: ((int -> bool), Array<int> -> Array<int>)  {
  var rezarray :: Array<int> = [2,4,8,16];
  var ri = 0;
  for (var i=0; i < arry.length; ++i) {
    if (int2bool(arry[i]))
      rezarray[ri++] = arry[i];
  }
  return rezarray;
} :: ((int -> bool), Array<int> -> Array<int>);

//Array subtypes:
function () :: (-> Array<int>) {
  var z :: Array<int> = [1];
  var y :: Array<double> = [2.0];
  // y[0].floor() works
  y = z; // this test fails because of this assignment.
 // y[0].floor() signals a method not found exception.
  return z;
} @@ fails; //:: (-> Array<int>);

//arrays of objects:
//TODO: make these use iterators once those work.
//TODO: write a version with polymorphic map once that exists.
function (ptarray) :: (Array<{x :: int, y :: int, mag :: (-> double)}> -> Array<double>) {
  var resarray :: Array<double> = [1.23];
  for (var i=0; i < ptarray.length; ++i)
    resarray[i] = ptarray[i].mag();
  return resarray;
} :: (Array<{x :: int, y :: int, mag :: (-> double)}> -> Array<double>);

function (ptarray) :: (Array<{x :: int, y :: int, mag :: (-> double)}> -> Array<double>) {
  function map(pt2dub, arry) :: (({x :: int, y :: int, mag :: (-> double)} -> double), 
                                 Array<{x :: int, y :: int, mag :: (-> double)}> -> 
                                 Array<double>) {
    var rezarray :: Array<double> = [1.0];
    for (var i=0; i < arry.length; ++i) {
      rezarray[i] = pt2dub(arry[i]);
    }
    return rezarray;
  }

  //TODO: is really annoying to re-specify the pt type everywhere.
  return map(function (pt) :: ({x :: int, y :: int, mag :: (-> double)} -> double) { return pt.mag(); },
             ptarray);
} :: (Array<{x :: int, y :: int, mag :: (-> double)}> -> Array<double>);

//array literals
function () :: (->) {
  var z :: Array<int> = [1];
} :: (->);
function () :: (->) {
  var z :: Array<int> = [1, 2];
} :: (->);
function () :: (->) {
  var z :: Array<int> = [1, 3, 5, 19];
} :: (->);
//TODO: allow empty array literals at some point
function () :: (->) {
  var z :: Array<int> = [];
} @@ fails; 

//finding most commen supertypes:
[1, 2, 3, 4, 5] :: Array<int>;
function () :: (->) {
  var z :: Array<int> = [1, 3, 5.94, 19];
} @@ fails; //Array<double> isn't a subtype of Array<int>
function () :: (-> double) {
  var z :: Array<double> = [1, 3, 5.94, 19];
  return z[0];
} :: (-> double);
function () :: (->) {
  var z :: Array<double> = [1.4, 3.1, 5.94, 19.23];
} :: (->);
//objects, now:
function () :: (-> int) {
  var z :: Array<{x::int}> = [{x: 5}, {x: 12}, {x: 93}];
  return z[0].x + z[1].x;
} :: (-> int);
function () :: (-> int) {
  var z :: Array<{x::int}> = [{x: 5.7}, {x: 12}, {x: 93}];
  return z[0].x + z[1].x;
} @@ fails;
function () :: (-> int) {
  var z :: Array<{x::int}> = [{x: "error will robinson"}, {x: 12}, {x: 93}];
  return z[0].x + z[1].x;
} @@ fails;
//supertype even when something isnt a subtype of the other:
function () :: (-> int) {
  var z :: Array<{x::int}> = [{x: 5, z: "hiroxlmen"}, {x: 46, y: "dont matter"}, {x: 12}, {x: 93}];
  return z[0].x + z[1].x;
} :: (-> int);

function () :: (-> int) {
  // This used to be Array<undefined> and was about subtyping.
  var z :: Array<string> = [1, "hi", 43.9, true];
  return 3;
} @@ fails;

function () :: (-> int) {
  var z :: Array<int> = [1];
  return z[2];
} :: (-> int);

function () :: (-> double) {
  var z :: Array<double> = [1, 3.0];
  return z[0];
} :: (-> double);

//TODO: subtyping for functions
function () :: (->) {
  var x :: Array<string> = [1];
} @@ fails;
function () :: (->) {
  var x :: int = 5;
  var y :: Array<int> = [x, x, x, 3];
  return;
} :: (->);

[1,2,3] :: Array<int>;


