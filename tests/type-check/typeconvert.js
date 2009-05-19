function() :: (-> string) {
  var x :: int = 12;
  return x.toString();
} @@ succeeds;
function() :: (-> string) {
  var x :: string = "z12";
  return x.toString();
} @@ succeeds;
function() :: (-> string) {
  var x :: double = 12.3;
  return x.toString();
} @@ succeeds;
function() :: (-> string) {
  var x :: double = 12.3;
  return x.toString();
} @@ succeeds;
function() :: (-> string) {
  var x :: bool = true;
  return x.toString();
} @@ succeeds;

function () :: (-> string) {
  var x :: int = 5;
  var myobj :: {haha :: (-> string)} = {haha : x.toString};
  myobj.haha();
} @@ fails; //invalid 'this' type for myobj.haha()

function () :: (-> string) {
  var x :: int = 5;
  var myobj :: {haha :: ([String] -> string)} = {haha: x.toString};
} @@ fails; //this types are not compatible

function () :: (->) {
  var x :: int = 5;
  var myobj :: {haha :: ([Number] -> string)} = {haha: x.toString};
} @@ succeeds; //this types are compatible

function () :: (-> string) {
  var x :: int = 5;
  var myobj :: {haha :: ([Number] -> string)} = {haha: x.toString};
  myobj.haha();
} @@ fails; //this type is incorrect when actually calling the function
            //haha expects a 'Number' as this, but it gets a 'myobj'
function () :: (-> string) {
  var x :: int = 5;
  var myobj = {haha: x.toString};
  myobj.haha();
} @@ fails; //same case as above

function () :: (->) {
  var x :: int = 5;
  var myobj = {haha: x.toString};
  (5).toString = (4324).toString;
} @@ succeeds; //no harm done here

function () :: (->) {
  var x :: int = 5;
  var myobj = {haha: x.toString};
  (5).toString = myobj.haha;
  x.toString = myobj.haha;
} @@ succeeds;

function () :: (-> string) {
  //bug: if you happen to make a structural sub-type of number,
  //our type-checker will let it through, but pJS will throw a type error!
  var z = 5;

  var omg :: Number = {
    toExponential: z.toExponential,
    toFixed: z.toFixed,
    toPrecision: z.toPrecision,
    toString: z.toString,
    toLocaleString: z.toLocaleString,
    valueOf: z.valueOf};
  return omg.toString();
} @@ fails;

