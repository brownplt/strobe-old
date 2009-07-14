function (x) :: (double -> double) { 
  b = x * 3;
  return b;
} @@ fails; //var not declared
function (x) :: (double -> double) { 
  x = x + 3 * 9;
  return x;
} :: (double -> double); 
function (x) :: (double -> double) { 
  x += 5;
  x /= (6 - 3 * x);
  return x;
} :: (double -> double); 
function (x) :: (double -> double) { 
  var z = x + 13;
  var y = 14 - 7;
  z /= x + y;
  return z;
} :: (double -> double);
//each of the operators succeeding:
function (x) :: (double -> double) { 
  x += 3;
  return x;
} :: (double -> double);
function (x) :: (double -> double) { 
  return (x -= x);
} :: (double -> double);
function (x) :: (double -> double) { 
  x *= 93;
  return x;
} :: (double -> double);
function (x) :: (double -> double) { 
  x /= (x += 4) + 3;
  return x;
} :: (double -> double);
function (x) :: (double -> double) { 
  x %= 2.3;
  x %= 1.4;
  return x;
} :: (double -> double);
function (x) :: (int -> int) {
  var f :: int = 23; 
  x <<= f;
  return x;
} :: (int -> int);
function (x) :: (int -> int) { 
  var f :: int = 23; 
  x >>= f;
  x >>>= f;
  return x;
} :: (int -> int);
function (x) :: (int -> int) { 
  var f :: int = 73; 
  x &= f;
  return x;
} :: (int -> int);
function (x) :: (int -> int) { 
  var f :: int = 342; 
  x ^= f;
  return x;
} :: (int -> int);
function (x) :: (int -> int) { 
  var f :: int = 9988; 
  x |= f;
  return x;
} :: (int -> int);
//the int-required ones should fail on doubles:
function (x) :: (double -> double) { 
  x <<= 4;
  return x;
} @@ fails;
function (x) :: (double -> double) { 
  x >>= 3;
  x >>>= 14;
  return x;
} @@ fails;
function (x) :: (double -> double) { 
  x &= 5;
  return x;
} @@ fails;
function (x) :: (double -> double) { 
  x ^= 13;
  return x;
} @@ fails;
function (x) :: (double -> double) { 
  x |= 29;
  return x;
} @@ fails;

// involving other types:
function (x) :: (double -> string) {
  var z = "15", y = "32";
  z += y; //should result in "1532"
  return z;
} :: (double -> string);

function (x) :: (double ->) {
  var z = true;
  z *= 5;
} @@ fails;
function (x) :: (double ->) {
  var z = "jimbababawe";
  z *= 5;
} @@ fails;

function (x) :: (double -> string) {
  x += "hah"; //the x + "hah" evaluates to a string, but then the actual assignment should fail.
  return "h";
} @@ fails;

//list expressions?
function (x) :: (double -> string) {
  var z = (4, 39, "haha", "sup dog? yes.. rather so."+x);
  return z;
} :: (double -> string);


