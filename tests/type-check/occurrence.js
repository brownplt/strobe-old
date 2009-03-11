function (x) :: (U(int, bool) -> bool) {
  //the typed scheme paper example
  return (isInt(x) ? (x<<3)==8 : !x);
} :: (U(int, bool) -> bool);

//make sure we can filter out not only equal types:
function (x) :: (U(int, bool) -> bool) {
  return (isDouble(x) ? (x<<3)==8 : !x);
} :: (U(int, bool) -> bool);

function (x) :: (U(int, bool, string) -> bool) {
  return (isInt(x) ? (x<<3)==8 : !x);
} @@ fails;

function (x) :: U(string, bool) -> string { return x; } @@ fails;
function (x) :: U(string, bool) -> string {
  if (true) return x;
  return "h";
} @@ fails;

function (x) :: (U(string, bool) -> string) {
  if (isString(x)) {
    //TODO: change return stmt checking so that occurrence typing has an effect
    //on it! (i.e. move it into typeCheckStmts)
    return x;
  }
  return "was not a string";
} :: (U(string, bool) -> string);

function (x) :: (U(int, bool) -> bool) {
  if (isBool(x)) { //typeof x == "boolean") {
    if (x) { return false; }
  }
  return true;
} :: (U(int, bool) -> bool);


//make sure we can filter out not only equal types:
function (x) :: (U(int, bool) -> bool) {
  return (typeof x == "number" ? (x<<3)==8 : !x);
} :: (U(int, bool) -> bool);


function (x) :: (U(int, bool) -> bool) {
  if (typeof x == "boolean") { //typeof x == "boolean") {
    if (x) { return false; }
  }
  return true;
} :: (U(int, bool) -> bool);



