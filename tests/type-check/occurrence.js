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



