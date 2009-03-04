function (x) :: (U(int, bool) -> bool) {
  //the typed scheme paper example"
  return (isInt(x) ? (x<<3)==8 : !x);
} :: (U(int, bool) -> bool);

