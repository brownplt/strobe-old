1 :: U(int, double);
"hey" :: U(double, bool, string);

function(x) :: (U(int, bool) -> ) {
  var z = x;
  z = 34;
  z = true;
  z = false;
  z = 19;
} :: (U(int, bool) ->);

//magical local inference infers "bool", not "true"!
function() :: (->) {
  var z = true;
  z = false;
} :: (->);

//empty union? is stupid.
function(x) :: (U() -> string) {
  var z = 3;
  if (x) {
    return x;
  }
  return x;
} @@ succeeds;


