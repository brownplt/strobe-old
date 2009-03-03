1 :: U(int, double);
"hey" :: U(double, bool, string);

function(x) :: (U(int, bool) -> ) {
  var z = x;
  z = 34;
  z = true;
  z = false;
  z = 19;
} :: (U(int, bool) ->);
//TODO: should "var z = true;" have z's type be bool, or true?