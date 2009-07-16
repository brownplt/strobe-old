relations {
  Int = Int;
  fail Int = Bool;
  Int = U(Int, Int);
  Int = U(Int, Int, Int);
  U(Int, Bool) = U(Bool, Int);
  Int <: Int;
  Int <: U(Int, Int);
  U(Int, Int) <: Int;
  Int <: Double;
  fail Double <: Int;
  Double = U(Double, Int);
  fail Int = U(Double, Int);
  Int <: U(Int, String);
  String <: U(Int, String);
  U(Int, String) <: U(Int, String, Bool);
  fail U(Int, String, Bool) <: U(Int, String)
}

expressions {
  45 :: Double;
  (true ? 4 : 5) :: Double;
  (true ? "hi there" : "bob jones") :: String;
  (true ? "HELLO" : 6) :: U(Int, String);
  (function (a) :: Double -> Double { return a; }) :: Double -> Double;
  (function (a) :: Double -> Double { return a; })(20) :: Double;
  (function (a) :: Double -> Double { return a+5; })(20) :: Double;
  fail (function(x,x) :: Int, Int -> Int { return x; });

  5 + "4" :: String;
  "5" + 34 :: String;
  "blah" + "hoomegl" :: String;
  fail 5.03 >> 3;
  fail 5.0 >> 3;
  fail 5e9 >> 7;
  fail -"arjun";
  -5  :: Int;
  -7.3  :: Double;
  4 / 343 :: Double;
  
  true && false :: Bool;
  true && (false || true) :: Bool;
  true && ((6 == 7) || (9 == 13)) :: Bool;
  fail true && x;
  
  fail 4 / "home";
  fail 4 * "3";
  5 + 4 :: Double; // subtype test
  4 * 3 :: Double;
  fail 4 / "13";
  fail 4 + (function(x) :: Double -> Undefined { return; });
  fail (3 == 0) + 10;
  
  (function (x) :: Double -> Undefined { return; }) :: Double -> Undefined;
  (function (x) :: Double -> Undefined { return; }) :: Double -> Undefined;
  fail (function (x) :: (Double -> Undefined) { return 5; });
  
  fail (function (x) :: -> Undefined { return; });
  fail (function () :: Int -> Undefined { return; });
  fail (function (x) :: Int -> Int { return "HAH"; });
  fail (function (x) :: Int -> Int { return; });

  //-----------------------------
  //Taken from CS173's typecheck:
  //-----------------------------
  3.0 :: Double;
  // (test (type-of (parse 'nempty)) (t-nlist))
  true :: Bool;
  false :: Bool;
  
  fail x ; //unbound ID
  
  (function (a) :: (Double -> Bool) { return a==0; })(20) :: Bool;
  fail (function (a) :: (Double -> Bool) { return a; })(20) ;
  
  (1 + 2) :: Double;
  (1 * 9 + 3) :: Double;
  4 + (9 - 5) :: Double;
  (9 * 10 - 11 - 12 - 13) == 0 :: Bool;

  fail (9 == 0) + (9 - 5);
  
  (0 == 0) ? (10 + 9) : (9 - 30) :: Double;
  (0 ==0 ) ? true : false :: Bool;
  
  fail 0 == 0 ? 10 + 9 : 9 - x ;
  fail 0 == 0 ? (3 == 0) + 10 : 9 - 30 ;
  0 == 0 ? 9 + 10 : 10 == 0 :: U(Bool, Int);
  0 == 0 ? 10 == 0 : 9 + 10 :: U(Bool, Int);
  0 == 0 ? true : 9 - 30 :: U(Bool, Int);
  (4 == 0) == 0 ? 9 + 10 : 9 - 30 :: Double;
  
  fail (function (a) :: (Double -> Bool) { return a == 0; })
    (4 == 0) ? 9 + 10 : 9 - 30;
  (function (a) :: (Double -> Bool) {
     return a == 0; })(4) ? 9 + 10 : "blerK" :: U(Int, String);
  
  
  (function (x) :: (Double -> Double) { return x; }) :: (Double -> Double);
  fail (function (x) :: (String -> Double) { return x; }) ;
  (function (x) :: (String -> Double) { return 43; }) :: (String -> Double);
  
  (function (x) :: (String -> Double) {
      return (x == "") ? 0 : 1; }) :: (String -> Double);
  (function (x) :: (String -> Bool) {
      return (x == "")}) :: (String -> Bool);
  //more complicated functions:
  (function (x) :: (Double -> (Double -> Double)) {
      return (function (y) :: (Double -> Double) {
                return x * y; }); }) :: (Double -> (Double -> Double));
  fail (function (x) :: (Double -> (Double -> Double)) {
      return (function (y) :: (Double -> Double) {
                 return x * z; }); }) ; //z is not defined
  (function (x) :: (Double -> (String -> Double)) {
      return (function (x) :: (String -> Double) {
                return (x=="" ? 5 : 10); }); }) :: (Double -> (String -> Double));
  fail (function (x) :: (String -> Double) {
       return x;}) ; //expected String, got Double
  
  //applying functions
  fail 4 (20) ; //can't apply non-function
  fail "moileben"("Stringy machine") ;
  
  (function (x) :: (Double -> (Double -> Double)) {
      return (function (y) :: (Double -> Double) {
                return x * y; }); })(33) :: (Double -> Double);
  (function (x) :: (Double -> (Double -> Double)) {
      return (function (y) :: (Double -> Double) {
                return x * y; }); })(33)(29) :: Double;
  
  //TODO: add testing w/  arrays, once we get those:
  fail (function (x) :: (Double -> Double) { return x; })("45") ;
  (function (x) :: (String -> Bool) { return x==""; })("45") :: Bool;
  fail (function (x) :: (String -> Bool) { return x==""; })(45) ;
  
  //NOTE: functional programming is ugly in javascript...
  (function (toapp) :: ((Double -> String) -> (Double -> String)) {
      return (function (x) :: (Double -> String) {
                return toapp(x); })}) ::
        ((Double -> String) -> (Double -> String));
  
  (function (toapp) :: ((Double -> String) -> (Double -> String)) {
      return (function (x) :: (Double -> String) { return toapp(x); })})
    (function (n) :: (Double -> String) { return ""+n;}) :: (Double -> String);
  (function (toapp) :: ((Double -> String) -> (Double -> String)) {
      return (function (x) :: (Double -> String) { return toapp(x); })})
    (function (n) :: (Double -> String) { return ""+n;})(93) :: String;
  
  fail (3 == 0)(13) ; //expected a function
  fail (x == 0)(13) ; //x not declared
  
  (function (x) :: (Double -> (Double -> Double)) {
    return (function (z) :: (Double -> Double) {
      return x + z; })})(4)(3) :: Double;
  fail (function (x) :: (Double -> Double) {
    return (function (z) :: (Double -> Double) {
       return x + z; })})(4)(3) ;
  fail (function (x) :: (Double -> Double) {
     return x + x;})(4)(3) ;
  
  fail (function (a) :: (-> Undefined) {return;}) ;
  
  //simple things that should succeed. test for when this doesn't matter
  4 :: Int;
  3 :: Int;
  
  function (x) :: String -> Undefined {
    return;
  } :: String -> Undefined
  
}  
