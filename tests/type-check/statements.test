4 :: double;

//blocks, empties
function() :: (->) {
  {
    var x = 5;;;;
    var z :: int = 23;;;
    z = x + 39;;;
  };;;;{};;{;;{;;{};}};;
} :: (->);
//expr statements
function() :: (->) {
  3; 9; 4 > 5; 6; 17; "string";
} :: (->);
//ifs are tested elsewhere
//while loops:
function(loop) :: (bool ->) {
  while (loop) {
    if (4 == 9) loop = false;
    loop = true;
  }
  while(true);
  while(true){}
} :: (bool ->);
//do while loops
function() :: (->) {
  do { var x = 39 + 14 + "strnk"; } while (4==5 ? true : false);
} :: (->);
//for loops
function() :: (->) {
  for (var i = 0; i < 2000; ++i)
  {
    //Hi Bob!
    0-0|    808;
  }
} :: (->);

//TODO: put these tests somewhere else
/*function() :: (->) { continue; } @@ fails;
function() :: (->) { break; } @@ fails;
function() :: (->) { 
stmt: for (;;) { break invalid; }} @@ fails;
function() :: (->) { 
stmt: for (;;) { break stmt; }} :: (->);
function() :: (->) { 
stmt: for (;;) { continue invalid; }} @@ fails;
function() :: (->) { 
stmt: for (;;) { continue stmt; }} :: (->);*/

function() :: (->) {
  for (var a=1,b=2,c=false; c; a+=1, b-=2)
  {
    if (b < 300 && a > 45) c = true;
    if (b+a==5) continue;
    var pyu = a*b-3;
    if (pyu+"string" == "49string") break;   
  }
} :: (->);
function() :: (->) {
  for (i = 0; i < 300; ++i) {}
} @@ fails; //i is not defined
