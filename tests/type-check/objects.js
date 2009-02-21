{} :: {};
{x: 5} :: {x :: int};
{x :: int : 5} :: {x :: int};
{x :: double : 5} :: {x :: double};

{point :: {x::int,y::int} : {x:5, y:3}} :: {point :: {x::int,y::int}};

//dotrefs
function (point) :: ({x::int, y::int} -> double) {
  var sqrt = function(x) :: (double -> double) { return x*x; }; // lol not
  var magnitude = point.x * point.x + point.y * point.y;
  return sqrt(magnitude);
} :: ({x :: int, y :: int} -> double);
function (point) :: ({x::int, y::int} -> double) {  
  var sqrt :: (double -> double);
  var magnitude = point.x * point.x + point.y * point.y + point.z * point.z;
  return sqrt(magnitude);
} @@ fails;

//more nested objects
function() :: (->) {
  // This sucks, but is not necessary!
  var gadget :: {
    debug :: {
      error :: (string -> ),
      trace :: (string->),
      warning :: (string ->),
    },
    storage :: {
      extract :: (string -> string),
      openText :: (string -> string),
    }} = { debug : { error: function(s) :: (string ->) { return; },
                      trace: function(s) :: (string ->) { return; },
                      warning: function(s) :: (string ->) { return; } },
           storage : { extract: function(s) :: (string -> string) { return s; },
                       openText: function(s) :: (string -> string) { return s; } } };

  var debugfunc = gadget.debug.warning;
  var extractfunc = gadget.storage.extract;
  //disclaimer: the following function calls are meaningless
  debugfunc(extractfunc("NUMBER_PROCESSORS"));
  debugfunc("The number of RAMs is: " + extractfunc("MEMORY_SIZE"));
  gadget.debug.warning("You are being warned.");
  gadget.debug.trace = gadget.debug.error;
  gadget.debug.trace("This is showing an error, because I messed around with the functions.");
} :: (->);
  

//TODO: add test cases using toString et. al., once inheritance from base object is done

//TODO: allow number properties? 
{0: '3', 4: 4} @@ succeeds; //there is no way to write out this type

//duplicates in literals:
{z: 5, 5: 6, 5: 9} @@ fails;

//duplicates in types:
{point :: {x::int,x::int} : {x:5}} @@ fails;

function() :: (->) {
  var z :: {name :: int, name :: string, name :: double};
  //z = 4;
} @@ fails;
function() :: (->) {
  var z :: {name :: int, name :: int};
} @@ fails;
