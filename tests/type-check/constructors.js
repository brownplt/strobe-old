//should the following work?:
/*
function () :: (->) {
  function maybeobj(obj) :: {x :: int?, y :: string?} -> string {
    var z = obj.y;
    z = "broohaha!!!!!!!!!!!!!!!";
    return z;
  }
  maybeobj({});
} @@ succeeds;*/

//no-prototype constructors:
function () :: (-> int) {
  function MyObj(xVal) :: [{...}] int ~~> {x::int,y::int,...} {
    this.x = xVal;
    this.y = 0;
  }
  var o = new MyObj(5);
  return o.x + o.y;
} :: (-> int);

function () :: (-> int) {
  function MyObj(xVal) :: [{...}] int ~~> {x::int,y::int,...} {
    this = {}; //FAIL
    this.x = xVal;
    this.y = 0;
  }
  var o = new MyObj(5);
  return o.x + o.y;
} @@ fails;

//the following 3 errors are all related:
function () :: (-> int) {
  function MyObj(xVal) :: int ~~> {x::int,y::int,...} {
    this.x = xVal;
    //should fail, since 'y' has not been assigned
  }
  var o = new MyObj(5);
  return o.x + o.y;
} @@ fails;

function () :: (-> int) {
  function MyObj(xVal) :: int ~~> {x::int,y::int,...} {
    this.x = xVal;
    this.y = 0;
    this.z = "OMAGA";
    //should this fail, since 'z' is not in the returned type?
  }
  var o = new MyObj(5);
  return o.x + o.y;
} @@ fails;

function () :: (-> int) {
  function MyObj(xVal) :: int ~~> {x::int,y::int,...} {
    this.y = "HFIEF";
    this.x = xVal;
    //should fail, since incorrect types.
  }
  var o = new MyObj(5);
  return o.x + o.y;
} @@ fails;

//variations on a theme:
function () :: (-> int) {
  function MyObj(xVal) :: [{...}] int ~~> {x::U(string,int),y::int,...} {
    this.x = "phooey";
    this.y = 0;
  }
  var o = new MyObj(5);
  return o.y;
} :: (-> int);
function () :: (-> int) {
  function MyObj(xVal) :: [{...}] int ~~> {x::U(string,int),y::int,...} {
    this.x = 99;
    this.y = 0;
  }
  var o = new MyObj(5);
  return o.y;
} :: (-> int);

//the following is strange. this has a different type in the true and the
//false cases. we have to union the field together and keep 'this' as
//an object, not a union of objects. special case FTW
//we can special case cause we know 'this' cannot be assigned =).
function () :: (-> int) {
  function MyObj(y) :: [{...}] bool ~~> {x::U(string,int),y::int,...} {
    if (y)
      this.x = 99;
    else
      this.x = "O MY GOD";
    //here, this has type U({x::int},{x::string}). maybe it should be
    //{x::U(int, string)} ?
    //should really act like variablz do.

    this.y = 0;
  }
  var o = new MyObj(false);
  return o.y;
} :: (-> int);

function () :: (-> int) {
  function MyObj(y) :: [{...}] bool ~~> {x::U(string,int),y::int,...} {
    if (y)
      var krom = 99;
    else
      var krom = "O MY GOD";
    this.x = krom;
    this.y = 0;
  }
  var o = new MyObj(false);
  return o.y;
} :: (-> int);




