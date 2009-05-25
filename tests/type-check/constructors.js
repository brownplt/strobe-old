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

//prototypes!!!!!!!11
function () :: (-> int) {
  function Point(x,y) :: int, int ~~> {x::int, y::int,...} {
    this.x = x;
    this.y = y;
  }
  Point.prototype.summed = function () :: [{x::int, y::int}] -> int {
    return this.x + this.y;
  };
  var p = new Point(10, 12);
  return p.summed();
} :: (-> int);

function () :: (-> int) {
  function Point(x,y) :: int, int ~~> {x::int, y::int,...} {
    this.x = x;
    this.y = y;
  }
  var p = new Point(10, 12);
  var res = p.summed();
  Point.prototype.summed = function () :: [{x::int, y::int}] -> int {
    return this.x + this.y;
  };
  return res;
} @@ fails;

function () :: (-> int) {
  function Point(x,y) :: [{summed :: ([{x::int, y::int}] -> int), ...}] int, int
                      ~~> {x::int, y::int,mag::int,...} {
    this.x = x;
    this.y = y;
    this.mag = this.summed();
  }
  Point.prototype.summed = function () :: [{x::int, y::int}] -> int {
    return this.x + this.y;
  };
  var p = new Point(10, 12);
  return p.mag;
} :: (-> int);

//we can't create an object until we assign summed, though:
function () :: (-> int) {
  function Point(x,y) :: [{summed :: ([{x::int, y::int}] -> int), ...}] int, int
                      ~~> {x::int, y::int,mag::int,...} {
    this.x = x;
    this.y = y;
    this.mag = this.summed();
  }
  var p = new Point(10, 12);
  return p.mag;
} @@ fails;

//soundness:
//the next case is uber hacked around atm by disallowing assigning a
// TPrototype to a non-ANF var.
function () :: (-> int) {
  function Point(x,y) :: int, int ~~> {x::int, y::int,...} {
    this.x = x;
    this.y = y;
  }
  var pp = Point.prototype;
  var Point = function (x,y) :: int, int ~~> {x::int, y::int,...} {
    this.x = x;
    this.y = y;
  }
  pp.summed = function () :: [{x::int, y::int}] -> int {
    return this.x + this.y;
  };
  var p = new Point(10, 12);
  return p.summed();
} @@ fails;

function () :: (-> {x::int,y::int,summed::(->string)}) {
  function Point(x,y) :: int, int ~~> {x::int, y::int,summed::(->string)...} {
    this.x = x;
    this.y = y;
    this.summed = function () :: (->string) { return "HAHAHA"; };
  }
  //the next line should fail because it conflicts with the constructed this
  //type
  Point.prototype.summed = function () :: [{x::int, y::int}] -> int {
    return this.x + this.y;
  };
  var p = new Point(10, 12);
  return p;
} @@ fails;

