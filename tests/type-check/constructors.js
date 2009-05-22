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
  function MyObj(xVal) :: int ~~> {x::int,y::int} {
    this.x = xVal;
    this.y = 0;
  }
  var o = new MyObj(5);
  return o.x + o.y;
} :: (-> int);

//no-prototype constructors:
function () :: (-> int) {
  function MyObj(xVal) :: int ~~> {x::int,y::int} {
    this.x = xVal;
    //should fail, since 'y' has not been assigned
  }
  var o = new MyObj(5);
  return o.x + o.y;
} @@ fails;




