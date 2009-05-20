function () :: (->) {
  var pt = {x:1, y:5, z:13};
  for (x in pt) x;
} @@ fails; //undeclared var
function () :: (->) {
  var pt = {x:1, y:5, z:13};
  for (x in 5);
} @@ fails; //not iterating in a proper object

function () :: (->) {
  var pt = {x:1, y:5, z:13};
  for (var x in pt);
} :: (->);

function () :: (->) {
  var pt = {x:1, y:5, z:13};
  var pt2 = {x:10, y:10, z:100};
  for (var x in pt) {
    pt2[x] = pt[x];
  }
} :: (->);

function () :: (->) {
  var pt = {x:1, y:true, z:"stringy"};
  var pt2 = {x:10, y:false, z:"alsostring"};
  for (var x in pt) {
    pt2[x] = pt[x];
  }
} :: (->);

function () :: (->) {
  var pt = {x:"mismatching types eh", y:5, z:"stringy"};
  var pt2 = {x:10, y:10.3, z:"alsostring"};
  for (var x in pt) {
    pt2[x] = pt[x];
  }
} @@ fails;

function () :: (->) {
  function mutatestr(o) :: ({foo :: string} ->) {
    o.foo = "HAHAHAH";
  }
  var pt = {x:1, y:2};
  var res = "";
  for (var x in pt) {
    mutatestr({foo: x});
    res += pt[x];
  }
} @@ fails;

function () :: (->) {
  var pt = {x:1.3, y:5.9, z:13};
  var pt2 = {x:10, y:10, z:100};
  for (var x in pt) {
    pt2[x] = pt[x];
  }
} @@ fails;

//toJSON:
function() :: (->) {
function toJSON_placeholder(object) :: any -> string? { return "x"; }
function toJSON(object) :: any -> string? {
  function isElement(o) :: any -> bool { return false; }
  var ret :: string? = "null<string>";

  //#*($RJH#*(RU*(#* now we have a parsing error #*($#*( great *(#*(#*#
  /*if (((typeof object) === "undefined") || ((typeof object) === "function") ||
      ((typeof object) === "unknown"))
  {
    ret = "null<string>";
  }
  else*/ if (object === "replace with null or undefined") {
    ret = "null";
  }
  else if (typeof object === "boolean") {
    ret = object ? "true" : "false"; //return object.toString();
  }
  //else if (object.toJSON) { //TODO: this wont work
  //  ret = object.toJSON();
  //}
  else if (isElement(object)) { //from "Object"
    ret = "null<string>";
  }
  else {
    //todo: need way to represent 'generic object' - can be refined
    //by doing (typeof object === "object")
    //or specified as A <: {} in the function header.
    //then need a way to represent an iterator over that object.
    //then we can do this:
    var results :: Array<string> = ["placeholder"];
    for (var property in object) {
      var value :: string?;
      value = toJSON_placeholder(object[property]);
      //if (value!==null<string>) //!(typeof value === "undefined"))
      //  results.push(escapeString(property) + ': ' + value);
    }

    function joinresults(a,split) :: Array<string>, string -> string {
      return "this would join a together";
    }

    ret = '{' + joinresults(results, ', ') + '}';
  }
  return ret;
}

} :: (->);

//extract all keys
  function(object) :: ({} -> Array<string>) {
    var keys = ["placeholder"];
    var i = 0;
    for (var property in object)
    {
      keys[i] = (property);
      i = i + 1;
    }
    return keys;
  } :: ({} -> Array<string>);



