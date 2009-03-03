succeeds {
  function add(x,y) :: int, int -> int {
    return x+y;
  }
}
{
  if (add(10,12) != 22) {
    throw "epic fail";
  }
};

blames "client" {
  function add(x,y) :: int, int -> int {
    return x+y;
  }
}
{
  add("ten","eleven");
};

blames "client" {
  var add = function(x,y) :: int, int -> int {
    return x;
  }
  var z = add(4, 5); //undefined, undefined);
}
{
  add(undefined, undefined);
};

blames "client" {
  var add = function(x,y) :: int, int -> int {
    return x+y;
  }
  var z = add(14, 19); //undefined, undefined);
}
{
  add(undefined, undefined);
};

//TODO: add code that would compile 'y' into an actual array
succeeds {
  var return1st = function(x,y) :: int, int... -> int {
    return x;
  };
}
{
  return1st(43);
  return1st(43, 31, 1, 9,4, 5, 2, 3);
};

blames "chocolate" {
  function foo() :: -> int {
    throw "chocolate violated the contract; haha funny";
  }
}
{
  foo();
};

//easily repeatable test case, for speed testing:
blames "client" { function add(x,y) :: int, int -> int { return x+y; } } { add(3.4, 10); };

