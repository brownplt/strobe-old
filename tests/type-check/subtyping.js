function (b,a) :: ((int -> int), (int -> int) ->) { a = b; } @@ succeeds;
//function sub-typing.
//a = b works iff b is a subtype of a
//co-variant return types:
function (b,a) :: ((int -> int), (int -> double) ->) { a = b; } @@ succeeds;
function (b,a) :: ((int -> double), (int -> int) ->) { a = b; } @@ fails;
function (b,a) :: ((int -> {x::string}), (int -> { ... }) ->) { a = b; } @@ succeeds;
function (b,a) :: ((int -> {}), (int -> {x::string}) ->) { a = b; } @@ fails;

//contra-variant arg types:
function (b,a) :: ((double -> int), (int -> int) ->) { a = b; } @@ succeeds;
function (b,a) :: ((int -> int), (double -> int) ->) { a = b; } @@ fails;

//TODO: various things w/ req args, opt args, etc:

function (b,a) :: (Array<int>, Array<double> ->) { a = b; } @@ succeeds;

function (b,a) :: (Array<int>, Array<double> ->) {
  a = b;
  a[0] = 3.4;
} @@ fails; 

function (b,a) :: (Array<double>, Array<double> ->) { a = b; } @@ succeeds;
function (b,a) :: (Array<double>, Array<int> ->) { a = b; } @@ fails;

function (b,a) :: (Array<int>, Array<double> ->) {
    a = b;
    a[0] = 19.43;
} @@ fails;
function (b,a) :: ({x::int,y::int}, {x::double}->) {
    a = b;
    a.x = 3.41;
} @@ fails;

//objects:
//object subtyping:
{x:5} :: {... };
{point: {x: 10.0, y: 13.9}} :: { ... };

//{x :: int : 5} :: {x :: double};
//{point :: {x::int,y::int} : {x:5, y:3}} :: {point :: {x::int,y::double}};
//{point :: {x::int,y::int} : {x:5, y:3}} :: {point :: {x::double,y::int}};
//{point :: {x::int,y::int} : {x:5, y:3}} :: {point :: {y::double,x::double}};

{point :: {x::int,y::int} : {x:5.3, y:3}} @@ fails;
{point :: {x::int,y::int} : {z:13, y:3}} @@ fails;
{point :: {x::int,y::int ... } : {z:5.3, y:3, x: 334}} @@ succeeds;

{point :: { ... } : {a: '4', b: '3', c: '1gg', d: '55t'}} :: {point :: { ... }};

function (b,a) :: ({x::int,y::int}, {x::int, ... }->) {
    a = b;
    a.x = 3;
} @@ succeeds;

function (b,a) :: ({x::int,y::int}, {x::int }->) {
    a = b;
    a.x = 3;
} @@ fails;

function () :: (->) {
  var arrb :: Array<{x::int,y::int}> = [{x:5,y:6}];
  arrb[0] = {x:5};
} @@ fails;
function () :: (->) {
  var a :: {x :: int} = {x: 5};
  var arrb :: Array<{x::int,y::int}> = [{x:5}];
  a = arrb[0];
} @@ fails;

//invariant-in-the-field subtyping
function (b, a) :: ({p :: {x :: int, y :: int}}, {p :: {x :: double}} ->) {
  a = b;
  a.p.x = 3.41;
} @@ fails;
function (b, a) :: ({x :: int, y :: int}, {x :: int, ... } ->) {
  a = b;
  a.x = 3;
} @@ succeeds;

function (b, a) :: ({p :: {x :: int, y :: int}}, {p :: {x :: int, ... }} ->) {
  a = b;
  a.p.x = 3;
} @@ succeeds;

//union subtyping
function (b,a) :: (U(int, bool), int->) { a = b; } @@ fails;
function (b,a) :: (U(int, double), double->) { a = b; } @@ succeeds;
function (b,a) :: (U(int, bool), U(int, bool)->) { a = b; } @@ succeeds;

0 == 0 ? true : 9 - 30 :: U(bool, int);
0 == 0 ? true : 9 - 30 :: U(bool, int);
0 == 0 ? true : 9 - 30 :: U(bool, int);

//with 'any':
function (b,a) :: (U(int, bool, string), any->) { a = b; } @@ succeeds;
function (b,a) :: (any, any->) { a = b; } @@ succeeds;
function (b,a) :: (any, U(int, bool, string)->) { a = b; } @@ fails;

// object field assignment
function() :: (->) {
  var obj = { x : 234, y : "hello" };

  obj.x = 9000;
} @@ succeeds;
