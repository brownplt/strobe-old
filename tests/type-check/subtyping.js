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

function () :: (->) {
  var p :: {point :: { ... } } = {a: '4', b: '3', c: '1gg', d: '55t'};
} @@ fails;
function () :: (->) {
  var p :: {point :: { ... } } = {point :{a: '4', b: '3', c: '1gg', d: '55t'}};
} :: (->);

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

//the readonly here is redundant for the moment, since slack implies readonly
function (b, a) :: ({p :: {x :: int, y :: int}},
                    {readonly p :: {x :: int, ... }} ->) {
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

function (b) :: (bool ->) {
  var foo :: {x :: U(int, string)} = {x : 5};
  if (b)
    foo = {x: "hi"};
  else
    foo = {x: 3};
  foo.x = 3;
} @@ fails;

function (b) :: (bool ->) {
  var foo :: {x :: U(int, string)} = {x : 5};
  var baz :: {x :: string} = {x : "hi"};

  if (b)
    foo = baz;
  else
    foo = {x: 5};

  foo.x = 3;
} @@ fails;
function (b) :: (bool ->) {
  var foo :: {x :: U(int, string)} = {x : 5};
  var baz :: {x :: string} = {x : "hi"};

  foo = {x:"hi"};
  foo.x = 3;
} @@ fails; //shrug

function (b) :: (bool ->) {
  var foo :: {x :: U(int, string)} = {x : 5 || "g"};
  //$printtype$(foo);
  if (b)
    foo.x = 3; //can't mutate to a union fieldzomg
  else
    foo.x = "NEIN";
  //$printtype$(foo);
} @@ fails;

function (b) :: (bool -> int) {
  var foo :: {x :: int, y :: int, ...} = {x:3, y:5};
  if (b)
    foo = {x:5, y:6, z:7};
  else
    foo = {x: 10, y:12};
  return foo.z;
} @@ fails;

//field subtyping...
//you can pass in sub-types as things to read from
function (reader, obj) :: forall a. (({readonly x :: a} -> a), {x::a} -> a) {
  return reader(obj);
} @@ succeeds;
function (reader, obj) :: forall animal dog : dog <: animal .
  (({readonly x :: animal} -> animal), {x::dog} -> animal) {
  return reader(obj);
} @@ succeeds;
function (reader, obj) :: forall dog animal : dog <: animal .
  (({readonly x :: dog} -> dog), {x::animal} -> dog) {
  return reader(obj);
} @@ fails;

function (reader, obj) :: forall a b : b <: a .
  (({readonly x :: a} -> a), {readonly x::b} -> a) {
  return reader(obj);
} @@ succeeds;
function (reader, obj) :: forall a b : b <: a .
  (({readonly x :: a} -> a), {writeonly x::b} -> a) {
  return reader(obj);
} @@ fails;

//super-types as things to write to
function (writer, obj) :: forall a. (({writeonly x :: a} -> ), {x::a} -> ) {
  writer(obj);
} @@ succeeds;
function (writer, obj) :: forall animal dog : dog <: animal .
  (({writeonly x :: animal} -> ), {x::dog} -> ) {
  writer(obj);
} @@ fails;
//the next one succeeds because you can write dogs into something that contains
//animals. you just can't *read* dogs because there might be animals there
//which aren't dogs.
function (writer, obj) :: forall dog animal : dog <: animal .
  (({writeonly x :: dog} -> ), {x::animal} -> ) {
  writer(obj);
} @@ succeeds;

function (writer, obj) :: forall a b : a <: b .
  (({writeonly x :: a} -> ), {writeonly x::b} -> ) {
  writer(obj);
} @@ succeeds;
function (writer, obj) :: forall a b : a <: b .
  (({writeonly x :: a} -> ), {readonly x::b} -> ) {
  writer(obj);
} @@ fails;

//and invariants as read-writable things
function (readwriter, obj) :: forall a . (({x :: a} -> a), {x :: a} -> a) {
  return readwriter(obj);
} @@ succeeds;
function (readwriter, obj) :: forall a b : b <: a .
  (({x :: a} -> a), {x::b} -> a) {
  return readwriter(obj);
} @@ fails;
function (readwriter, obj) :: forall a b : a <: b .
  (({x :: a} -> a), {x::b} -> a) {
  return readwriter(obj);
} @@ fails;

function (readwriter, obj) :: forall a .
  (({x :: a} -> a), {readonly x :: a} -> a) {
  return readwriter(obj);
} @@ fails;
function (readwriter, obj) :: forall a .
  (({x :: a} -> a), {writeonly x :: a} -> a) {
  return readwriter(obj);
} @@ fails;
