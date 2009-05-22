function (x) :: (double -> double) {
  if (x == 0)
    return 49;
  else if (x == 12)
    return 15;
  else
    return 5;
} :: (double -> double);

function (x) :: (double -> ) {
  if (x == 0)
    return;
  else if (x == 12)
    return;
  else
    return;
} :: (double -> );

function (x) :: (double -> double) {
  if (x == 0)
    return 49;
  else if (x == 12)
    return;
  else
    return 5;
} @@ fails;

function (x) :: (double -> ) {
  if (x == 0)
    return;
  else if (x == 12)
    return;
  else
    return 5;
} @@ fails;



function (x) :: (double -> ) {
} :: (double -> );

function (x) :: (double -> ) {
  return;
} :: (double -> );

function (x) :: (double -> double ) {
  if (x == 12)
    x++;
  if (x == 9)
    --x;

  return x;
} :: (double -> double);

function (x) :: (double -> ) {
} :: (double ->);

function (x) :: (double -> double ) {
} @@ fails;

function (x) :: (double -> double ) {
  return;
} @@ fails;

function (x) :: (double -> double ) {
  if (x == 5) return 20;
} @@ fails;

function(x) :: (double -> int) {
 // the type of the function is irrelevant when a path does not return
} @@ fails;

function(x) :: (double -> int) {
foo: {
  if (x == 12.0) { return 500; }
  else { break; }
  return 700; // unreachable, but we do not care about that right now
}
} @@ fails;

function(x) :: (double -> int) {
bar: { break;
       return 500; }
} @@ fails;


function (x) :: (double -> double ) {
  switch (x) {
    case 3: return 2;
    case 4: return 12;
  }
} @@ fails;

//not all paths returning:
function (x) :: (U(int, bool) -> bool) {
   if (typeof x == "number") {
     return false;
   }
} @@ fails; //not all paths return

function (ignore) :: (int -> string) {
  var a = 3;
  var b = 19 + a;
  var c = "A STRING";
  var d = "ANOTHeR STRING";
  var e = (a*4 == (b - 23)) ? c : d;

  if (a*b == 4)
  {
      if (e == c) {
        return d;
      }
      return c;
  }
} @@ fails; //not all paths return

function (x) :: (double -> ) {
  return;
  return;
} @@fails;

function (x) :: (double -> ) {
  return;
  return;
  ("hithere"=="" ? 'how' : 'areyou?');
} @@ fails;

function (x) :: (double -> double) {
  if (x==3)
    return 4;
  else
    return 3;
  ("hithere"=="" ? 'how' : 'areyou?');
} @@ fails;

function (x) :: (double -> double) {
  if (x==3)
    return 4;
  else
    return 3;
  ("hithere"=="" ? 'how' : 'areyou?');
  return 2;
} @@ fails;
function (x) :: (double -> ) {
  if (x==3)
    return;
  else
    return;
  ("hithere"=="" ? 'how' : 'areyou?');
} @@ fails;

