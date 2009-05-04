function() :: (->) {
  document.title = "this should work";
} @@ succeeds;

function() :: (->) {
  document.title = 234234;
} @@ fails;

function() :: (->) {
  document.write("Calling a method succeeds.");
} @@ succeeds;

function() :: (->) {
  // This code may work in the browser.  However, it is always safe to reject
  // code.
  var m = document.write;
  m("Failure because this is wrong.");
} @@ fails;
