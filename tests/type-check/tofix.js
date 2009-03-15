function () :: (->) {
  var a :: nonexistent?;
} @@ fails;
function () :: (->) {
  var b :: Array<int, int>?;
} @@ fails;
function () :: (->) {
  var b :: Array<>?;
} @@ fails;
function () :: (->) {
  var b :: Array<faketype>?;
} @@ fails;

