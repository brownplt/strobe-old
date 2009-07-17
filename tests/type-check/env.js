//type-environment checks:

function () :: (->) { //non-existent type names:
  var a :: nonexistent?;
} @@ fails;
function (a) :: (thesetypesdontexist ->) {
}  @@ fails;
function () :: (->) {
  var b :: Array<faketype>?;
} @@ fails;

//kinds:
function () :: (->) {
  var b :: Array<int, int>?;
} @@ fails;
function () :: (->) {
  var b :: Array<>?;
} @@ fails;

