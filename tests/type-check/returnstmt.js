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

function (x) :: (double -> double ) {
} @@ fails;
function (x) :: (double -> double ) {
  if (x == 5) return 20;
} @@ fails;

function (x) :: (double -> double ) {
  switch (x) {
    case 3: return 2;
    case 4: return 12;
  }
} @@ fails;

//Questionable cases: should tJS fail these, because it has code that is impossible to be executed? (like java does)
function (x) :: (double -> ) {
  return;
  return;
} :: (double -> );
function (x) :: (double -> ) {
  return;
  return;
  ("hithere"=="" ? 'how' : 'areyou?');
} :: (double -> );
function (x) :: (double -> double) {
  if (x==3)
    return 4;
  else
    return 3;
  ("hithere"=="" ? 'how' : 'areyou?');
} :: (double -> double);
function (x) :: (double -> ) {
  if (x==3)
    return;
  else
    return;
  ("hithere"=="" ? 'how' : 'areyou?');
} :: (double -> );

