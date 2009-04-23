45 :: double;

(true ? 4 : 5) :: double;
(true ? "hi there" : "bob jones") :: string;
(true ? "HELLO" : 6) :: U(int, string);
(function (a) :: (double -> double) { return a; }) :: (double -> double);
(function (a) :: (double -> double) { return a; })(20) :: double;
(function (a) :: (double -> double) { return a+5; })(20) :: double;

function(x,x) :: int, int -> int {
  return x;
} @@ fails;

//addition and various ops.
//the following will likely stay the same:
5 + "4" :: string;
"5" + 34 :: string;
"blah" + "hoomegl" :: string;
5.03 >> 3 @@ fails; //required int for binary ops
5.0 >> 3 @@ fails;
5e9 >> 7 @@ fails;

4 / 343 :: double;

true && false :: bool;
true && (false || true) :: bool;
true && ((6 == 7) || (9 == 13)) :: bool;
true && x @@ fails;

//the following may change:
4 / "home" @@ fails;
4 * "3" @@ fails;
5 + 4 :: double; //should be 'int'
4 * 3 :: double;
//5 && 6 @@ fails; //we no longer require bools
4 / "13" @@ fails;
4 + (function(x) :: (double ->) { return; }) @@ fails;
true && (3 || false) @@ fails;
(3 == 0) + 10 @@ fails;
//
(function (x) :: (double ->) { return; }) :: (double ->);
(function (x) :: (double ->) { return; }) :: (double ->);
(function (x) :: (double ->) { return 5; }) @@ fails;

(function (x) :: ( ->) { return; }) @@ fails; //argument # mismatch
(function () :: (int ->) { return; }) @@ fails; //argument # mismatch
(function (x) :: (int -> int) { return "HAH"; }) @@ fails; //wrong return type
(function (x) :: (int -> int) { return; }) @@ fails; //wrong return type

//-----------------------------
//Taken from CS173's typecheck:
//-----------------------------
3.0 :: double;
// (test (type-of (parse 'nempty)) (t-nlist))
true :: bool;
false :: bool;

x @@ fails; //unbound ID

(function (a) :: (double -> bool) { return a==0; })(20) :: bool;
(function (a) :: (double -> bool) { return a; })(20) @@ fails;

(1 + 2) :: double;
(1 * 9 + 3) :: double;
4 + (9 - 5) :: double;
(9 * 10 - 11 - 12 - 13) == 0 :: bool;

(9 == 0) + (9 - 5) @@ fails;

(0 == 0) ? (10 + 9) : (9 - 30) :: double;
(0 ==0 ) ? true : false :: bool;

0 == 0 ? 10 + 9 : 9 - x @@ fails;
0 == 0 ? (3 == 0) + 10 : 9 - 30 @@ fails;
0 == 0 ? 9 + 10 : 10 == 0 :: U(bool, int);
0 == 0 ? 10 == 0 : 9 + 10 :: U(bool, int);
0 == 0 ? true : 9 - 30 :: U(bool, int);
//20 + 9 ? 10 + 9 : 9 - 30 @@ fails; //no longer require bools
(4 == 0) == 0 ? 9 + 10 : 9 - 30 :: double;
(function (a) :: (double -> bool) {
   return a == 0; })(4 == 0) ? 9 + 10 : 9 - 30 @@ fails;
(function (a) :: (double -> bool) {
   return a == 0; })(4) ? 9 + 10 : "blerK" :: U(int, string);


(function (x) :: (double -> double) { return x; }) :: (double -> double);
(function (x) :: (string -> double) { return x; }) @@ fails;
(function (x) :: (string -> double) { return 43; }) :: (string -> double);

(function (x) :: (string -> double) {
    return (x == "") ? 0 : 1; }) :: (string -> double);
(function (x) :: (string -> bool) {
    return (x == "")}) :: (string -> bool);

//more complicated functions:
(function (x) :: (double -> (double -> double)) {
    return (function (y) :: (double -> double) {
              return x * y; }); }) :: (double -> (double -> double));
(function (x) :: (double -> (double -> double)) {
    return (function (y) :: (double -> double) {
              return x * z; }); }) @@ fails; //z is not defined
(function (x) :: (double -> (string -> double)) {
    return (function (x) :: (string -> double) {
              return (x=="" ? 5 : 10); }); }) :: (double -> (string -> double));
(function (x) :: (string -> double) {
    return x;}) @@ fails; //expected string, got double

//applying functions
4 (20) @@ fails; //can't apply non-function
"moileben"("stringy machine") @@ fails;

(function (x) :: (double -> (double -> double)) {
    return (function (y) :: (double -> double) {
              return x * y; }); })(33) :: (double -> double);
(function (x) :: (double -> (double -> double)) {
    return (function (y) :: (double -> double) {
              return x * y; }); })(33)(29) :: double;

//TODO: add testing w/  arrays, once we get those:
(function (x) :: (double -> double) { return x; })("45") @@ fails;
(function (x) :: (string -> bool) { return x==""; })("45") :: bool;
(function (x) :: (string -> bool) { return x==""; })(45) @@ fails;

//NOTE: functional programming is ugly in javascript...
(function (toapp) :: ((double -> string) -> (double -> string)) {
    return (function (x) :: (double -> string) {
              return toapp(x); })}) ::
      ((double -> string) -> (double -> string));

(function (toapp) :: ((double -> string) -> (double -> string)) {
    return (function (x) :: (double -> string) { return toapp(x); })})
  (function (n) :: (double -> string) { return ""+n;}) :: (double -> string);
(function (toapp) :: ((double -> string) -> (double -> string)) {
    return (function (x) :: (double -> string) { return toapp(x); })})
  (function (n) :: (double -> string) { return ""+n;})(93) :: string;

/*
;some more list ops, then more intricate testing
;isnempty
(test (type-of (parse '{nempty? nempty}))
      (t-bool))
(test/exn (type-of (parse '{nempty? {* 3 4}})) "expected nlist")
(test/exn (type-of (parse '{* 3 {nempty? nempty}})) "expected two numbers")

(test (type-of (parse '{ncons 1 {ncons 2 {ncons 3 {ncons 4 nempty}}}}))
      (t-nlist))

(test/exn (type-of (parse '{ncons {ncons {ncons {ncons 4 5} 6} 7} 8})) "expected nlist")
(test/exn (type-of (parse '{ncons {ncons {ncons {ncons 4 nexmpty} 6} 7} 8})) "No type binding")
(test/exn (type-of (parse '{ncons {ncons {ncons {ncons 4 nempty} 6} 7} 8})) "expected number")

(test (type-of (parse '{nfirst {ncons {nfirst nempty} nempty}})) (t-num))
(test/exn (type-of (parse '{nfirst {ncons {nfirst 100000000} nempty}})) "expected nlist")

(test (type-of (parse '{nrest {ncons 2 {ncons 2 nempty}}})) (t-nlist))
(test/exn (type-of (parse '{nrest {nfirst {ncons 2 {ncons 2 nempty}}}})) "expected nlist")

;;crazy test
(test (type-of (parse '{with {madapp : (nlist -> (nlist -> ((nlist -> number) -> ((number -> nlist) -> ((nlist -> number) -> nlist)))))
                                     {fun {srclist : nlist}  : (nlist -> ((nlist -> number) -> ((number -> nlist) -> ((nlist -> number) -> nlist))))
                                          {fun {restlist : nlist} : ((nlist -> number) -> ((number -> nlist) -> ((nlist -> number) -> nlist)))
                                               {fun {app1 : (nlist -> number)} : ((number -> nlist) -> ((nlist -> number) -> nlist))
                                                    {fun {app2 : (number -> nlist)} : ((nlist -> number) -> nlist)
                                                         {fun {app3 : (nlist -> number)} : nlist
                                                              {ncons {app3 {nrest {app2 {- {app1 srclist} 49}}}} restlist}}}}}}}
                             {{{{{madapp {ncons {+ 1 {nfirst nempty}} {ncons {/ 9 4} nempty}}}
                                         {ncons {* 3 1} {with {x : nlist {nrest nempty}} x}}}
                                         {fun {l   : nlist}  : number {nfirst {nrest {nrest l}}}}}
                                         {fun {num : number} : nlist  {bif {zero? {- num {* 4 num}}}
                                                                           nempty
                                                                           {ncons num {ncons num nempty}}}}}
                                         {fun {l   : nlist}  : number {bif {nempty? l}
                                                                           42
                                                                           {nfirst l}}}}}))
      (t-nlist))

(test/exn (type-of (parse '{with {madapp : (nlist -> (nlist -> ((nlist -> number) -> ((number -> nlist) -> ((nlist -> number) -> nlist)))))
                                     {fun {srclist : nlist}  : (nlist -> ((nlist -> number) -> ((number -> nlist) -> ((nlist -> number) -> nlist))))
                                          {fun {restlist : nlist} : ((nlist -> number) -> ((number -> nlist) -> ((nlist -> number) -> nlist)))
                                               {fun {app1 : (number -> number)} : ((number -> nlist) -> ((nlist -> number) -> nlist))
                                                    {fun {app2 : (number -> nlist)} : ((nlist -> number) -> nlist)
                                                         {fun {app3 : (nlist -> number)} : nlist
                                                              {ncons {app3 {nrest {app2 {- {app1 srclist} 49}}}} restlist}}}}}}}
                             {{{{{madapp {ncons {+ 1 {nfirst nempty}} {ncons {/ 9 4} nempty}}}
                                         {ncons {* 3 1} {with {x : nlist {nrest nempty}} x}}}
                                         {fun {l   : nlist}  : number {nfirst {nrest {nrest l}}}}}
                                         {fun {num : number} : nlist  {bif {zero? {- num {* 4 num}}}
                                                                           nempty
                                                                           {ncons num {ncons num nempty}}}}}
                                         {fun {l   : nlist}  : number {bif {nempty? l}
                                                                           42
                                                                           {nfirst l}}}}}))
      "")

(test/exn (type-of (parse '{with {madapp : (nlist -> (nlist -> ((nlist -> number) -> ((number -> nlist) -> ((nlist -> number) -> nlist)))))
                                     {fun {srclist : nlist}  : (nlist -> ((nlist -> number) -> ((number -> nlist) -> ((nlist -> number) -> nlist))))
                                          {fun {restlist : nlist} : ((nlist -> number) -> ((number -> boolean) -> ((nlist -> number) -> nlist)))
                                               {fun {app1 : (nlist -> number)} : ((number -> nlist) -> ((nlist -> number) -> nlist))
                                                    {fun {app2 : (number -> nlist)} : ((nlist -> number) -> nlist)
                                                         {fun {app3 : (nlist -> number)} : nlist
                                                              {ncons {app3 {nrest {app2 {- {app1 srclist} 49}}}} restlist}}}}}}}
                             {{{{{madapp {ncons {+ 1 {nfirst nempty}} {ncons {/ 9 4} nempty}}}
                                         {ncons {* 3 1} {with {x : nlist {nrest nempty}} x}}}
                                         {fun {l   : nlist}  : number {nfirst {nrest {nrest l}}}}}
                                         {fun {num : number} : nlist  {bif {zero? {- num {* 4 num}}}
                                                                           nempty
                                                                           {ncons num {ncons num nempty}}}}}
                                         {fun {l   : nlist}  : number {bif {nempty? l}
                                                                           42
                                                                           {nfirst l}}}}}))
      "")
*/

(3 == 0)(13) @@ fails; //expected a function
(x == 0)(13) @@ fails; //x not declared

(function (x) :: (double -> (double -> double)) {
  return (function (z) :: (double -> double) {
    return x + z; })})(4)(3) :: double;
(function (x) :: (double -> double) {
  return (function (z) :: (double -> double) {
    return x + z; })})(4)(3) @@ fails;
(function (x) :: (double -> double) {
  return x + x;})(4)(3) @@ fails;

(function (a) :: (->) {return;}) @@ fails;

/*
;silly us
(test (type-of (parse '{{{fun {x : number} : (number -> number) {fun {z : number} : number {+ x z}}} 4} 3})) (t-num)) ;this works
(test/exn (type-of (parse '{{{fun {x : number} : number {fun {z : number} : number {+ x z}}} 4} 3})) "expected result type") ;wrong return type
(test/exn (type-of (parse '{{{fun {x : number} : number {+ x x}} 4} 3})) "expected a function")*/

//simple things that should succeed. test for when this doesn't matter
4 @@ succeeds;
3 @@ succeeds;

function (x) :: (string -> ) {
  return;
} @@ succeeds;




