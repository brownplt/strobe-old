//
type intmathfunc :: int -> int;
type event :: ->;
type objtostr1 ::  -> string;
type objtostr2 :: ( -> string);

type justanint :: ((((int))));

type mapint2str :: (a -> b), Array<a> -> Array<b>;
//this parses, too, although it has a different meaning:
type mapint2str :: a -> b, Array<a> -> Array<b>;

type f :: (int, int?, int... ->);
type f :: (int, int?, int?, a?, int... ->);

function hithere(a, b, c) ::  int, int, int?, string?, Array<int>... -> double<int<{}>>,int -> int {}

//type badfunc :: A?, B..., C... -> ;
//type a :: a b c -> d;

type fff :: a -> b -> c;
