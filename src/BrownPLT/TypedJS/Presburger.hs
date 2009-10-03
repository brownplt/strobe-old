{-|
  From
  http://hackage.haskell.org/packages/archive/presburger/0.3/doc/html/src/
    Data-Integer-Presburger.html

  BSD3 code

 Copied so that we can create open terms
-}
module BrownPLT.TypedJS.Presburger
  ( check, simplify, Formula(..), Term (FreeVar), (.*), is_constant
  , PP(..), closeFormula, freeVars
  ) where


import qualified Data.IntMap as Map
import Data.Maybe(fromMaybe)
import Data.List(nub,foldl')
import Control.Monad(mplus,guard)
import Prelude hiding (LT,EQ)
import qualified Data.Set as S
import Text.PrettyPrint.HughesPJ


-- | Check if a formula is true.
check :: Formula -> Bool
check f = eval_form (pre (True,0) f)

simplify :: Formula -> Formula
simplify f = invert (pre (True,0) f)

-- Sugar -----------------------------------------------------------------------


infixl 3 :/\:
infixl 2 :\/:
infixr 1 :=>:

infix 4 :<:, :<=:, :>:, :>=:, :=:, :/=:, :|


-- Forst-oreder formulas for Presburger arithmetic.
data Formula  
  = Formula :/\: Formula
  | Formula :\/: Formula
  | Formula :=>: Formula
  | Not Formula
  | Exists (Term -> Formula)
  | Forall (Term -> Formula)
  | TRUE
  | FALSE
  | Term :<:   Term
  | Term :>:   Term
  | Term :<=:  Term
  | Term :>=:  Term
  | Term :=:   Term
  | Term :/=:  Term
  | Integer :| Term

freeVars :: Formula -> S.Set String
freeVars f = case f of
  f1 :/\: f2 -> S.union (freeVars f1) (freeVars f2)
  f1 :\/: f2 -> S.union (freeVars f1) (freeVars f2)
  f1 :=>: f2 -> S.union (freeVars f1) (freeVars f2)
  Not f1 -> freeVars f1
  TRUE -> S.empty
  FALSE -> S.empty
  t1 :<: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  t1 :>: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  t1 :<=: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  t1 :>=: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  t1 :=: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  t1 :/=: t2 -> S.union (freeVarsTerm t1) (freeVarsTerm t2)
  otherwise -> error "plz dont do that"

freeVarsTerm :: Term -> S.Set String
freeVarsTerm (FreeVar s) = S.singleton s
freeVarsTerm _ = S.empty

substTerm :: String -> Term -> Term -> Term
substTerm o x (FreeVar s)
  | o == s = x
  | otherwise = (FreeVar s)
substTerm o x t = t

subst :: String -> Term -> Formula -> Formula
subst o x f = case f of
  f1 :/\: f2 -> (subst o x f1) :/\: (subst o x f2)
  f1 :\/: f2 -> (subst o x f1) :\/: (subst o x f2)
  f1 :=>: f2 -> (subst o x f1) :=>: (subst o x f2)
  Not f1 -> subst o x f1
  TRUE -> TRUE
  FALSE -> FALSE
  Forall fn -> Forall (\arg -> (subst o x (fn arg)))
  t1 :<: t2 -> (substTerm o x t1) :<: (substTerm o x t2)
  t1 :>: t2 -> (substTerm o x t1) :>: (substTerm o x t2)
  t1 :<=: t2 -> (substTerm o x t1) :<=: (substTerm o x t2)
  t1 :>=: t2 -> (substTerm o x t1) :>=: (substTerm o x t2)
  t1 :=: t2 -> (substTerm o x t1) :=: (substTerm o x t2)
  t1 :/=: t2 -> (substTerm o x t1) :/=: (substTerm o x t2)
  otherwise -> error "plz dont do that in subst"

closeFormula :: Formula -> [String] -> Formula
closeFormula f [] = f
closeFormula f (o:os) = Forall (\x -> subst o x (closeFormula f os))

pre :: (Bool,Int) -> Formula -> Form
pre n form = case form of
  f1 :/\: f2        -> and' (pre n f1) (pre n f2)
  f1 :\/: f2        -> or'  (pre n f1) (pre n f2)
  f1 :=>: f2        -> pre n (Not f1 :\/: f2)
  Exists f          -> pre_ex (top,x + 1) [x] (f (var x))
    where (top,x) = n
  Forall f          -> pre n (Not (Exists (Not . f)))
  TRUE              -> tt'
  FALSE             -> ff'
  t1 :<: t2         -> lt' t1 t2
  t1 :>: t2         -> lt' t2 t1
  t1 :<=: t2        -> leq' t1 t2
  t1 :>=: t2        -> leq' t2 t1
  t1 :=: t2         -> eq' t1 t2
  t1 :/=: t2        -> neq' t1 t2
  k :| t            -> divs' k t
  Not form1 -> case form1 of
    Not f           -> pre n f
    Forall f        -> pre n (Exists (Not . f))
    _               -> not' (pre n form1)

pre_ex :: (Bool,Int) -> [Name] -> Formula -> Form
pre_ex (top,n) xs form = case form of
  Exists f          -> pre_ex (top,n+1) (n:xs) (f (var n))
  f1 :\/: f2        -> or' (pre_ex (top,n) xs f1) (pre_ex (top,n) xs f2)
  Not form1 ->
    case form1 of
      Not form2     -> pre_ex (top,n) xs form2
      Forall f      -> pre_ex (top,n) xs (Exists (Not . f))
      p :/\: q      -> pre_ex (top,n) xs (Not p :\/: Not q)
      _             -> exists_many top xs (pre (False,n) form)
  _                 -> exists_many top xs (pre (False,n) form)

invert :: Form -> Formula
invert form = case form of
  Conn And f1 f2 -> invert f1 :/\: invert f2
  Conn Or  f1 f2 -> invert f1 :\/: invert f2
  Prop prop -> case prop of
    Pred FF   True      :> []      -> FALSE
    Pred FF   False     :> []      -> TRUE
    Pred LT   True      :> [t1,t2] -> t1 :<: t2
    Pred LT   False     :> [t1,t2] -> t1 :>=: t2
    Pred LEQ  True      :> [t1,t2] -> t1 :<=: t2
    Pred LEQ  False     :> [t1,t2] -> t1 :>: t2
    Pred EQ   True      :> [t1,t2] -> t1 :=: t2
    Pred EQ   False     :> [t1,t2] -> t1 :/=: t2
    Pred (Divs n) True  :> [t]     -> n :| t
    Pred (Divs n) False :> [t]     -> Not (n :| t)
    _ -> error "(bug) Type error in 'invert'"


-- Terms ----------------------------------------------------------------------

-- | Terms of Presburger arithmetic.
-- Term are created by using the 'Num' class.
-- WARNING: Presburger arithmetic only supports multiplication
-- by a constant, trying to create invalid terms will result
-- in a run-time error.  A more type-safe alternative is to
-- use the '(.*)' operator.
data Term = Term (Map.IntMap Integer) Integer
          | FreeVar String -- ^thank you




type Name           = Int

-- | @split_term x (n * x + t1) = (n,t1)@
-- @x@ does not occur in @t1@
split_term         :: Name -> Term -> (Integer,Term)
split_term x (Term m n) = (fromMaybe 0 c, Term m1 n)
  where (c,m1) = Map.updateLookupWithKey (\_ _ -> Nothing) x m

var                :: Name -> Term
var x               = Term (Map.singleton x 1) 0

num                :: Integer -> Term
num n               = Term Map.empty n


--------------------------------------------------------------------------------

instance Eq Term where
  t1 == t2  = is_constant (t1 - t2) == Just 0

instance Num Term where
  fromInteger n             = Term Map.empty n

  Term m1 n1 + Term m2 n2   = Term (Map.unionWith (+) m1 m2) (n1 + n2)

  negate (Term m n)         = Term (Map.map negate m) (negate n)

  t1 * t2  = case fmap (.* t2) (is_constant t1) `mplus`
                  fmap (.* t1) (is_constant t2) of
               Just t  -> t
               Nothing -> error $ unlines [ "[(*) @ Term] Non-linear product:"
                                          , "  *** " ++ show t1
                                          , "  *** " ++ show t2
                                          ]
  signum t  = case is_constant t of
                Just n  -> num (signum n)
                Nothing -> error $ unlines [ "[signum @ Term]: Non-constant:"
                                           , " *** " ++ show t
                                           ]

  abs t     = case is_constant t of
                Just n  -> num (abs n)
                Nothing -> error $ unlines [ "[abs @ Term]: Non-constant:"
                                           , " *** " ++ show t
                                           ]


-- | Check if a term is a constant (i.e., contains no variables).
-- If so, then we return the constant, otherwise we return 'Nothing'.
is_constant :: Term -> Maybe Integer
is_constant (Term m n) = guard (all (0 ==) (Map.elems m)) >> return n

(.*) :: Integer -> Term -> Term
0 .* _        = 0
1 .* t        = t
k .* Term m n = Term (Map.map (k *) m) (k * n)


-- Formulas --------------------------------------------------------------------

data PredSym    = FF | LT | LEQ | EQ | Divs Integer {- +ve -}
data Pred       = Pred PredSym Bool -- Bool: positive (i.e. non-negated)?
data Prop       = Pred :> [Term]
data Conn       = And | Or deriving Eq
data Form       = Conn Conn Form Form | Prop Prop

abs_form       :: Form -> ([Prop],[Prop] -> Form)
abs_form fo     = let (ps,skel) = loop [] fo
                  in (reverse ps, fst . skel)
  where loop ps (Conn c p q) =
          let (ps1,f1) = loop ps p
              (ps2,f2) = loop ps1 q
          in (ps2, \fs -> let (p1,fs1) = f1 fs
                              (p2,fs2) = f2 fs1
                          in (Conn c p1 p2, fs2))
        loop ps (Prop p) = (p:ps, \(f:fs) -> (Prop f,fs))


not' :: Form -> Form
not' (Conn c t1 t2) = Conn (not_conn c) (not' t1) (not' t2)
not' (Prop p)       = Prop (not_prop p)

ff' :: Form
ff' = Prop $ Pred FF True :>[]

tt' :: Form
tt' = Prop $ Pred FF False :>[]

lt' :: Term -> Term -> Form
lt' t1 t2 = Prop $ Pred LT True :> [t1,t2]

leq' :: Term -> Term -> Form
leq' t1 t2 = Prop $ Pred LEQ True :> [t1,t2]

eq' :: Term -> Term -> Form
eq' t1 t2 = Prop $ Pred EQ True :> [t1,t2]

neq' :: Term -> Term -> Form
neq' t1 t2 = Prop $ Pred EQ False :> [t1,t2]

and' :: Form -> Form -> Form
and' p q = Conn And p q

or' :: Form -> Form -> Form
or' p q = Conn Or p q

divs' :: Integer -> Term -> Form
divs' n t = Prop $ Pred (Divs n) True :> [t]

ors' :: [Form] -> Form
ors' [] = ff'
ors' xs = foldr1 or' xs

not_conn :: Conn -> Conn
not_conn And = Or
not_conn Or  = And

not_prop :: Prop -> Prop
not_prop (f :> ts) = not_pred f :> ts

not_pred :: Pred -> Pred
not_pred (Pred p pos) = Pred p (not pos)



-- Eliminating existential quantifiers -----------------------------------------

data NormProp = Ind Prop
              | L Pred Term

norm2 :: Name -> Integer -> Pred -> Term -> Term -> (Integer,NormProp)
norm2 x final_k p t1 t2
  | k1 == k2   = (1, Ind (p :> [t1',t2']))
  | k1 > k2    = (abs k, L p t)
  | otherwise  = (abs k, L p' t)

  where (k1,t1') = split_term x t1
        (k2,t2') = split_term x t2

        k   = k1 - k2
        t   = (final_k `div` k) .* (t2' - t1')   -- only used when k /= 0

        p'  = case p of
                Pred LT b  -> Pred LEQ (not b)
                Pred LEQ b -> Pred LT (not b)
                _          -> p

norm1 :: Name -> Integer -> Pred -> Term -> (Integer,NormProp)
norm1 x final_k p@(Pred (Divs d) b) t
  | k == 0    = (1, Ind (p :> [t]))
  | otherwise = (abs k, L ps (l .* t'))

  where (k,t')  = split_term x t
        l       = final_k `div` k
        ps      = Pred (Divs (d * abs l)) b

norm1 _ _ _ _ = error "(bug) norm1 applied to a non-unary operator"


norm_prop :: Name -> Integer -> Prop -> (Integer,NormProp)
norm_prop _ _ p@(_ :> [])           = (1,Ind p)
norm_prop x final_k (p :> [t])      = norm1 x final_k p t
norm_prop x final_k (p :> [t1,t2])  = norm2 x final_k p t1 t2
norm_prop _ _ _                     = error "(bug) norm_prop on arity > 2"

-- The integer is "length as - length bs"
a_b_sets :: (Integer,[Term],[Term]) -> NormProp -> (Integer,[Term],[Term])
a_b_sets (o,as,bs) p = case p of
  Ind _ -> (o,as,bs)

  L (Pred op True) t ->
    case op of
      LT  -> (1 + o , t     : as,         bs)
      LEQ -> (1 + o , (t+1) : as,         bs)
      EQ  -> (o     , (t+1) : as, (t-1) : bs)
      _   -> (o     ,         as,         bs)

  L (Pred op False) t ->
    case op of
      LT  -> (o - 1 ,         as, (t-1) : bs)
      LEQ -> (o - 1 ,         as, t     : bs)
      EQ  -> (o     , t     : as, t     : bs)
      _   -> (o     ,         as,         bs)


analyze_props :: Name -> [Prop] -> ( [NormProp]
                                   , Integer    -- scale
                                   , Integer    -- bound
                                   , Either [Term] [Term]  -- A set or B set
                                   )
analyze_props x ps = (ps1, final_k, bnd, if o < 0 then Left as else Right bs)
  where (ks,ps1)  = unzip $ map (norm_prop x final_k) ps
        final_k   = lcms ks
        (o,as,bs) = foldl' a_b_sets (0,[],[]) ps1
        bnd       = lcms (final_k : [ d | L (Pred (Divs d) _) _ <- ps1 ])

from_bool :: Bool -> Prop
from_bool True  = Pred FF False :> []
from_bool False = Pred FF True :> []

neg_inf :: NormProp -> Term -> Prop
neg_inf prop t = case prop of
  Ind p -> p
  L ps@(Pred op pos) t1 -> case op of
    LT      -> from_bool pos
    LEQ     -> from_bool pos
    EQ      -> from_bool (not pos)
    Divs {} -> ps :> [t + t1]
    FF      -> error "(bug) FF in NormPred"

pos_inf :: NormProp -> Term -> Prop
pos_inf prop t = case prop of
  Ind p -> p
  L ps@(Pred op pos) t1 -> case op of
    LT      -> from_bool (not pos)
    LEQ     -> from_bool (not pos)
    EQ      -> from_bool (not pos)
    Divs {} -> ps :> [t + t1]
    FF      -> error "(bug) FF in NormPred"

normal :: NormProp -> Term -> Prop
normal prop t = case prop of
  Ind p -> p
  L ps@(Pred (Divs {}) _) t1  -> ps :> [t + t1]
  L ps t1                     -> ps :> [t,t1]


data Ex = Ex [(Name,Integer)]
             [Constraint]
             [Prop]

exists_many :: Bool -> [Name] -> Form -> Form
exists_many top xs f  = ors'
                  $ map exp_f
                  $ foldr (concatMap . ex_step) [Ex [] [] ps] (nub xs)
  where (ps,skel) = abs_form f
        exp_f = if top then expand_top skel else expand skel


ex_step :: Name -> Ex -> [Ex]
ex_step x (Ex xs ds ps) = case as_or_bs of
  Left as ->
    ( let arg = negate (var x)
      in Ex ((x,d) : xs) (constr arg) (map (`pos_inf` arg) ps1)
    ) : [ let arg = a - var x
          in Ex ((x,d) : xs) (constr arg) (map (`normal` arg) ps1) | a <- as ]

  Right bs ->
    ( let arg = var x
      in Ex ((x,d) : xs) (constr arg) (map (`neg_inf` arg) ps1)
    ) : [ let arg = b + var x
          in Ex ((x,d) : xs) (constr arg) (map (`normal` arg) ps1) | b <- bs ]

  where (ps1,k,d',as_or_bs) = analyze_props x ps
        d = lcms (d' : map fst ds)
        constr t = if k == 1 then ds else (k,t) : ds


expand_top :: ([Prop] -> Form) -> Ex -> Form
expand_top skel (Ex xs ds ps) =
  ors' [ skel (map (subst_prop env) ps) | env <- elim xs ds ]

expand :: ([Prop] -> Form) -> Ex -> Form
expand skel (Ex xs ds ps) =
  ors' [ foldr and' (skel (map (subst_prop env) ps)) (map (`ctr` env) ds)
            | env <- envs xs ]

  where envs []         = [ Map.empty ]
        envs ((x,bnd):qs) = [ Map.insert x v env
                                      | env <- envs qs, v <- [ 1 .. bnd ] ]

        ctr (k,t) env = Prop (Pred (Divs k) True :> [ subst_term env t ])



type Env = Map.IntMap Integer

subst_prop :: Env -> Prop -> Prop
subst_prop env (p :> ts) = p :> map (subst_term env) ts

subst_term :: Env -> Term -> Term
subst_term env (Term m n) =
  let (xs,vs) = unzip $ Map.toList $ Map.intersectionWith (*) env m
  in Term (foldl' (flip Map.delete) m xs) (foldl' (+) n vs)




-- Evaluation ------------------------------------------------------------------

-- The meanings of formulas.
eval_form :: Form -> Bool
eval_form (Conn c p q) = eval_conn c (eval_form p) (eval_form q)
eval_form (Prop p)     = eval_prop p

-- The meanings of connectives.
eval_conn :: Conn -> Bool -> Bool -> Bool
eval_conn And = (&&)
eval_conn Or  = (||)

-- The meanings of atomic propositions.
eval_prop :: Prop -> Bool
eval_prop (Pred p pos :> ts) = if pos then res else not res
  where res = eval_pred p (map eval_term ts)

-- The meanings of predicate symbols.
eval_pred :: PredSym -> [Integer] -> Bool
eval_pred p ts = case (p,ts) of
  (FF,     [])    -> False
  (Divs d, [k])   -> divides d k
  (LT,     [x,y]) -> x < y
  (LEQ,    [x,y]) -> x <= y
  (EQ,     [x,y]) -> x == y
  _               -> error "Type error"

-- We define: "d | a" as "exists y. d * y = a"
divides :: Integral a => a -> a -> Bool
0 `divides` 0 = True
0 `divides` _ = False
x `divides` y = mod y x == 0

-- The meaning of a term with no free variables.
-- NOTE: We do not check that there are no free variables.
eval_term :: Term -> Integer
eval_term (Term _ k) = k

-- The meaning of a term with free variables
eval_term_env :: Term -> Env -> Integer
eval_term_env (Term m k) env = sum (k : map eval_var (Map.toList m))
  where eval_var (x,c) = case Map.lookup x env of
                           Nothing -> error "free var"
                           Just v  -> c * v
--------------------------------------------------------------------------------


-- Solving divides constraints -------------------------------------------------
-- See the paper's appendix.


-- | let (p,q,r) = extended_gcd x y
--   in (x * p + y * q = r)  &&  (gcd x y = r)
extended_gcd :: Integral a => a -> a -> (a,a,a)
extended_gcd arg1 arg2 = loop arg1 arg2 0 1 1 0
  where loop a b x lastx y lasty
          | b /= 0    = let (q,b') = divMod a b
                            x'     = lastx - q * x
                            y'     = lasty - q * y
                        in x' `seq` y' `seq` loop b b' x' x y' y
          | otherwise = (lastx,lasty,a)


type Constraint     = (Integer,Term)
type VarConstraint  = (Integer,Integer,Term)

-- m | (x * a1 + b1) /\ (n | x * a2 + b2)
theorem1 :: VarConstraint -> VarConstraint -> (VarConstraint, Constraint)
theorem1 (m,a1,b1) (n,a2,b2) = (new_x, new_other)
  where new_x     = (m * n, d, (p*n) .* b1 + (q * m) .* b2)
        new_other = (d, a2 .* b1 - a1 .* b2)

        (p,q,d)   = extended_gcd (a1 * n) (a2 * m)

-- solutions for x in [1 .. bnd] of: m | x * a + b
theorem2 :: Integer -> (Integer,Integer,Integer) -> [Integer]
theorem2 bnd (m,a,b)
  | r == 0      = [ t * k - c | t <- [ lower .. upper ] ]
  | otherwise   = []
  where k           = div m d
        c           = p * qu
        (p,_,d)     = extended_gcd a m
        (qu,r)      = divMod b d

        (lower',r1) = divMod (1 + c) k
        lower       = if r1 == 0 then lower' else lower' + 1  -- hmm
        upper       = div (bnd + c) k

  -- lower and upper:
  -- t * k - c = 1   --> t = (1 + c) / k
  -- t * k - c = bnd --> t = (bnd + c) / k




elim :: [(Name,Integer)] -> [Constraint] -> [ Env ]
elim [] ts = if all chk ts then [ Map.empty ] else []
  where chk (x,t) = divides x (eval_term t)
elim ((x,bnd):xs) cs = do env <- elim xs cs1
                          v <- case mb of
                                 Nothing      -> [ 1 .. bnd ]
                                 Just (a,b,t) ->
                                   theorem2 bnd (a,b,eval_term_env t env)
                          return (Map.insert x v env)

  where (mb,cs1) = elim_var x cs




elim_var :: Name -> [Constraint] -> (Maybe VarConstraint, [Constraint])
elim_var x cs = case foldl' part ([],[]) cs of
                  ([], have_not)     -> (Nothing, have_not)
                  (h : hs, have_not) -> let (c,hn) = step h hs have_not
                                        in (Just c,hn)
  where part s@(have,have_not) c@(m,t)
          | m == 1      = s
          | a == 0      = (have        , c:have_not)
          | otherwise   = ((m,a,b):have,   have_not)
            where (a,b) = split_term x t

        step :: VarConstraint -> [VarConstraint] -> [Constraint]
             -> (VarConstraint,[Constraint])
        step h [] ns      = (h,ns)
        step h (h1:hs) ns = step h2 hs (n : ns)
          where (h2,n) = theorem1 h h1

-- Misc -----------------------------------------------------------------------

lcms :: Integral a => [a] -> a
lcms xs = foldr lcm 1 xs


-- Pretty Printing -------------------------------------------------------------

class PP a where
  pp :: a -> Doc


var_name           :: Name -> String
var_name x          = let (a,b) = divMod x 26
                          rest = if a == 0 then "" else show a
                      in toEnum (97 + b) : rest

instance Show Term where show x = show (pp x)
instance PP Term where
  pp (FreeVar x) = text x
  pp (Term m k) | isEmpty vars  = text (show k)
                | k == 0        = vars
                | k > 0         = vars <+> char '+' <+> text (show k)
                | otherwise     = vars <+> char '-' <+> text (show $ abs k)
    where ppvar (x,n) = sign <+> co <+> text (var_name x)
            where (sign,co)
                     | n == -1    = (char '-', empty)
                     | n < 0      = (char '-', text (show (abs n)) <+> char '*')
                     | n == 1     = (char '+', empty)
                     | otherwise  = (char '+', text (show n) <+> char '*')
          first_var (x,1)  = text (var_name x)
          first_var (x,-1) = char '-' <> text (var_name x)
          first_var (x,n)  = text (show n) <+> char '*' <+> text (var_name x)

          vars = case filter ((/= 0) . snd) (Map.toList m) of
                   []     -> empty
                   v : vs -> first_var v <+> hsep (map ppvar vs)


-- 4: wrap term, not
-- 3: wrap and
-- 2: wrap or
-- 1: wrap implies, quantifiers
instance PP Formula where
  pp = pp1 0 -- ' 0 0
    where
    pp1 :: Int -> Formula -> Doc
    pp1 p form = case form of
      _ :/\: _ -> hang (text "/\\") 2 (loop form)
        where loop (f1 :/\: f2) = loop f1 $$ loop f2
              loop f            = pp f

      _ :\/: _ -> hang (text "\\/") 2 (loop form)
        where loop (f1 :\/: f2) = loop f1 $$ loop f2
              loop f            = pp f

      _ -> pp' 0 p form



    pp' :: Int -> Name -> Formula -> Doc
    pp' n p form = case form of
      f1 :/\: f2 | n < 3  -> pp' 2 p f1 <+> text "/\\" <+> pp' 2 p f2
      f1 :\/: f2 | n < 2  -> pp' 1 p f1 <+> text "\\/" <+> pp' 1 p f2
      f1 :=>: f2 | n < 1  -> pp' 1 p f1 <+> text "=>" <+> pp' 0 p f2
      Not f      | n < 4  -> text "Not" <+> pp' 4 p f
      Exists {}  | n < 1  -> pp_ex (text "exists") p form
        where pp_ex d q (Exists g) = pp_ex (d <+> text (var_name q))
                                                          (q+1) (g (var q))
              pp_ex d q g          = d <> text "." <+> pp' 0 q g

      Forall {} | n < 1 -> pp_ex (text "forall") p form
        where pp_ex d q (Forall g) = pp_ex (d <+> text (var_name q))
                                                          (q+1) (g (var q))
              pp_ex d q g          = d <> text "." <+> pp' 0 q g
      TRUE        -> text "true"
      FALSE       -> text "false"
      t1 :<:  t2 | n < 4  -> pp t1 <+> text "<"  <+> pp t2
      t1 :>:  t2 | n < 4  -> pp t1 <+> text ">"  <+> pp t2
      t1 :<=: t2 | n < 4  -> pp t1 <+> text "<=" <+> pp t2
      t1 :>=: t2 | n < 4  -> pp t1 <+> text ">=" <+> pp t2
      t1 :=:  t2 | n < 4  -> pp t1 <+> text "="  <+> pp t2
      t1 :/=: t2 | n < 4  -> pp t1 <+> text "/=" <+> pp t2
      k :| t1    | n < 4  -> text (show k) <+> text "|" <+> pp t1
      _ -> parens (pp' 0 p form)

instance Show Formula where show = show . pp



instance PP PredSym where
  pp p = case p of
    FF      -> text "false"
    LT      -> text "<"
    LEQ     -> text "<="
    EQ      -> text "==="
    Divs n  -> text (show n) <+> text "|"

instance PP Pred where
  pp (Pred p True) = pp p
  pp (Pred p False) = case p of
    FF      -> text "true"
    LT      -> text ">="
    LEQ     -> text ">"
    EQ      -> text "=/="
    Divs n  -> text (show n) <+> text "/|"

instance Show Prop where show = show . pp
instance PP Prop where
  pp (p :> [t1,t2]) = pp t1 <+> pp p <+> pp t2
  pp (p :> ts)      = pp p <+> hsep (map pp ts)


instance PP Conn where
  pp And  = text "/\\"
  pp Or   = text "\\/"

instance PP Form where
  pp me@(Conn c _ _) = hang (pp c) 2 (vcat $ map pp $ jn me [])
    where jn (Conn c1 p1 q1) fs | c == c1 = jn p1 (jn q1 fs)
          jn f fs = f : fs
  pp (Prop p)     = pp p

instance PP NormProp where
  pp (Ind p)  = pp p
  pp (L p@(Pred (Divs {}) _) t) = pp p <+> text "_ +" <+> pp t
  pp (L p t)                    = text "_" <+> pp p <+> pp t

instance Show NormProp where show = show . pp

instance PP Ex where
  pp (Ex xs ps ss) = hang (text "OR" <+> hsep (map quant xs)) 2
             ( text "!" <+> hsep (map (parens . divs) ps)
            $$ vcat (map pp ss)
             )
    where quant (x,n) = parens $ text (var_name x) <> colon <> text (show n)
          divs (x,t)  = text (show x) <+> text "|" <+> pp t


