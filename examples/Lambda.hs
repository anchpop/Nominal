{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

-- | An example of "Nominal": untyped lambda calculus.

module Lambda where

import Nominal
import Prelude hiding ((.))
import Data.Set (Set)
import qualified Data.Set as Set

-- ----------------------------------------------------------------------
-- * Terms

data V
instance AtomKind V
type Variable = AtomOfKind V

-- | The type of lambda terms, up to alpha-equivalence.
data Term = Var Variable | App Term Term | Abs (Bind Variable Term)
          deriving (Eq, Generic, Nominal, NominalSupport, NominalShow, Show)

-- | A convenience constructor for abstractions. This allows us to
-- write @lam (\x -> App x x)@ instead of @Abs (x.App (Var x) (Var x))@
lam :: (Term -> Term) -> Term
lam f = with_fresh (\x -> Abs (x . f (Var x)))

-- | A version of 'lam' that permits us to suggest a name for the
-- bound variable.
lam_named :: String -> (Term -> Term) -> Term
lam_named n f = with_fresh_named n (\x -> Abs (x . f (Var x)))

-- | An alternative syntax for 'App'.
(@@) :: Term -> Term -> Term
m @@ n = App m n

infixl 9 @@

-- ----------------------------------------------------------------------
-- * Substitution
  
-- | Substitution. Note that it is capture avoiding!
-- 'subst' /m/ /x/ /n/ substitutes /m/ for 'Var' /x/ in /n/.
subst :: Term -> Variable -> Term -> Term
subst m z (Var x)
  | x == z    = m
  | otherwise = Var x
subst m z (App t s) = App (subst m z t) (subst m z s)
subst m z (Abs (x :. t)) = Abs (x . subst m z t)

-- ----------------------------------------------------------------------
-- * Free variables

-- | Free variables.
fv :: Term -> Set Variable
fv (Var x) = Set.singleton x
fv (App m n) = fv m `Set.union` fv n
fv (Abs (x :. t)) = Set.delete x (fv t)

-- ----------------------------------------------------------------------
-- * Evaluation

-- | Beta-reduction to normal form.
reduce :: Term -> Term
reduce (Var x) = Var x
reduce (App m n) =
  case reduce m of
    Abs (x :. t) -> reduce (subst n x t)
    m' -> App m' (reduce n)
reduce (Abs (x :. t)) = Abs (x . reduce t)

-- ----------------------------------------------------------------------
-- * Some example terms

-- | Church numeral zero.
z :: Term
z = lam_named "s" $ \s -> lam_named "z" $ \z -> z

-- | Successor of Church numeral.
s :: Term
s = lam $ \n -> lam_named "s" $ \s -> lam_named "z" $ \z -> s @@ (n @@ s @@ z)

-- | Addition of Church numerals.
plus :: Term
plus = lam $ \n -> lam $ \m -> n @@ s @@ m

-- | Multiplication of Church numerals.
times :: Term
times = lam $ \n -> lam $ \m -> n @@ (plus @@ m) @@ z

-- | The Church numeral /n/. This function demonstrates a use of
-- 'with_fresh' to build lambda terms from names.
church :: Integer -> Term
church n =
  with_fresh_named "s" $ \s ->
    with_fresh_named "z" $ \z ->
      Abs (s . Abs (z . aux n (Var s) (Var z)))
  where
    aux n s z
      | n <= 0 = z
      | otherwise = s @@ (aux (n-1) s z)

-- | Another example of a recursively built term.
multilam :: Integer -> Term -> Term
multilam 0 t = t
multilam n t = lam (\x -> multilam (n-1) t)

-- | Another example of a recursively built term.
nested :: Integer -> Term -> Term
nested 0 t = t
nested n t = lam (\x -> nested (n-1) (t @@ x))

-- ----------------------------------------------------------------------
-- | A pretty-printer for terms.

-- | Optional parentheses.
paren :: Bool -> String -> String
paren False s = s
paren True s = "(" ++ s ++ ")"

-- | Pretty-printing with precedence and support.
pretty_aux :: Support -> Int -> Term -> String
pretty_aux sup d (Var x) = show x
pretty_aux sup d (App m n) = paren (d > 10) $
  pretty_aux sup 10 m ++ " " ++ pretty_aux sup 11 n
pretty_aux sup d (Abs body) = open_for_printing sup body $ \x m sup ->
  paren (d > 1) $
    "λ" ++ show x ++ "." ++ pretty_aux sup 1 m

-- | Top-level function for pretty-printing.
pretty :: Term -> IO ()
pretty m = putStrLn (pretty_aux (support m) 0 m)

-- ----------------------------------------------------------------------
-- * Now try it!

-- $ Here are some things you can try:
--
-- >>> z
-- >>> s
-- >>> plus
-- >>> pretty z
-- >>> pretty s
-- >>> pretty plus
-- >>> pretty times
-- >>> pretty $ church 1
-- >>> pretty $ church 2
-- >>> pretty $ church 3
-- >>> pretty $ plus @@ church 2 @@ church 2
-- >>> pretty $ reduce (plus @@ church 2 @@ church 2)
-- >>> plus @@ church 2 @@ church 2 == church 4
-- >>> reduce (plus @@ church 2 @@ church 2) == church 4
-- >>> x <- fresh_named "x" :: IO Variable
-- >>> y <- fresh_named "y" :: IO Variable
-- >>> let k = Abs (x . App (Var x) (Var y))
-- >>> pretty k
-- >>> fv k
-- >>> pretty $ subst z y k
