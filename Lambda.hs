{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | An example of "Nominal": untyped lambda calculus.

import Nominal
import Prelude hiding ((.))
import Data.Set (Set)
import qualified Data.Set as Set

newtype Variable = Variable Atom
  deriving (Atomic, Nominal, NominalSupport, Eq, Show, Ord)

-- | The type of lambda terms, up to alpha-equivalence.
data Term = Var Variable | App Term Term | Abs (Bind Variable Term)

-- In an ideal programming language, this instance would be
-- automatically derived with \"deriving\". We could probably make
-- this even simpler.
instance Nominal Term where
  swap π (Var x) = Var (swap π x)
  swap π (App t s) = App (swap π t) (swap π s)
  swap π (Abs t) = Abs (swap π t)

instance NominalSupport Term where
  support (Var x) = support x
  support (App t s) = support (t,s)
  support (Abs t) = support t

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

-- | Substitution. Note that it is capture avoiding!
-- 'subst' /m/ /x/ /n/ substitutes /m/ for 'Var' /x/ in /n/.
subst :: Term -> Variable -> Term -> Term
subst m x (Var y)
  | x == y = m
  | otherwise = Var y
subst m x (App t s) = App (subst m x t) (subst m x s)
subst m x (Abs t) = open t (\y s -> Abs (y . subst m x s))

-- | Function composition, re-defined here because we are hiding '.'
-- from the "Prelude".
compose :: (b -> c) -> (a -> b) -> (a -> c)
compose f g x = f (g x)

-- | Pretty-printing of lambda terms.
instance Show Term where
  showsPrec d (Var x) = showsPrec d x
  showsPrec d (App m n) = showParen (d > 10) $
    showsPrec 10 m `compose` showString " " `compose` showsPrec 11 n
  showsPrec d (Abs t) = open_for_printing t $ \x s ->
    showParen (d > 1) $
      showString ("λ" ++ show x ++ ".") `compose` showsPrec 1 s

-- | Free variables.
fv :: Term -> Set Variable
fv (Var x) = Set.singleton x
fv (App m n) = fv m `Set.union` fv n
fv (Abs t) = open t (\x s -> Set.delete x (fv s))

-- | Beta reduction to normal form.
reduce :: Term -> Term
reduce (Var x) = Var x
reduce (App m n) =
  case reduce m of
   Abs t -> open t (\x s -> reduce (subst n x s))
   m' -> App m' (reduce n)
reduce (Abs t) = open t (\x s -> Abs (x.reduce s))

-- $ Some example terms

-- | Church numeral zero.
z :: Term
z = lam_named "s" $ \s -> lam_named "z" $ \z -> z

-- | Successor of Church numeral.
s :: Term
s = lam$ \n -> lam_named "s" $ \s -> lam_named "z" $ \z -> s @@ (n @@ s @@ z)

-- | Addition of Church numerals.
plus :: Term
plus = lam$ \n -> lam$ \m -> n @@ s @@ m

-- | Multiplication of Church numerals.
times :: Term
times = lam$ \n -> lam$ \m -> n @@ (plus @@ m) @@ z

-- | The Church numeral /n/. This function demonstrates a use of
-- 'with_fresh' to build lambda terms from names.
church :: Integer -> Term
church n =
  with_fresh_named "s" $ \s ->
    with_fresh_named "z" $ \z ->
      Abs (s. Abs (z. aux n (Var s) (Var z)))
  where
    aux n s z
      | n <= 0 = z
      | otherwise = s @@ (aux (n-1) s z)

-- | Another example of a recursively built term.
multilam :: Integer -> Term -> Term
multilam 0 t = t
multilam n t = lam (\x -> multilam (n-1) (t @@ x))
