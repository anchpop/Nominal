-- | An example of "Nominal": untyped lambda calculus.

import Nominal
import Prelude hiding ((.))

-- | The type of lambda terms, up to alpha-equivalence.
data Term = Var Atom | App Term Term | Abs (BindAtom Term)
          deriving (Show)

-- In an ideal programming language, this instance would be
-- automatically derived with \"deriving\". We could probably make
-- this even simpler.
instance Nominal Term where
  swap a b (Var x) = Var (swap a b x)
  swap a b (App t s) = App (swap a b t) (swap a b s)
  swap a b (Abs t) = Abs (swap a b t)

instance NominalSupport Term where
  support (Var x) = support x
  support (App t s) = support (t,s)
  support (Abs t) = support t

-- | A convenience constructor for abstractions. This allows us to
-- write @lam (\x -> App x x)@ instead of @Abs (x.App (Var x) (Var x))@
lam :: (Term -> Term) -> Term
lam = lam_named "x"

-- | A version of 'lam' that permits us to suggest a name for the
-- bound variable.
lam_named :: String -> (Term -> Term) -> Term
lam_named n f = with_fresh_named n (\x -> Abs (x . f (Var x)))

-- | Substitution. Note that it is capture avoiding!
-- 'subst' /m/ /x/ /n/ substitutes /m/ for 'Var' /x/ in /n/.
subst :: Term -> Atom -> Term -> Term
subst m x (Var y)
  | x == y = m
  | otherwise = Var y
subst m x (App t s) = App (subst m x t) (subst m x s)
subst m x (Abs t) = open t (\y s -> Abs (y . subst m x s))

