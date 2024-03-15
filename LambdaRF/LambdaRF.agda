module LambdaRF where

data Kind : Set where
  Star : Kind
  B    : Kind

data BaseType : B where 
  Bool : BaseType 
  Int  : BaseType
--  𝛼    : BaseType

data Predicate : Set where
  Empty      : Predicate 
  Refinement : (Term ⇒ Bool) → Predicate → Predicate 

--  Refinements
-- data Preds = PEmpty                         -- type Preds = [Expr]
--            | PCons  Expr Preds
--   deriving Eq
-- {-@ data Preds where 
--         PEmpty :: Preds
--         PCons  :: p:Expr -> ps:Preds 
--                          -> { ps':Preds | Set_sub (fvP ps') (Set_cup (fv p) (fvP ps)) &&
--                                           Set_sub (ftvP ps') (Set_cup (ftv p) (ftvP ps)) } @-}

infixr 30 _⇒_
data Type : Star where
  Refine : BaseType -> Predicate -> Type
  _⇒_   : Type → Type → Type
  ∃      : Type → Type
  -- ∀      : Kind → Type 

-- Should be changed when implementing polymorphism
Ctx : ℕ → Set
Ctx = Vec Type


data Term : Set where
  Var : ℕ → Term
  Lam : Type → (Term → Term) → Term
  App : Term → Term → Term
  Let : Term → (Term → Term) → Term
  -- If  : Term → Term → Term → Term
  -- Fix : Term → Term