module Syntax where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data Kind : Set where
  Star : Kind
  B    : Kind

data BaseType : Set where 
  Bool : BaseType 
  Int  : BaseType
  α    : BaseType

-- forward decleration to make Agda happy... 
data Syntax : Set 
data Predicate : Set 
data Type : Set 

data Syntax where
  Var  : ℕ     → Syntax
  Lam  : {-- Type → --} Syntax → Syntax
  App  : Syntax → Syntax → Syntax
  Let  : Syntax → Syntax → Syntax
  TLam : Kind → {-- Type → --}  Syntax → Syntax
  TApp : Syntax → Type → Syntax
  Annot : Syntax → Type → Syntax
  
data Predicate where
  Empty      : Predicate 
  Refinement : Syntax → Predicate → Predicate 

infixr 30 _⇒_
data Type where
  Refine : BaseType → Predicate → Type
  _⇒_   : Type → Type → Type
  ∃      : Type → Type → Type
  Lift   : BaseType → Type
  -- ∀      : Kind → Type → Type 

-- Should be changed when implementing polymorphism
Ctx : ℕ → Set
Ctx = Vec (Kind ⊎ Type)

-- data Ctx : ℕ → Set where
--   -- eCtx  : Ctx zero
--   tCtx : Vec Type
--   kCtx : Vec Kind

data Term {n} (Γ : Ctx n) : Type → Set where
  Var   : ℕ → Term Γ (Lift Int)
  Lam   : forall {a b} → Term ((inj₂ a) ∷ Γ) b → Term Γ (a ⇒ b)
  App   : forall {a b} → Term Γ (a ⇒ b) → Term Γ a → Term Γ b
  Let   : forall {a b} → Term Γ a → Term (inj₂ a ∷ Γ) b → Term Γ b
  TLam  : forall {a} → (k : Kind) → Term (inj₁ k ∷ Γ) a → Term Γ a
  TApp  : forall {a t} → Term (inj₂ t ∷ Γ) a → (t' : Type) → Term Γ a
  Annot : forall {a t} → Term (inj₂ t ∷ Γ) a → (t' : Type) → Term Γ a 
