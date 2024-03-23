module Syntax where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Sum using (_⊎_; inj₁; inj₂)


-- simple keystone types
data Kind : Set where
  Star : Kind
  B    : Kind

data Base : Set where 
  Bool    : Base 
  Int     : Base
  α       : Base
  
-- forward decleration of recursive types to make Agda happy... 
data Type      : Set 
data Predicate : Base → Set 
-- Should be changed when implementing polymorphism
TCtx : ℕ → Set
TCtx = Vec Type

KCtx : ℕ → Set
KCtx = Vec Kind
data Term {n m} (Π : KCtx n) (Γ : TCtx m)  : Type → Set
Closed : Type → Set
Closed = Term [] []

-- actual definitions
infixr 30 _v⇒_
infixr 30 _t⇒_
data Type where
  Refine : (b : Base) → Predicate b → Type
  _v⇒_  : Type → Type        → Type 
  _t⇒_  : Kind → Type        → Type 
  ∃      : Type → Type        → Type
  Forall : Kind → Type        → Type
  Lift   : Base               → Type

data Predicate  where 
  Empty : { t : Base } → Predicate t 
  And   : { t : Base } → (Closed ( (Lift t) v⇒ Lift Bool)) → Predicate t → Predicate t 


infixr 30 _⪯_
{-# NO_POSITIVITY_CHECK #-}
data _⪯_ : Type → Type → Set where 
  subtype : ∀ {t t' } → 
    (f : ∀ {n m : ℕ}  {Π : KCtx n} {Γ : TCtx m} → (Term Π Γ t) → (Term Π Γ t')) → t ⪯ t'

data Term {n m} Π Γ where
  Nat   : ℕ → Term Π Γ (Refine Int Empty)
  Bool  : ℕ → Term Π Γ (Refine Bool Empty)
  Var   : ∀ {t}  (v : Fin m) → t ≡ lookup Γ v → Term Π Γ t
  Lam   : ∀ {a b} → Term Π (a ∷ Γ) b     → Term Π Γ (a v⇒ b)
  TLam  : ∀ {a k} → Term (k ∷ Π) Γ a     → Term Π Γ (k t⇒ a)
  App   : ∀ {a a' b} → a ⪯ a' → Term Π Γ (a' v⇒ b) → Term Π Γ a → Term Π Γ b
  TApp  : ∀ {a k} → Term Π Γ (k t⇒ a) → (t : Type) → Term Π Γ a    
  Let   : ∀ {a b} → Term Π Γ a  → Term Π (a ∷ Γ) b → Term Π Γ b  
