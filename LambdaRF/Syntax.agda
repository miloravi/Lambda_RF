module Syntax where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data Kind : Set where
  Star : Kind
  B    : Kind

data Base : Set where 
  Bool : Base 
  Int  : Base
  
infixr 30 _v⇒_
infixr 30 _t⇒_
-- forward decleration to make Agda happy... 
data Type      : Set 
data Predicate : Base → Set 
data Type where
  Refine : (b : Base) → Predicate b → Type
  _v⇒_   : Type → Type → Type -- there has to be a better way than this...
  _t⇒_   : Kind → Type → Type 
  ∃      : Type → Type → Type
  Lift   : (b : Base) → Type
  -- ∀      : Kind → Type → Type 
  
-- Should be changed when implementing polymorphism
TCtx : ℕ → Set
TCtx = Vec Type

KCtx : ℕ → Set
KCtx = Vec Kind
  
data Term {n m} (Π : KCtx n) (Γ : TCtx m)  : Type → Set
Closed : Type → Set
Closed = Term [] []

data Predicate  where 
  Empty : { t : Base } → Predicate t 
  And   : { t : Base } → (Closed ( (Lift t) v⇒ Lift Bool)) → Predicate t → Predicate t 

data Syntax : Set where
  Var  : ℕ     → Syntax
  Lam  : {-- Type → --} Syntax → Syntax
  App  : Syntax → Syntax → Syntax
  Let  : Syntax → Syntax → Syntax
  TLam : Kind → {-- Type → --}  Syntax → Syntax
  TApp : Syntax → Type → Syntax
  Annot : Syntax → Type → Syntax
  
data Term {n m} Π Γ where
  Nat   : ℕ → Term Π Γ (Refine Int Empty)
  Var   : forall {t} (v : Fin m) → t ≡ lookup Γ v → Term Π Γ t
  Lam   : forall {a b} → Term Π (a ∷ Γ) b → Term Π Γ (a v⇒ b)
  App   : forall {a b} → Term Π Γ (a v⇒ b) → Term Π Γ a → Term Π Γ b
  TLam  : forall {a}   → (k : Kind) → Term (k ∷ Π) Γ a → Term Π Γ (k t⇒ a)
  TApp  : forall {a}   → (k : Kind) → Term (Π) Γ (k t⇒ a) → Term Π Γ a  
  -- | what do you add...?
  Let   : forall {a b} → Term Π Γ a → Term Π (a ∷ Γ) b → Term Π Γ b  
