module Syntax where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false) renaming (Bool to Boolean)


-- simple keystone types
data Base : Set where 
  Bool    : Base 
  Int     : Base

-- forward decleration of recursive types to make Agda happy... 
data Type      : Set 
data Predicate : Base → Set 
-- Should be changed when implementing polymorphism
-- KCtx : ℕ → Set
-- KCtx = Vec Kind

Ctx : ℕ → Set
Ctx = Vec Type

data Term {n} (Γ : Ctx n) : Type → Set
Closed : Type → Set
Closed = Term []

-- actual definitions
infixr 30 _⇒_
data Type where
  Refine : (b : Base) → Predicate b → Type
  _⇒_ : Type → Type  → Type 
  -- Lift   : Base               → Type
-- ∃      : Type → Type        → Type

⟦_⟧ : Type → Set
⟦ Refine Int p  ⟧  = ℕ
⟦ Refine Bool p ⟧  = Boolean
-- ^ might want to represent this as (type, predicate) instead
-- ^ since right now you can define a (Refine Int (<8)) ⪯ Refine Int (>8), which seems... incorrect.
-- ⟦Lift Int⟧  = ℕ
-- ⟦ Lift  Bool    ⟧  = Boolean
⟦ σ ⇒ τ ⟧         = ⟦ σ ⟧ → ⟦ τ ⟧
-- ⟦ ∃ a x ⟧      = ℕ -- I don't know what you become...



infixr 5 _∷_
data Env : ∀ {n} → Ctx n → Set where
  []  : Env []
  _∷_ : ∀ {n} {Γ : Ctx n} {τ} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)

lookupEnv : ∀ {n} {Γ : Ctx n} (m : Fin n) → Env Γ → ⟦ lookup Γ m ⟧
lookupEnv zero    (x ∷ _)   = x
lookupEnv (suc n) (_ ∷ env) = lookupEnv n env

Lift : Base → Type

data Predicate  where 
  Empty : { t : Base } → Predicate t 
  And   : { t : Base } → (Closed ( (Lift t) ⇒ Lift Bool)) → Predicate t → Predicate t
Lift b = Refine b Empty

infixr 30 _⪯_
data _⪯_ : Type → Type → Set where 
  subtype : ∀ {t t' } → (⟦ t ⟧ -> ⟦ t' ⟧) -> t ⪯ t'

data Term {n} Γ where
  Nat   : ℕ → {p : Predicate Int} → Term Γ (Refine Int p)
  Bool  : Boolean → {p : Predicate Bool} → Term Γ (Refine Bool p)
  Var   : ∀ {t}  (v : Fin n) → t ≡ lookup Γ v → Term Γ t
  Lam   : ∀ {a b} → Term (a ∷ Γ) b     → Term Γ (a ⇒ b)
  App   : ∀ {a a' b : Type} → a ⪯ a' → Term Γ (a' ⇒ b) → Term Γ a → Term Γ b
  Let   : ∀ {a b} → Term Γ a  → Term (a ∷ Γ) b → Term Γ b
  _==_  : ∀ {t} → Term Γ ((Lift t) ⇒ (Lift t) ⇒ Lift Bool)
  _≥_   : Term Γ (Lift Int  ⇒ (Lift Int ⇒ Lift Bool))
  _>_   : Term Γ (Lift Int  ⇒ (Lift Int ⇒ Lift Bool))
  _≤_   : Term Γ (Lift Int  ⇒ (Lift Int ⇒ Lift Bool))
  _<_   : Term Γ (Lift Int  ⇒ (Lift Int ⇒ Lift Bool))
  _+_   : Term Γ (Lift Int  ⇒ (Lift Int ⇒ Lift Int))
  _-_   : Term Γ (Lift Int  ⇒ (Lift Int ⇒ Lift Int))
  _*_   : Term Γ (Lift Int  ⇒ (Lift Int ⇒ Lift Int))
  _||_  : Term Γ (Lift Bool ⇒ (Lift Bool ⇒ Lift Bool))
  _&&_  : Term Γ (Lift Bool ⇒ (Lift Bool ⇒ Lift Bool))
 

greaterThan100 : Term []
  (Refine Int 
    (And 
      (App (subtype \x -> x) (_<_) (Nat 100 {Empty})) 
      (Empty)
    )
  )
greaterThan100 = Nat 101


bounded : Term []
  (Refine Int 
    (And 
      (App (subtype \x -> x) (_<_) (Nat 100 {Empty})) 
      (And (App (subtype \x -> x) (_>_) (Nat 200 {Empty})) 
           (Empty))
    )
  )
bounded = Nat 101