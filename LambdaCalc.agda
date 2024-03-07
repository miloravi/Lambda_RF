module LambdaCalc where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
-- open import Relation.Nullary using (Dec; yes; no)
-- open import Function using (_∘_; _$_)
-- open import Data.Product


infixr 30 _⇒_
data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

infixl 80 _∙_
data Syntax : Set where
  var  : ℕ → Syntax
  lit  : ℕ → Syntax
  _⊕_ : Syntax → Syntax → Syntax
  _∙_  : Syntax → Syntax → Syntax
  lam  : Type → Syntax → Syntax

Ctx : ℕ → Set
Ctx = Vec Type

data Term {n} (Γ : Ctx n) : Type → Set where
  var  : ∀ {τ} (v : Fin n) → τ ≡ lookup Γ v → Term Γ τ
  lit  : ℕ → Term Γ nat
  _⊕_ : Term Γ nat → Term Γ nat → Term Γ nat
  _∙_  : ∀ {a b} → Term Γ (a ⇒ b) → Term Γ a → Term Γ b
  lam  : ∀ {a b} → Term (a ∷ Γ) b → Term Γ (a ⇒ b) -- b moet implicit

