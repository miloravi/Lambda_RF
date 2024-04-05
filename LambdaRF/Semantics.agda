module Semantics where

open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _＋_; _*_ to _⋆_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Bool using (true; false; _∧_; _∨_) renaming (Bool to Boolean)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Syntax

equals : {t : Base} → ⟦ Lift t ⟧ → ⟦ Lift t ⟧ → Boolean
equals {Int} zero zero = true
equals {Int} zero (suc t) = false
equals {Int} (suc t) zero = false
equals {Int} (suc t₁) (suc t₂) = equals t₁ t₂
equals {Bool} true true = true
equals {Bool} false false = true
equals {Bool} _ _ = false

greaterThanEq : ⟦ Lift Int ⟧ → ⟦ Lift Int ⟧ → Boolean
greaterThanEq zero zero = true
greaterThanEq zero (suc t) = true
greaterThanEq (suc t) zero = false
greaterThanEq (suc t₁) (suc t₂) = greaterThanEq t₁ t₂

greaterThan : ⟦ Lift Int ⟧ → ⟦ Lift Int ⟧ → Boolean
greaterThan zero zero = false
greaterThan zero (suc t) = true
greaterThan (suc t) zero = false
greaterThan (suc t₁) (suc t₂) = greaterThan t₁ t₂

lesserThanEq : ⟦ Lift Int ⟧ → ⟦ Lift Int ⟧ → Boolean
lesserThanEq zero zero = true
lesserThanEq zero (suc t) = false
lesserThanEq (suc t) zero = true
lesserThanEq (suc t₁) (suc t₂) = lesserThanEq t₁ t₂

lesserThan : ⟦ Lift Int ⟧ → ⟦ Lift Int ⟧ → Boolean
lesserThan zero zero = false
lesserThan zero (suc t) = false
lesserThan (suc t) zero = true
lesserThan (suc t₁) (suc t₂) = lesserThan t₁ t₂

_[_] : ∀ {n} {Γ : Ctx n} {τ} → Env Γ → Term Γ τ → ⟦ τ ⟧
env [ Nat n  ]                = n
env [ Bool b ]                = b
env [ Var v refl ]            = lookupEnv v env
env [ Lam t ]                 = λ x → (x ∷ env) [ t ]
env [ App (subtype f) t₁ t₂ ] = (env [ t₁ ]) (f (env [ t₂ ]))
env [ Let t₁ t₂ ]             = let x = env [ t₁ ] in (x ∷ env) [ t₂ ]
env [ _==_ ]                  = λ t₁ → λ t₂ → equals t₁ t₂
env [ _≥_ ]                   = λ t₁ → λ t₂ → greaterThanEq t₁ t₂
env [ _>_ ]                   = λ t₁ → λ t₂ → greaterThan t₁ t₂
env [ _≤_ ]                   = λ t₁ → λ t₂ → lesserThanEq t₁ t₂
env [ _<_ ]                   = λ t₁ → λ t₂ → lesserThan t₁ t₂
env [ _+_ ]                   = λ t₁ → λ t₂ → t₁ ＋ t₂
env [ _-_ ]                   = λ t₁ → λ t₂ → t₁ ∸ t₂
env [ _*_ ]                   = λ t₁ → λ t₂ → t₁ ⋆ t₂
env [ _||_ ]                  = λ t₁ → λ t₂ → t₁ ∧ t₂
env [ _&&_ ]                  =  λ t₁ → λ t₂ → t₁ ∨ t₂

⦅_⦆ : {b : Base} → Predicate b → ⟦ Lift b ⟧ → ⟦ Lift Bool ⟧
⦅ Empty ⦆     = \b → true 
⦅ And pred rest ⦆ = let 
  p = [] [ pred ] 
  in \b -> p b ∧ ⦅ rest ⦆ b


if_then_else_ : {A : Set} → Boolean → A → A → A
if true then x else y = x
if false then x else y = y

produce : {p : Predicate Int} → ℕ -> Maybe (Term [] (Refine Int p))
produce {p} n = let 
  pred = ⦅ p ⦆
  b = pred n 
  in if b then (just (Nat n)) else nothing
  
nBounded : Maybe (Term []
  (Refine Int 
    ((And 
      (App (subtype \x -> x) (_<_) (Nat 100 {Empty})) 
      (And (App (subtype \x -> x) (_>_) (Nat 200 {Empty})) 
           (Empty))
    ))
  ))
nBounded = produce 101 
  


