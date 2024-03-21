module LambdaCalc where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_; _$_)


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

-- Closed terms
Closed : Type → Set
Closed = Term []

erase : ∀ {n} {Γ : Ctx n} {τ} → Term Γ τ → Syntax
erase (var v _) = var (toℕ v)
erase (lit n)   = lit n
erase (t ⊕ u)  = erase t ⊕ erase u
erase (t ∙ u)   = erase t ∙ erase u
erase (lam {σ} t)   = lam σ (erase t)

≡⇒₁ : ∀ {σ σ′ τ τ′} → σ ⇒ τ ≡ σ′ ⇒ τ′ → σ ≡ σ′
≡⇒₁ refl = refl
≡⇒₂ : ∀ {σ σ′ τ τ′} → σ ⇒ τ ≡ σ′ ⇒ τ′ → τ ≡ τ′
≡⇒₂ refl = refl

_≟_ : (τ σ : Type) → Dec (τ ≡ σ)
nat   ≟ nat   = yes refl
nat   ≟ _ ⇒ _ = no λ()
_ ⇒ _ ≟ nat   = no λ()
σ ⇒ τ ≟ σ′ ⇒ τ′ with σ ≟ σ′ | τ ≟ τ′ 
...  | yes refl | yes refl = yes refl
...  | no  σ≢σ′ | _        = no (σ≢σ′ ∘ ≡⇒₁)
...  | _        | no τ≢τ′  = no (τ≢τ′ ∘ ≡⇒₂)

data Fromℕ (n : ℕ) : ℕ → Set where
  yeah : (m : Fin n) → Fromℕ n (toℕ m)
  nah  : (m : ℕ)     → Fromℕ n (n + m)

fromℕ : ∀ a b → Fromℕ a b
fromℕ zero    m       = nah m
fromℕ (suc n) zero    = yeah zero 
fromℕ (suc n) (suc m) with fromℕ n m
... | yeah x  = yeah (suc x)
... | nah x   = nah x

data Check {n} (Γ : Ctx n) : Syntax → Set where
  yay : (τ : Type) (t : Term Γ τ) → Check Γ (erase t)
  nay : {e : Syntax} → Check Γ e

check : ∀ {n} (Γ : Ctx n) (t : Syntax) → Check Γ t
check {n} Γ (var i)  with fromℕ n i 
... | yeah x = yay (lookup Γ x) (var x refl)
... | nah x  = nay 
check Γ (lit i)  = yay nat (lit i)
check Γ (x ⊕ y) with check Γ x | check Γ y 
... | yay nat x | yay nat y = yay nat (x ⊕ y)
... | _         | _         = nay
check Γ (f ∙ a)  with (check Γ f) | check Γ a
... | yay (a ⇒ b) f | yay c v with a ≟ c
...                         | yes refl  = yay b (f ∙ v)
...                         | _  = nay
check Γ (f ∙ a) | _ | _   = nay
check Γ (lam σ t) with check (σ ∷ Γ) t 
... | yay τ x            = yay (σ ⇒ τ) (lam x)    
... | nay                = nay


⟦_⟧ : Type → Set
⟦ nat   ⟧ = ℕ
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

infixr 5 _∷_
data Env : ∀ {n} → Ctx n → Set where
  []  : Env []
  _∷_ : ∀ {n} {Γ : Ctx n} {τ} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)

lookupEnv : ∀ {n} {Γ : Ctx n} (m : Fin n) → Env Γ → ⟦ lookup Γ m ⟧
lookupEnv zero    (x ∷ _)   = x
lookupEnv (suc n) (_ ∷ env) = lookupEnv n env

-- this is the evaluate function. Extremely funny that the blog just called it _[_]. 
_[_] : ∀ {n} {Γ : Ctx n} {τ} → Env Γ → Term Γ τ → ⟦ τ ⟧
env [ var v refl ] = lookupEnv v env
env [ lit n      ] = n
env [ t ⊕ u     ] = env [ t ] + env [ u ]
env [ t ∙ u      ] = (env [ t ]) (env [ u ])
env [ lam t      ] = λ x → (x ∷ env) [ t ] 


-- the below is less interesting (for now) but I'll include it since its in the blog
record Optimised {n} {Γ : Ctx n} {σ} (t : Term Γ σ) : Set where
  constructor opt
  field
    optimised : Term Γ σ
    sound     : ∀ {env} → env [ t ] ≡ env [ optimised ]

postulate ext : ∀ {A B : Set} {f g : A → B} → ({x : A} → f x ≡ g x) → f ≡ g
cfold : ∀ {n} {Γ : Ctx n} {τ} (t : Term Γ τ) → Optimised t
cfold (var v p) = opt (var v p) refl
cfold (lit x)   = opt (lit x)   refl
cfold (t ∙ u) with cfold t | cfold u
... | opt t′ p | opt u′ q = opt (t′ ∙ u′) (cong₂ _$_ p q)
cfold (lam t) with cfold t
... | opt t′ p = opt (lam t′) (ext p)
cfold (t ⊕ u) with cfold t | cfold u
... | opt (lit n) p | opt (lit m) q = opt (lit (n + m)) (cong₂ _+_ p q)
... | opt t′      p | opt u′      q = opt (t′ ⊕ u′) (cong₂ _+_ p q)