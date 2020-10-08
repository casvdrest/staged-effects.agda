open import Function
open import Data.Sum
open import Relation.Binary.PropositionalEquality

module Scoped.Sig where

------------------
--- signatures ---
------------------

record Sig : Set₁ where
  field
    C : Set
    R : C → Set

open Sig

infixr 13 _⊕_

_⊕_ : Sig → Sig → Sig
C (σ₁ ⊕ σ₂) = C σ₁ ⊎ C σ₂
R (σ₁ ⊕ σ₂) (inj₁ c) = R σ₁ c
R (σ₁ ⊕ σ₂) (inj₂ c) = R σ₂ c

record _≺_ (σ₁ σ₂ : Sig) : Set₁ where
  open Sig
  field
    inj   : C σ₁ → C σ₂
    ret≡  : ∀ {op} → R σ₂ (inj op) ≡ R σ₁ op

open _≺_ ⦃ ... ⦄

variable σ σ₁ σ₂ σ₃ σ′ γ γ₁ γ₂ γ₃ γ′ : Sig

right≺ : ⦃ σ₁ ≺ σ₃ ⦄ → σ₁ ≺ (σ₂ ⊕ σ₃)
_≺_.inj right≺ = inj₂ ∘ inj
_≺_.ret≡ (right≺ ⦃ w ⦄) = subst (λ x → _ ≡ x) (ret≡ ⦃ w ⦄) refl


instance
  simply≺ : σ ≺ σ
  _≺_.inj simply≺ = id
  _≺_.ret≡ simply≺ = refl

  left≺ : σ₁ ≺ (σ₁ ⊕ σ₂)
  _≺_.inj left≺ = inj₁
  _≺_.ret≡ left≺ = refl

  simple-right≺ : σ₂ ≺ (σ₁ ⊕ σ₂)
  simple-right≺ = right≺


swap≺ : (σ₁ ⊕ σ₂) ≺ (σ₂ ⊕ σ₁)
_≺_.inj swap≺ = swap
_≺_.ret≡ swap≺ {inj₁ _} = refl
_≺_.ret≡ swap≺ {inj₂ _} = refl

assoc≺ʳ : ((σ₁ ⊕ σ₂) ⊕ σ₃) ≺ (σ₁ ⊕ σ₂ ⊕ σ₃)
_≺_.inj assoc≺ʳ = assocʳ
_≺_.ret≡ assoc≺ʳ {inj₁ (inj₁ x)} = refl
_≺_.ret≡ assoc≺ʳ {inj₁ (inj₂ y)} = refl
_≺_.ret≡ assoc≺ʳ {inj₂ y} = refl

assoc≺ˡ : (σ₁ ⊕ σ₂ ⊕ σ₃) ≺ ((σ₁ ⊕ σ₂) ⊕ σ₃)
_≺_.inj assoc≺ˡ = assocˡ
_≺_.ret≡ assoc≺ˡ {inj₁ x} = refl
_≺_.ret≡ assoc≺ˡ {inj₂ (inj₁ x)} = refl
_≺_.ret≡ assoc≺ˡ {inj₂ (inj₂ y)} = refl

trans≺ : σ₁ ≺ σ₂ → σ₂ ≺ σ₃ → σ₁ ≺ σ₃
_≺_.inj (trans≺ w₁ w₂) = inj ⦃ w₂ ⦄ ∘ inj ⦃ w₁ ⦄
_≺_.ret≡ (trans≺ w₁ w₂) = trans (ret≡ ⦃ w₂ ⦄) (ret≡ ⦃ w₁ ⦄)
