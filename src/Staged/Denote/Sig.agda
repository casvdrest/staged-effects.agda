module Staged.Denote.Sig where

open import Function using (id ; _∘_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst ; trans ; cong ; sym)

module _ where

  record Sig : Set₁ where
    constructor _▹_∣_▹_  
    field S₁ : Set
          P₁ : S₁ → Set
          S₂ : S₁ → Set
          P₂ : ∀ {s₁} → S₂ s₁ → Set

  open Sig

  infixr 15 _⊕_
  _⊕_ : (ζ₁ ζ₂ : Sig) → Sig
  S₁ (ζ₁ ⊕ ζ₂)             = S₁ ζ₁ ⊎ S₁ ζ₂
  P₁ (ζ₁ ⊕ ζ₂) (inj₁ x)    = P₁ ζ₁ x
  P₁ (ζ₁ ⊕ ζ₂) (inj₂ y)    = P₁ ζ₂ y
  S₂ (ζ₁ ⊕ ζ₂) (inj₁ x)    = S₂ ζ₁ x
  S₂ (ζ₁ ⊕ ζ₂) (inj₂ y)    = S₂ ζ₂ y
  P₂ (ζ₁ ⊕ ζ₂) {inj₁ x} r  = P₂ ζ₁ r
  P₂ (ζ₁ ⊕ ζ₂) {inj₂ y} r  = P₂ ζ₂ r

module _ where 

  infix 10 _⊏_
  record _⊏_ (ζ₁ ζ₂ : Sig) : Set₁ where 
    open Sig
    field  inj  : S₁ ζ₁ → S₁ ζ₂
           P₁≡ : ∀ {op} → P₁ ζ₂ (inj op) ≡ P₁ ζ₁ op 
           S₂≡ : ∀ {op} → S₂ ζ₂ (inj op) ≡ S₂ ζ₁ op
           P₂≡ : ∀ {op} {s₂ : S₂ ζ₂ (inj op)} → P₂ ζ₁ (subst id S₂≡ s₂) ≡ P₂ ζ₂ s₂

  variable ζ ζ₁ ζ₂ ζ₃ : Sig
             
  open _⊏_ ⦃...⦄

  instance ⊏-refl : ζ ⊏ ζ
  _⊏_.inj  ⊏-refl = id
  _⊏_.P₁≡ ⊏-refl = refl
  _⊏_.S₂≡ ⊏-refl = refl
  _⊏_.P₂≡ ⊏-refl = refl

  instance ⊏-left : ζ₁ ⊏ ζ₁ ⊕ ζ₂
  _⊏_.inj  ⊏-left = inj₁
  _⊏_.P₁≡ ⊏-left = refl
  _⊏_.S₂≡ ⊏-left = refl
  _⊏_.P₂≡ ⊏-left = refl

  
  eq≡ : ∀ {ℓ} {A : Set ℓ} {x y : A} → (eq₁ : x ≡ y) → (eq₂ : x ≡ y) → eq₁ ≡ eq₂
  eq≡ refl refl = refl

  instance ⊏-right : ⦃ ζ₁ ⊏ ζ₃ ⦄ → ζ₁ ⊏ ζ₂ ⊕ ζ₃  
  _⊏_.inj  ⊏-right = inj₂ ∘ inj 
  _⊏_.P₁≡ (⊏-right ⦃ w ⦄) {op}     rewrite (P₁≡ ⦃ w ⦄ {op}) = refl
  _⊏_.S₂≡ (⊏-right ⦃ w ⦄) {op}     rewrite (S₂≡ ⦃ w ⦄ {op}) = refl
  _⊏_.P₂≡ (⊏-right {ζ₁}  ⦃ w ⦄) {op} {z} rewrite (sym (P₂≡ ⦃ w ⦄ {op} {z})) =
    cong (Sig.P₂ ζ₁) let zeq = (S₂≡ ⦃ w ⦄ {op}) in cong (λ x → subst id x z) (eq≡ _ _)
