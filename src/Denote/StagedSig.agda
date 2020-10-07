module Denote.StagedSig where

open import Function using (id ; _∘_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

module _ where

  record StagedSig : Set₁ where
    constructor _▹_∣_▹_  
    field C : Set
          R : C → Set
          Z : C → Set
          I : ∀ {c} → Z c → Set

  open StagedSig

  infixr 15 _⊞_
  _⊞_ : (ζ₁ ζ₂ : StagedSig) → StagedSig
  C (ζ₁ ⊞ ζ₂)             = C ζ₁ ⊎ C ζ₂
  R (ζ₁ ⊞ ζ₂) (inj₁ x)    = R ζ₁ x
  R (ζ₁ ⊞ ζ₂) (inj₂ y)    = R ζ₂ y
  Z (ζ₁ ⊞ ζ₂) (inj₁ x)    = Z ζ₁ x
  Z (ζ₁ ⊞ ζ₂) (inj₂ y)    = Z ζ₂ y
  I (ζ₁ ⊞ ζ₂) {inj₁ x} r  = I ζ₁ r
  I (ζ₁ ⊞ ζ₂) {inj₂ y} r  = I ζ₂ r

module _ where 

  infix 10 _⊏_
  record _⊏_ (ζ₁ ζ₂ : StagedSig) : Set₁ where 
    open StagedSig
    field  inj  : C ζ₁ → C ζ₂
           ret≡ : ∀ {op} → R ζ₂ (inj op) ≡ R ζ₁ op 

  variable ζ ζ₁ ζ₂ ζ₃ : StagedSig

  open _⊏_ ⦃...⦄

  instance ⊏-refl : ζ ⊏ ζ
  _⊏_.inj  ⊏-refl = id
  _⊏_.ret≡ ⊏-refl = refl

  instance ⊏-left : ζ₁ ⊏ ζ₁ ⊞ ζ₂
  _⊏_.inj  ⊏-left = inj₁
  _⊏_.ret≡ ⊏-left = refl

  instance ⊏-right : ⦃ ζ₁ ⊏ ζ₃ ⦄ → ζ₁ ⊏ ζ₂ ⊞ ζ₃  
  _⊏_.inj  ⊏-right = inj₂ ∘ inj 
  _⊏_.ret≡ (⊏-right ⦃ w ⦄) {op} rewrite (ret≡ ⦃ w ⦄ {op}) = refl

  
