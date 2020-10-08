open import Level
open import Function
open import Data.Product
open import Data.Sum

module Container where

module _ where

  record Con : Set₁ where
    constructor _▹_ 
    field S : Set
          P : S → Set 

  open Con public

  ⟦_⟧ᶜ : Con → Set → Set
  ⟦ S ▹ P ⟧ᶜ X = ∃ λ s → P s → X

  data μ (C : Con) : Set where
    ⟨_⟩ : ⟦ C ⟧ᶜ (μ C) → μ C

  variable
    C C₁ C₂ C₃ : Con
    V V₁ V₂ V₃ : Set
    A B : Set

  mapᶜ : (A → B) → ⟦ C ⟧ᶜ A → ⟦ C ⟧ᶜ B 
  mapᶜ f (s , p) = s , f ∘ p

  foldᶜ : (⟦ C ⟧ᶜ A → A) → μ C → A
  foldᶜ f ⟨ s , p ⟩ = f (s , foldᶜ f ∘ p)

  infixr 10 _∪_
  _∪_ : (C₁ C₂ : Con) → Con
  S (C₁ ∪ C₂) = S C₁ ⊎ S C₂
  P (C₁ ∪ C₂) (inj₁ x) = P C₁ x
  P (C₁ ∪ C₂) (inj₂ y) = P C₂ y

  record _≺_ (C₁ C₂ : Con) : Set₁ where
    field inj : ⟦ C₁ ⟧ᶜ A → ⟦ C₂ ⟧ᶜ A

  open _≺_  ⦃...⦄

  instance ≺-refl : C ≺ C
  _≺_.inj ≺-refl = id

  instance ≺-left : C₁ ≺ (C₁ ∪ C₂)
  _≺_.inj ≺-left (s , p) = inj₁ s , p

  instance ≺-right : ⦃ C₁ ≺ C₃ ⦄ → C₁ ≺ (C₂ ∪ C₃)
  _≺_.inj ≺-right x with inj x
  ... | s , p = inj₂ s , p

  inject : ⦃ C₁ ≺ C₂ ⦄ → ⟦ C₁ ⟧ᶜ (μ C₂) → μ C₂
  inject x = ⟨ inj x ⟩

module _ where 
  
  record _⇒_ (C : Con) (V : Set) : Set where
    field run : ⟦ C ⟧ᶜ V → V

  open _⇒_ public
  infix 9 _⇒_

  infixr 15 _⊙_
  _⊙_ : (C₁ ⇒ V) → (C₂ ⇒ V) → (C₁ ∪ C₂ ⇒ V)
  run (f ⊙ g) (inj₁ x , p) = run f (x , p)
  run (f ⊙ g) (inj₂ y , p) = run g (y , p)
 
