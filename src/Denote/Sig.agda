module Denote.Sig where

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ-syntax ; uncurry)
open import Data.Maybe

open import Function using (id ; const ; _∘_)
open import Level

-- Definition, extension and fixpoint
module _ where

  variable ℓ : Level

  record Sig : Set₁ where
    constructor _▹_
    field S : Set
          P : S → Set

  ⟦_⟧ᶜ : Sig → (Set ℓ → Set ℓ)
  ⟦ S ▹ P ⟧ᶜ X = Σ[ s ∈ S ] (P s → X)

  data μ {ℓ} (σ : Sig) : Set ℓ where
    ⟨_⟩ : ⟦ σ ⟧ᶜ (μ {ℓ} σ) → μ σ


-- Map/Fold
module _ where

  variable 
           A B : Set ℓ
           σ σ₁ σ₂ σ₃ : Sig

  mapᶜ : (f : A → B) → ⟦ σ ⟧ᶜ A → ⟦ σ ⟧ᶜ B 
  mapᶜ f (s , p) = s , f ∘ p

  infix 5 _⇒_
  _⇒_ : ∀ {ℓ} → (σ : Sig) → (A : Set ℓ) → Set ℓ
  σ ⇒ A = ⟦ σ ⟧ᶜ A → A
  
  foldᶜ : σ ⇒ A → μ {ℓ} σ → A
  foldᶜ f ⟨ s , p ⟩ = f (s , foldᶜ f ∘ p)

-- Combinators 
module _ where

  open Sig

  infixr 10 _∪_
  _∪_ : (σ₁ σ₂ : Sig) → Sig
  S (σ₁ ∪ σ₂) = S σ₁ ⊎ S σ₂
  P (σ₁ ∪ σ₂) (inj₁ x) = P σ₁ x
  P (σ₁ ∪ σ₂) (inj₂ y) = P σ₂ y

  infixr 10 _∩_
  _∩_ : (σ₁ σ₂ : Sig) → Sig
  S (σ₁ ∩ σ₂) = S σ₁ × S σ₂
  P (σ₁ ∩ σ₂) = uncurry λ s₁ s₂ → P σ₁ s₁ ⊎ P σ₂ s₂


-- Algebra composition
module _ where 

  infixr 10 _⊙_
  _⊙_ :   (σ₁ ⇒ A)
        → (σ₂ ⇒ A)
          -----------
        → σ₁ ∪ σ₂ ⇒ A
        
  (f ⊙ g) (inj₁ x , p) = f (x , p)
  (f ⊙ g) (inj₂ y , p) = g (y , p)

module _ where

  open import Value.Core

  _⊰_ : (σ₁ σ₂ : Sig) → Set₁
  σ₁ ⊰ σ₂ = ∀ {A} → ⟦ σ₁ ⟧ᶜ A ⊂ ⟦ σ₂ ⟧ᶜ A

  postulate instance ⊰-refl : σ ⊰ σ
  postulate instance ⊰-left : σ₁ ⊰ (σ₁ ∪ σ₂)
  postulate instance ⊰-right : ⦃ σ₁ ⊰ σ₃ ⦄ → σ₁ ⊰ (σ₂ ∪ σ₃)

  injectᶜ : ⦃ σ₁ ⊰ σ₂ ⦄ → ⟦ σ₁ ⟧ᶜ (μ σ₂) → μ {zero} σ₂
  injectᶜ x = ⟨ inject x ⟩

  projectᶜ : ⦃ σ₁ ⊰ σ₂ ⦄ → μ {zero} σ₂ → Maybe (⟦ σ₁ ⟧ᶜ (μ {zero} σ₂))
  projectᶜ ⟨ x ⟩ = project x
