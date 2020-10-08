module Staged.Value.Core where

open import Function

open import Data.Maybe
open import Data.Sum

module _ where

  record _⊂_ (V₁ V₂ : Set) : Set where 
    field injectᵛ  : V₁ → V₂
          projectᵛ : V₂ → Maybe V₁

  open _⊂_ ⦃...⦄ public 

{-
  instance ⊂-refl : ∀ {V} → V ⊂ V 
  _⊂_.inject  ⊂-refl = id
  _⊂_.project ⊂-refl = just

  instance ⊂-left : ∀ {V₁ V₂} → V₁ ⊂ (V₁ ⊎ V₂)
  _⊂_.inject  ⊂-left = inj₁
  _⊂_.project ⊂-left (inj₁ x) = just x
  _⊂_.project ⊂-left (inj₂ y) = nothing

  instance ⊂-right : ∀ {V₁ V₂ V₃} → ⦃ V₁ ⊂ V₃ ⦄ → V₁ ⊂ (V₂ ⊎ V₃) 
  _⊂_.inject  ⊂-right = inj₂ ∘ inject
  _⊂_.project ⊂-right (inj₁ x) = nothing
  _⊂_.project ⊂-right (inj₂ y) = project y
-}
  
