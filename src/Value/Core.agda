module Value.Core where

open import Data.Maybe

module _ where

  record _`⊏_ (V₁ V₂ : Set) : Set where 
    field inject  : V₁ → V₂
          project : V₂ → Maybe V₁

  open _`⊏_ ⦃...⦄ public
