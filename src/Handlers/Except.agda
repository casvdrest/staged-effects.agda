module Handlers.Except where

open import Function

open import Data.Empty
open import Data.Maybe
open import Data.Sum

open import Container
open import Handlers.IOTree

open import Relation.Binary.PropositionalEquality

module _ where 

  open _≪_ ⦃...⦄

  variable X : Set

  data ExcCmd (X : Set) : Set where
    `throw : X → ExcCmd X

  ExcSig : Set → Con
  S (ExcSig X) = ExcCmd X
  P (ExcSig X) (`throw x) = ⊥

  handleExc : IO (ExcSig X ∪ σ) A → IO σ (Maybe A)
  handleExc =
    fold (end ∘ just)
         λ where
           (inj₁ (`throw x)) p → end nothing
           (inj₂ c) p → cmd c p 


  throw : ⦃ ExcSig X ≪ σ ⦄ → X → IO σ A
  throw ⦃ w ⦄ e = cmd (inj (`throw e)) (⊥-elim ∘ subst id (ret≡ ⦃ w ⦄))
