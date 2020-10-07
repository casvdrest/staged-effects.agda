module Effects.State where

open import Function

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List

open import Denote.Sig
open import Denote.StagedSig
open import Denote.Tree

open import Relation.Binary.PropositionalEquality

open import Category.Functor

module _ where

  open RawFunctor ⦃...⦄
  open StagedSig

  data StateCmd (S : Set) : Set where
    `get : StateCmd S
    `put : (s : S) → StateCmd S

  StateSig : Set → StagedSig
  C (StateSig S) = StateCmd S
  R (StateSig S) `get = S
  R (StateSig S) (`put s) = ⊤
  Z (StateSig S) _ = ⊥

  variable S : Set

  hSt'' :  ⦃ RawFunctor L ⦄ →
           S → Tree L (StateSig S ⊞ ζ) A →
           Tree ((S ×_) ∘ L) ζ (S × A)
  hSt'' s (leaf x) = leaf (s , x)
  hSt'' s (node (inj₁ `get) l _ k) = hSt'' s (k (const s <$> l))
  hSt'' _ (node (inj₁ (`put s)) l _ k) = hSt'' s (k l)
  hSt'' s (node (inj₂ c) l st k) =
    node  c (s , l)
          (λ{ z (s' , l) → hSt'' s' (st z l) })
          (λ{ (s' , lr) → hSt'' s' (k lr) })

  open _⊏_ ⦃...⦄

  get : ⦃ StateSig S ⊏ ζ ⦄ → Tree id ζ S
  get ⦃ w ⦄ = node (inj `get) tt
                   (λ z _ → ⊥-elim (subst id (Z≡ ⦃ w ⦄) z))
                   (λ r   → return (subst id (R≡ ⦃ w ⦄) r))

  put : ⦃ StateSig S ⊏ ζ ⦄ → S → Tree id ζ S
  put {S = S} ⦃ w ⦄ s = node (inj (`put s)) tt
               (λ z _ → ⊥-elim (subst id (Z≡ ⦃ w ⦄) z))
               (const $ return s) 
