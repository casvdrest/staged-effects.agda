{-# OPTIONS --type-in-type #-}

module Staged.Effects.State where

open import Function

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List

open import Staged.Denote

open import Relation.Binary.PropositionalEquality

open import Category.Functor

module _ where

  open RawFunctor ⦃...⦄
  open Sig

  data StateOp (H : Set) : Set where
    `get : StateOp H
    `put : (h : H) → StateOp H

  StateSig : Set → Sig
  S₁ (StateSig H) = StateOp H
  P₁ (StateSig H) `get = H
  P₁ (StateSig H) (`put _) = ⊤
  S₂ (StateSig H) _ = ⊥

  variable A B H : Set

  hSt'' :  ⦃ RawFunctor L ⦄ →
           H → Tree L (StateSig H ⊕ ζ) A →
           Tree ((H ×_) ∘ L) ζ (H × A)
  hSt'' h (leaf x) = leaf (h , x)
  hSt'' h (node (inj₁ `get) l _ k) = hSt'' h (k (const h <$> l))
  hSt'' _ (node (inj₁ (`put h)) l _ k) = hSt'' h (k l)
  hSt'' h (node (inj₂ c) l st k) =
    node  c (h , l)
          (λ{ z (h' , l) → hSt'' h' (st z l) })
          (λ{ (h' , lr) → hSt'' h' (k lr) })

  open _⊏_ ⦃...⦄

  get : ⦃ StateSig H ⊏ ζ ⦄ → Tree id ζ H
  get ⦃ w ⦄ = node (inj `get) tt
                   (λ z _ → ⊥-elim (subst id (S₂≡ ⦃ w ⦄) z))
                   (λ r   → return (subst id (P₁≡ ⦃ w ⦄) r))

  put : ⦃ StateSig H ⊏ ζ ⦄ → H → Tree id ζ H
  put ⦃ w ⦄ s = node (inj (`put s)) tt
                     (λ z _ → ⊥-elim (subst id (S₂≡ ⦃ w ⦄) z))
                     (const $ return s) 
