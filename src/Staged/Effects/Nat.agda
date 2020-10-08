{-# OPTIONS --type-in-type #-}

module Staged.Effects.Nat where

open import Function

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Staged.Denote
open import Staged.Value.Core

open import Category.Functor

open import Relation.Binary.PropositionalEquality

module _ where

  open Sig

  data NatOp (V : Set) : Set where
    `nat : V → NatOp V

  NatOpSig : Set → Sig
  S₁ (NatOpSig V) = NatOp V
  P₁ (NatOpSig V) (`nat n) = V
  S₂ (NatOpSig V) (`nat n) = ⊥
  P₂ (NatOpSig V) {`nat x₁} ()

module _ {V : Set} where 

  open RawFunctor ⦃...⦄

  variable A : Set

  hNat' : ⦃ ℕ ⊂ V ⦄ → ⦃ RawFunctor L ⦄ → Tree L (NatOpSig V ⊕ ζ) A → Tree L ζ A
  hNat' (leaf x) = leaf x
  hNat' (node (inj₁ (`nat n)) l sc k) = hNat' (k (const n <$> l))
  hNat' (node (inj₂ c) l sc k) =
    node c l
         (λ z → hNat' ∘ sc z)
         (hNat' ∘ k)

  open _⊏_ ⦃...⦄

  nat : ⦃ NatOpSig V ⊏ ζ ⦄ → ⦃ ℕ ⊂ V ⦄ → ℕ → Tree id ζ V
  nat ⦃ w ⦄ n =
    node (inj (`nat (injectᵛ n))) tt
         (λ z _ → ⊥-elim (subst id (S₂≡ ⦃ w ⦄) z))
         (λ r → return (subst id (P₁≡ ⦃ w ⦄) r))
