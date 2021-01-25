module Staged.Effects.Nat where

open import Function

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Maybe

open import Staged.Denote
open import Staged.Value.Core

open import Category.Functor

open import Relation.Binary.PropositionalEquality

module _ where

  open Sig

  data NatOp (V : Set) : Set where
    `nat : ℕ → NatOp V

  NatOpSig : Set → Sig
  S₁ (NatOpSig V) = NatOp V
  P₁ (NatOpSig V) (`nat n) = V
  S₂ (NatOpSig V) (`nat n) = ⊥
  P₂ (NatOpSig V) {`nat x₁} ()


  variable T A B : Set

  data NatT (T : Set) : Set where
    tnat : NatT T

module _ where 

  
  open RawFunctor ⦃...⦄

  try : Maybe A → (A → Tree L ζ (Maybe B)) → Tree L ζ (Maybe B)
  try m f = maybe f (leaf nothing) m

  hNatCheck : ⦃ NatT T ⊂ T ⦄ → ⦃ RawFunctor L ⦄ → T → Tree L (NatOpSig T ⊕ ζ) A → Tree (Maybe ∘ L) ζ (Maybe A)
  hNatCheck t (leaf x) = leaf (just x)
  hNatCheck t (node (inj₁ (`nat x)) l st k) = try (projectᵛ t) λ where tnat → hNatCheck t (k (const t <$> l))
  hNatCheck t (node (inj₂ c) l st k) = node c (just <$> l) (λ r → flip try λ l → hNatCheck t (st r l)) (flip try λ l → hNatCheck t (k l))

module _ {V : Set} where 

  open RawFunctor ⦃...⦄

  hNat' : ⦃ ℕ ⊂ V ⦄ → ⦃ RawFunctor L ⦄ → Tree L (NatOpSig V ⊕ ζ) A → Tree L ζ A
  hNat' (leaf x) = leaf x
  hNat' (node (inj₁ (`nat n)) l sc k) = hNat' (k (const (injectᵛ n) <$> l))
  hNat' (node (inj₂ c) l sc k) =
    node c l
         (λ z → hNat' ∘ sc z)
         (hNat' ∘ k)

  open _⊏_ ⦃...⦄

  nat : ⦃ NatOpSig V ⊏ ζ ⦄ → ℕ → Tree id ζ V
  nat ⦃ w ⦄ n =
    node (inj (`nat n)) tt
         (λ z _ → ⊥-elim (subst id (S₂≡ ⦃ w ⦄) z))
         (λ r → return (subst id (P₁≡ ⦃ w ⦄) r))
