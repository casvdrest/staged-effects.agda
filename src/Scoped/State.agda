module Scoped.State where

open import Function

open import Data.Unit
open import Data.Product
open import Data.Sum

open import Scoped.Sig
open import Scoped.Prog

module _ where

  open Sig
  
  data StateCmd (S : Set) : Set where
    `get : StateCmd S
    `put : (s : S) → StateCmd S

  StateSig : Set → Sig
  C (StateSig S) = StateCmd S
  R (StateSig S) `get = S
  R (StateSig S) (`put s) = ⊤

  variable S : Set
  
  hSt' : S → Prog (StateSig S ⊕ σ) γ A → Prog σ γ (A × S)
  hSt' s  (var x) = var (x , s)
  hSt' s  (op (inj₁ `get) k) = hSt' s (k s)
  hSt' _  (op (inj₁ (`put s)) k) = hSt' s (k tt)
  hSt' s  (op (inj₂ y) k) = op y (hSt' s ∘ k)
  hSt' s  (scope g sc k) =
    scope g (hSt' s ∘ sc) (λ{ (x , s) → hSt' s (k x) })
