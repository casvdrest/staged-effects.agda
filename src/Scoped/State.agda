module Scoped.State where

open import Function

open import Data.Unit
open import Data.Product
open import Data.Sum

open import Container
open import Scoped.Prog

module _ where

  open Con
  
  data StateCmd (H : Set) : Set where
    `get : StateCmd H
    `put : (h : H) → StateCmd H

  StateSig : Set → Con
  S (StateSig H) = StateCmd H
  P (StateSig H) `get = H
  P (StateSig H) (`put s) = ⊤

  variable H : Set
  
  hSt' : H → Prog (StateSig H ∪ σ) γ A → Prog σ γ (A × H)
  hSt' h  (var x) = var (x , h)
  hSt' h  (op (inj₁ `get) k) = hSt' h (k h)
  hSt' _  (op (inj₁ (`put h)) k) = hSt' h (k tt)
  hSt' h  (op (inj₂ y) k) = op y (hSt' h ∘ k)
  hSt' h  (scope g sc k) =
    scope g (hSt' h ∘ sc) (λ{ (x , h') → hSt' h' (k x) })
