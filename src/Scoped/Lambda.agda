module Scoped.Lambda where

open import Function

open import Data.Nat
open import Data.Sum
open import Data.Maybe using (Maybe ; just ; nothing ; maybe)
open import Data.List
open import Data.Product

open import Container
open import Scoped.Prog

module _ where

  open Con

  Name = ℕ

  Env : Set → Set
  Env V = List (Name × V)

  data LamScope : Set where
    `lambda : Name → LamScope

  LamSig : Set → Con
  S (LamSig V) = LamScope
  P (LamSig V) (`lambda n) = V

  data FetchOp (V : Set) : Set where
    `fetch : Name → FetchOp V

  FetchSig : Set → Con
  S (FetchSig V) = FetchOp V
  P (FetchSig V) (`fetch x) = V

module _ {V : Set} where

  postulate
    lookupₐ : {X : Set} → List (Name × X) → Name → Maybe X

  postulate CANNOT_BE_DEFINED : ∀ {A : Set} → A

  hLam :  Env V →
          Prog (FetchSig V ∪ σ) (LamSig V ∪ γ) A →
          Prog σ γ (Maybe A)
  hLam _ (var x) = var (just x)
  hLam E (op (inj₁ (`fetch x)) k) =
    maybe (hLam E ∘ k) (var nothing) (lookupₐ E x)
  hLam E (op (inj₂ c) k) = op c (hLam E ∘ k) 
  hLam E (scope (inj₁ (`lambda n)) sc k) = hLam E (k CANNOT_BE_DEFINED)
  hLam E (scope (inj₂ g) sc k) =
    scope g (hLam E ∘ sc) (maybe (hLam E ∘ k) (var nothing))
