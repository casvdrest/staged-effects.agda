module Scoped.LetBind where

open import Function
open import Level

open import Data.Nat
open import Data.Product
open import Data.List
open import Data.Unit
open import Data.Sum
open import Data.Maybe using (Maybe ; just ; nothing ; maybe)

open import Container
open import Scoped.Prog

module _ where

  open Con

  Name = ℕ

  Env : Set → Set
  Env V = List (Name × V)

  data FetchOp (V : Set) : Set where
     `fetch : Name → FetchOp V

  FetchSig : Set → Con
  S (FetchSig V) = FetchOp V
  P (FetchSig V) (`fetch x) = V

  data LetScope (V : Set) : Set where
     `letbind : Name → V → LetScope V

  LetSig : Set → Con
  S (LetSig V) = LetScope V
  P (LetSig V) (`letbind n v) = ⊤


module _ {V : Set} where 

  postulate
    lookupₐ : ∀ {X : Set} → List (Name × X) → Name → Maybe X

  hLet :  Env V → Prog (FetchSig V ∪ σ) (LetSig V ∪ γ) A →
          Prog σ γ (Maybe A)
  hLet _ (var x) = var (just x)
  hLet E (op (inj₁ (`fetch x)) k) =
     maybe  (hLet E ∘ k) (var nothing)
               (lookupₐ E x)
  hLet E (op (inj₂ c) k) = op c (hLet E ∘ k) 
  hLet E (scope (inj₁ (`letbind n v)) sc k) =
     hLet ((n , v) ∷ E) (sc tt) >>=
       maybe (hLet E ∘ k) (var nothing)
  hLet E (scope (inj₂ g) sc k) =
     scope g  (hLet E ∘ sc) (maybe (hLet E ∘ k) (var nothing))
