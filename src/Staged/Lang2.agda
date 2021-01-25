{-# OPTIONS --overlapping-instances #-}

module Staged.Lang2 where

open import Function

open import Data.Nat
open import Data.Sum
open import Data.Maybe
open import Data.List
open import Data.Product
open import Data.Bool

open import Relation.Binary.PropositionalEquality

open import Container
open import Staged.Denote

open import Staged.Effects.Nat
open import Staged.Effects.Lambda
open import Staged.Effects.NoOp

open import Staged.Expression.Nat
open import Staged.Expression.Lambda

module _ where

  data Ty : Set where
    tfun : (s t : Ty) → Ty
    tnat : Ty

  instance FunType⊂Ty : FunType Ty ⊂ Ty
  _⊂_.injectᵛ FunType⊂Ty (fun s t) = tfun s t
  _⊂_.projectᵛ FunType⊂Ty (tfun s t) = just (fun s t) 
  _⊂_.projectᵛ FunType⊂Ty tnat = nothing

  instance NatT⊂Ty : NatT Ty ⊂ Ty
  _⊂_.injectᵛ NatT⊂Ty tnat = tnat 
  _⊂_.projectᵛ NatT⊂Ty (tfun x x₁) = nothing
  _⊂_.projectᵛ NatT⊂Ty tnat = just tnat

  Expr = μ $ NatExpr ∪ LamExpr 

  LangSig = NatOpSig Ty ⊕ LamSig Ty ⊕ NoOpSig

  ⟦_⟧ : Expr → Tree id LangSig Ty
  ⟦_⟧ = ⟪ ⟦nat⟧ `⊙ ⟦lambda⟧ ⟫ 

  open Eq ⦃...⦄

  instance ty-eq : Eq Ty
  (ty-eq Eq.=? tfun s₁ t₁) (tfun s₂ t₂) = (s₁ =? s₂) ∧ (t₁ =? t₂)
  (ty-eq Eq.=? tfun x x₁) tnat = false
  (ty-eq Eq.=? tnat) (tfun y y₁) = false
  (ty-eq Eq.=? tnat) tnat = true

  operate : Tree id LangSig Ty → Ty → Maybe Ty
  operate x t with hLamCheck [] t (hNatCheck t x)
  ... | leaf nothing = nothing
  ... | leaf (just nothing) = nothing
  ... | leaf (just (just x₁)) = just x₁

  example : Expr
  example = abs' 0 (nat' 10) 

  ut : operate ⟦ example ⟧ (tfun tnat tnat) ≡ just tnat
  ut = refl
