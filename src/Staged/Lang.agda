{-# OPTIONS --overlapping-instances #-}

module Staged.Lang where

open import Function

open import Data.Nat
open import Data.Sum
open import Data.Maybe
open import Data.List
open import Data.Product

open import Relation.Binary.PropositionalEquality

-- Step 1: import basic library functionality
open import Container
open import Staged.Denote

-- Step 2: import effects
open import Staged.Effects.Nat
open import Staged.Effects.State
open import Staged.Effects.Lambda
open import Staged.Effects.NoOp

-- Step 3: import object language constructors
open import Staged.Expression.Nat
open import Staged.Expression.State ℕ
open import Staged.Expression.Lambda
open import Staged.Expression.Seq

-- Step 4: assemble eDSL
module _ where

  -- Choose a value type
  data Val : Set where
    vnat  : ℕ → Val
    vclos : Closure Val → Val

  instance ℕ⊂Val : ℕ ⊂ Val
  _⊂_.injectᵛ ℕ⊂Val = vnat
  _⊂_.projectᵛ ℕ⊂Val (vnat x) = just x
  _⊂_.projectᵛ ℕ⊂Val (vclos x) = nothing

  instance Closure⊂Val : Closure Val ⊂ Val
  _⊂_.injectᵛ Closure⊂Val = vclos
  _⊂_.projectᵛ Closure⊂Val (vnat x) = nothing
  _⊂_.projectᵛ Closure⊂Val (vclos x) = just x


  -- Compose Expression type
  Expr = μ $ SeqExpr ∪ NatExpr ∪ StateExpr ∪ LamExpr


  -- Compose effect signature
  LangSig = NatOpSig Val ⊕ StateSig ℕ ⊕ LamSig Val ⊕ NoOpSig


  -- Build semantic function
  ⟦_⟧ : Expr → Tree id LangSig Val
  ⟦_⟧ = ⟪ ⟦seq⟧ `⊙ ⟦nat⟧ `⊙ ⟦state⟧ `⊙ ⟦lambda⟧ ⟫

  -- Define handler application
  operate : Tree id LangSig Val → ℕ → Maybe Val
  operate x n with hLam' [] [] n (hSt'' 0 (hNat' x))
  ... | leaf nothing              = nothing
  ... | leaf (just (_ , _ , snd)) = just snd


-- Step 5: profit
module _ where 

  `x `y `z `u `v `w : Name
  `x = 0
  `y = 1
  `z = 2
  `u = 3
  `v = 4
  `w = 5

  -- put 1 >> let x = put 10 in get  
  example₀ : Expr
  example₀ = put' (nat' 1) >>' let' `x (put' (nat' 10)) get'

  -- put 1 >>' let x = λ y → put 10 in get 
  example₁ : Expr
  example₁ = put' (nat' 1) >>' let' `x (abs' `y (put' (nat' 10))) get'

  example₂ : Expr
  example₂ = app' (abs' `x (var' `x)) (nat' 4)

  example₃ : Expr
  example₃ = let' `x (abs' `y (var' `y)) (app' (var' `x) (nat' 5))

  example₄ : Expr
  example₄ =
    put' (nat' 0) >>'
    let' `x (abs' `y get') (put' (nat' 42) >>' app' (var' `x) (nat' 0))

  ut₀ : operate ⟦ example₀ ⟧ 5 ≡ just (vnat 10)
  ut₀ = refl

  ut₁ : operate ⟦ example₁ ⟧ 5 ≡ just (vnat 1) 
  ut₁ = refl

  ut₂ : operate ⟦ example₂ ⟧ 4 ≡ just (vnat 4)
  ut₂ = refl
  
  ut₃ : operate ⟦ example₃ ⟧ 6 ≡ just (vnat 5)
  ut₃ = refl

  ut₄ : operate ⟦ example₄ ⟧ 5 ≡ just (vnat 42)
  ut₄ = refl

 
