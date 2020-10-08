{-# OPTIONS --type-in-type --overlapping-instances #-}

module Staged.Lang where

open import Function

open import Data.Nat
open import Data.Sum
open import Data.Maybe
open import Data.List
open import Data.Product

open import Relation.Binary.PropositionalEquality


-- Step 1: import basic library functionality
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

-- Step 4: assemble eDSL
module _ where

  -- Choose a value type
  data Val : Set where
    vnat  : ℕ → Val
    vclos : Closure Val → Val

  instance ℕ⊂Val : ℕ ⊂ Val
  _⊂_.inject ℕ⊂Val = vnat
  _⊂_.project ℕ⊂Val (vnat x) = just x
  _⊂_.project ℕ⊂Val (vclos x) = nothing

  instance Closure⊂Val : Closure Val ⊂ Val
  _⊂_.inject Closure⊂Val = vclos
  _⊂_.project Closure⊂Val (vnat x) = nothing
  _⊂_.project Closure⊂Val (vclos x) = just x


  -- Compose Expression type
  Expr   = NatExpr ∪ StateExpr ∪ LamExpr 


  -- Compose effect signature
  LamSig = NatOpSig Val ⊞ StateSig ℕ ⊞ LamOpSig Val ⊞ NoOpSig


  -- Build semantic function
  ⟦_⟧ : μ Expr → Tree id LamSig Val
  ⟦_⟧ = ⟪ ⟦nat⟧ `⊙ ⟦state⟧ `⊙ ⟦lambda⟧ ⟫

  -- Define handler application
  operate : Tree id LamSig Val → ℕ → Maybe Val
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

  example₀ : μ Expr
  example₀ = let' `x (abs' `y (put' $ nat' 10) ) $
             let' `z (app' (var' `x) (var' `x))  $
             let' `u (app' (var' `x) (var' `x))  $ get'


  -- ut₀ : operate ⟦ example₀ ⟧ 20 ≡ {!!}
  -- ut₀ = refl

  -- example₁ : Expr
  -- example₁ =
  --   let' 0 (lam 1 (plus (var 1) (var 1))) $
  --   call (var 0) (num 4)

  -- ut₁ : operate (denote example₁) ≡ just (numv 8)
  -- ut₁ = refl

  -- example₂ : Expr
  -- example₂ =
  --   let' 0 (lam 1 (update (plus recall (num 1)))) $
  --   let' 2 (lam 3 (update (plus recall (num 2)))) $
  --   let' 4 (call (var 0) (num 0)) $
  --   let' 5 (call (var 2) (num 0)) $
  --   recall

  -- ut₂ : operate (denote example₂) ≡ just (numv 3)
  -- ut₂ = refl
  
