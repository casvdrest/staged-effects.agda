{-# OPTIONS --type-in-type --overlapping-instances #-}

module Lang where

open import Function

open import Data.Nat
open import Data.Sum
open import Data.Maybe


-- Step 1: import basic library functionality
open import Denote

-- Step 2: import effects
open import Effects.Nat
open import Effects.State
open import Effects.Lambda

-- Step 3: import object language constructors
open import Expression.Nat
open import Expression.State ℕ
open import Expression.Lambda

-- Step 4: assemble eDSL
module _ where

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

  Expr = NatExpr ∪ StateExpr ∪ LamExpr 

  ⟦_⟧ : μ Expr → Tree id (NatOpSig Val ⊞ StateSig ℕ ⊞ LamOpSig Val) Val
  ⟦_⟧ = ⟪ ⟦nat⟧ `⊙ ⟦state⟧ `⊙ ⟦lambda⟧ ⟫


-- Examples 
module _ where 

  `x `y `z : Name
  `x = 0
  `y = 1
  `z = 2

  -- let x = (λ y → put 1337) in 42 
  prog₀ : μ Expr
  prog₀ = letbindᴱ `x (absᴱ `y (putᴱ (natᴱ 1337))) (putᴱ (natᴱ 42))

  
