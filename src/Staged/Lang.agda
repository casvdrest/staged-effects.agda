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
open import Staged.Effects.Except
open import Staged.Effects.NoOp

-- Step 3: import object language constructors
open import Staged.Expression.Nat
open import Staged.Expression.State ℕ
open import Staged.Expression.Lambda
open import Staged.Expression.Seq
open import Staged.Expression.Except

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
  Expr = μ $ SeqExpr ∪ ExcExpr ∪ NatExpr ∪ StateExpr ∪ LamExpr


  -- Compose effect signature
  LangSig = NatOpSig Val ⊕ StateSig ℕ ⊕ ExcSig Val Val ⊕ LamSig Val ⊕ NoOpSig


  -- Build semantic function
  ⟦_⟧ : Expr → Tree id LangSig Val
  ⟦_⟧ = ⟪ ⟦seq⟧ `⊙ ⟦except⟧ `⊙ ⟦nat⟧ `⊙ ⟦state⟧ `⊙ ⟦lambda⟧ ⟫

  -- Define handler application
  operate : Tree id LangSig Val → ℕ → Maybe (Val ⊎ Val)
  operate x n with hLam' [] [] n (hEx (hSt'' 0 (hNat' x)))
  ... | leaf nothing = nothing
  ... | leaf (just (_ , (inj₁ (_ , v)))) = just (inj₁ v)
  ... | leaf (just (_ , (inj₂ (_ , v)))) = just (inj₂ v)


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

  ut₀ : operate ⟦ example₀ ⟧ 5 ≡ just (inj₁ (vnat 10))
  ut₀ = refl

  -- put 1 >>' let x = λ y → put 10 in get 
  example₁ : Expr
  example₁ = put' (nat' 1) >>' let' `x (abs' `y (put' (nat' 10))) get'

  ut₁ : operate ⟦ example₁ ⟧ 5 ≡ just (inj₁ (vnat 1))
  ut₁ = refl

  example₂ : Expr
  example₂ = app' (abs' `x (var' `x)) (nat' 4)

  ut₂ : operate ⟦ example₂ ⟧ 4 ≡ just (inj₁ (vnat 4))
  ut₂ = refl

  example₃ : Expr
  example₃ = let' `x (abs' `y (var' `y)) (app' (var' `x) (nat' 5))
  
  ut₃ : operate ⟦ example₃ ⟧ 6 ≡ just (inj₁ (vnat 5))
  ut₃ = refl

  example₄ : Expr
  example₄ =
    put' (nat' 0) >>'
    let' `x (abs' `y get') (put' (nat' 42) >>' app' (var' `x) (nat' 0))

  ut₄ : operate ⟦ example₄ ⟧ 5 ≡ just (inj₁ (vnat 42))
  ut₄ = refl

  example₅ : Expr
  example₅ =
    throw' (nat' 12)

  ut₅ : operate ⟦ example₅ ⟧ 2 ≡ just (inj₂ (vnat 12))
  ut₅ = refl

  example₆ : Expr
  example₆ =
    catch' (throw' (nat' 6)) `x (var' `x)

  ut₆ : operate ⟦ example₆ ⟧ 6 ≡ just (inj₁ (vnat 6))
  ut₆ = refl

  example₇ : Expr
  example₇ = 
    put' (nat' 0) >>'
    catch' (put' (nat' 1) >>' throw' (nat' 2)) `x get'

  ut₇ : operate ⟦ example₇ ⟧ 6 ≡ just (inj₁ (vnat 1))
  ut₇ = refl
