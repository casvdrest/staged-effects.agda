{-# OPTIONS --overlapping-instances #-}

module Compositional.Core where

open import Function
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Fin hiding (inject ; _≺_)

open import Category.Monad

open import Container

module _ where

  Name : Set
  Name = ℕ

  record LambdaM (M : Set → Set) (V  : Set) : Set where
    field fetch   : Name → M V
          abstr   : Name → M V → M V
          apply   : V → V → M V
          letbind : Name → V → M V → M V

  open LambdaM ⦃...⦄ public

  record NatM (M : Set → Set) (V : Set) : Set where
    field nat : ℕ → M V

  open NatM ⦃...⦄ public

  record StateM (M : Set → Set) (S : Set) : Set where
    field get : M S
          put : S → M ⊤

  open StateM ⦃...⦄ public

  variable M : Set → Set

module _ ⦃ _ : RawMonad M ⦄ ⦃ _ : LambdaM M V ⦄ where

  open RawMonad ⦃...⦄

  LamExpr : Con
  S LamExpr = Name ⊎ Name ⊎ ⊤ ⊎ Name
  P LamExpr (inj₁ x)               = ⊥
  P LamExpr (inj₂ (inj₁ x))        = ⊤
  P LamExpr (inj₂ (inj₂ (inj₁ x))) = ⊤ ⊎ ⊤
  P LamExpr (inj₂ (inj₂ (inj₂ y))) = ⊤ ⊎ ⊤

  denoteLam : LamExpr ⇒ M V
  run denoteLam (inj₁ x , p) = fetch x
  run denoteLam (inj₂ (inj₁ x) , p) = abstr x (p tt)
  run denoteLam (inj₂ (inj₂ (inj₁ x)) , p) = do
    v₁ ← p (inj₁ tt)
    v₂ ← p (inj₂ tt)
    apply v₁ v₂
  run denoteLam (inj₂ (inj₂ (inj₂ y)) , p) = do
    v ← p (inj₁ tt)
    letbind y v (p (inj₂ tt))


  `fetch : ⦃ LamExpr ≺ C ⦄ → Name → μ C
  `fetch x = inject (inj₁ x , λ())

  `abstr : ⦃ LamExpr ≺ C ⦄ → Name → μ C → μ C
  `abstr x b = inject (inj₂ (inj₁ x) , λ where tt → b)
  
  `apply : ⦃ LamExpr ≺ C ⦄ → μ C → μ C → μ C
  `apply e₁ e₂ = inject (inj₂ (inj₂ (inj₁ tt)) , λ where (inj₁ tt) → e₁
                                                         (inj₂ tt) → e₂)

  `letbind : ⦃ LamExpr ≺ C ⦄ → Name → μ C → μ C → μ C
  `letbind x e b = inject ((inj₂ (inj₂ (inj₂ x))) , λ where (inj₁ tt) → e
                                                            (inj₂ tt) → b)

module _ ⦃ _ : RawMonad M ⦄ ⦃ _ : NatM M V ⦄ where

  NatExpr : Con
  S NatExpr   = ℕ
  P NatExpr _ = ⊥

  denoteNat : NatExpr ⇒ M V
  run denoteNat (n , _) = nat n

  `nat : ⦃ NatExpr ≺ C ⦄ → ℕ → μ C
  `nat n = inject (n , λ())

module _ ⦃ _ : RawMonad M ⦄ ⦃ _ : StateM M V ⦄ where

  open RawMonad ⦃...⦄

  StateExpr : Con
  S StateExpr = ⊤ ⊎ ⊤
  P StateExpr (inj₁ tt) = ⊥
  P StateExpr (inj₂ tt) = ⊤

  denoteState : StateExpr ⇒ M V
  run denoteState (inj₁ tt , _) = get
  run denoteState (inj₂ tt , p) = do
    v ← p tt
    put v
    return v

  `get : ⦃ StateExpr ≺ C ⦄ → μ C
  `get = inject (inj₁ tt , λ())

  `put : ⦃ StateExpr ≺ C ⦄ → μ C → μ C
  `put e = inject ((inj₂ tt) , (λ where tt → e))
    
module _ ⦃ _ : RawMonad M ⦄ ⦃ _ : LambdaM M V ⦄ ⦃ _ : NatM M V ⦄ ⦃ _ : StateM M V ⦄ where

  open RawMonad ⦃...⦄
  open _≺_ ⦃...⦄

  -- Compose Expressions
  Expr   = LamExpr ∪ (NatExpr ∪ StateExpr)

  -- Compose Semantic Algebras
  denote = denoteLam ⊙ denoteNat ⊙ denoteState 

  
