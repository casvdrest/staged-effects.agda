module Staged.Expression.State (St : Set) where

open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Maybe hiding (_>>=_)

open import Staged.Denote
open import Staged.Effects.State
open import Staged.Value.Core

module _ where 

  StateExpr : Sig
  Sig.S StateExpr = Bool
  Sig.P StateExpr false = ⊥  -- get
  Sig.P StateExpr true  = ⊤  -- put e

module _ {V : Set} where 

  postulate ERROR : ∀ {A : Set ℓ} → A

  ⟦state⟧ :   ⦃ StateSig St ⊏ ζ ⦄
            → ⦃ St ⊂ V ⦄
              --------------------
            → StateExpr ⟨ ζ ⟩⇒ V

  denote ⟦state⟧ (false , _) = do
    n ← get
    return (inject n)
  denote (⟦state⟧ ⦃ _ ⦄ ⦃ w ⦄) (true  , p) = do
    just n ← mapᵀ (project ⦃ w ⦄) (p tt)
      where nothing → ERROR
    put n
    return (inject n)

module _ where 

  get' : ⦃ StateExpr ⊰ σ ⦄ → μ σ
  get' = injectᶜ (false , λ())

  put' : ⦃ StateExpr ⊰ σ ⦄ → μ σ → μ σ
  put' e = injectᶜ (true , (λ _ → e))
