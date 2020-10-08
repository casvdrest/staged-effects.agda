module Expression.State (St : Set) where

open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Maybe hiding (_>>=_)

open import Denote.Sig
open import Denote.StagedSig
open import Denote.Tree

open import Effects.State

open import Value.Core

module _ {V : Set} where 

  StateExpr : Sig
  Sig.S StateExpr = Bool
  Sig.P StateExpr false = ⊥  -- get
  Sig.P StateExpr true  = ⊤  -- put e

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

  getᴱ : ⦃ StateExpr ⊰ σ ⦄ → μ σ
  getᴱ = injectᶜ (false , λ())

  putᴱ : ⦃ StateExpr ⊰ σ ⦄ → μ σ → μ σ
  putᴱ e = injectᶜ (true , (λ _ → e))
