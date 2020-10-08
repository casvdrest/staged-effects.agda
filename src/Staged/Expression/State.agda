module Staged.Expression.State (St : Set) where

open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Maybe hiding (_>>=_)

open import Container
open import Staged.Denote
open import Staged.Effects.State
open import Staged.Value.Core

module _ where 

  StateExpr : Con
  Con.S StateExpr = Bool
  Con.P StateExpr false = ⊥  -- get
  Con.P StateExpr true  = ⊤  -- put e

module _ {V : Set} where 

  postulate ERROR : ∀ {A : Set} → A

  ⟦state⟧ :   ⦃ StateSig St ⊏ ζ ⦄
            → ⦃ St ⊂ V ⦄
              --------------------
            → StateExpr ⟨ ζ ⟩⇒ V

  denote ⟦state⟧ (false , _) = do
    n ← get
    return (injectᵛ n)
  denote (⟦state⟧ ⦃ _ ⦄ ⦃ w ⦄) (true  , p) = do
    just n ← mapᵀ (projectᵛ ⦃ w ⦄) (p tt)
      where nothing → ERROR
    put n
    return (injectᵛ n)

module _ where 

  get' : ⦃ StateExpr ≺ C ⦄ → μ C
  get' = inject (false , λ())

  put' : ⦃ StateExpr ≺ C ⦄ → μ C → μ C
  put' e = inject (true , (λ _ → e))
