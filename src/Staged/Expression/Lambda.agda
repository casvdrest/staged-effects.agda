module Staged.Expression.Lambda where

open import Data.Sum
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product

open import Container
open import Staged.Denote
open import Staged.Effects.Lambda
open import Staged.Value.Core

module _ where

  LamExpr : Con
  Con.S LamExpr = (Name ⊎ Name) ⊎ ⊤ ⊎ Name
  Con.P LamExpr (inj₁ (inj₁ x )) = ⊥     -- var x
  Con.P LamExpr (inj₁ (inj₂ y )) = ⊤     -- abs x e
  Con.P LamExpr (inj₂ (inj₁ tt)) = Bool  -- app e e
  Con.P LamExpr (inj₂ (inj₂ y )) = Bool  -- letin x e e

module _ {V : Set} where 

  ⟦lambda⟧ :   ⦃ LamOpSig V ⊏ ζ ⦄
             → ⦃ Closure V ⊂ V ⦄
               ------------------
             → LamExpr ⟨ ζ ⟩⇒ V
  
  denote ⟦lambda⟧ (inj₁ (inj₁ x)  , p) = fetch x
  denote ⟦lambda⟧ (inj₁ (inj₂ y)  , p) = abs y (p tt)
  denote ⟦lambda⟧ (inj₂ (inj₁ tt) , p) = do
    v₁ ← p false
    v₂ ← p true
    app v₁ v₂
  denote ⟦lambda⟧ (inj₂ (inj₂ y)  , p) = do
    v ← p false
    letbind y v (p true)

module _ where 

  var' : ⦃ LamExpr ≺ C ⦄ → Name → μ C
  var' x = inject ((inj₁ (inj₁ x)) , λ())

  abs' : ⦃ LamExpr ≺ C ⦄ → Name → μ C → μ C
  abs' x e = inject ((inj₁ (inj₂ x)) , λ _ → e)

  app' : ⦃ LamExpr ≺ C ⦄ → μ C → μ C → μ C
  app' e₁ e₂ = inject ((inj₂ (inj₁ tt)) , λ { false → e₁ ; true → e₂ })

  let' : ⦃ LamExpr ≺ C ⦄ → Name → μ C → μ C → μ C
  let' x e₁ e₂ = inject ((inj₂ (inj₂ x)) , λ { false → e₁ ; true → e₂  })
