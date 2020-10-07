module Expression.Lambda where

open import Data.Sum
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product

open import Denote.Sig
open import Denote.StagedSig
open import Denote.Tree

open import Effects.Lambda

open import Value.Core

module _ {V : Set} where

  LamExpr : Sig
  Sig.S LamExpr = (Name ⊎ Name) ⊎ ⊤ ⊎ Name
  Sig.P LamExpr (inj₁ (inj₁ x )) = ⊥     -- var x
  Sig.P LamExpr (inj₁ (inj₂ y )) = ⊤     -- abs x e
  Sig.P LamExpr (inj₂ (inj₁ tt)) = Bool  -- app e e
  Sig.P LamExpr (inj₂ (inj₂ y )) = Bool  -- letin x e e


  ⟦lambda⟧ :   ⦃ LamOpSig V ⊏ ζ ⦄
             → ⦃ Closure V `⊏ V ⦄
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


  varᴱ : ⦃ LamExpr ⊰ σ ⦄ → Name → μ σ
  varᴱ x = injectᶜ ((inj₁ (inj₁ x)) , λ())

  absᴱ : ⦃ LamExpr ⊰ σ ⦄ → Name → μ σ → μ σ
  absᴱ x e = injectᶜ ((inj₁ (inj₂ x)) , λ _ → e)

  appᴱ : ⦃ LamExpr ⊰ σ ⦄ → μ σ → μ σ → μ σ
  appᴱ e₁ e₂ = injectᶜ ((inj₂ (inj₁ tt)) , λ { false → e₁ ; true → e₂ })

  letbindᴱ : ⦃ LamExpr ⊰ σ ⦄ → Name → μ σ → μ σ → μ σ
  letbindᴱ x e₁ e₂ = injectᶜ ((inj₂ (inj₂ x)) , λ { false → e₁ ; true → e₂ })
