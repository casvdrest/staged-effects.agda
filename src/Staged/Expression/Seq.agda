module Staged.Expression.Seq where

open import Data.Unit
open import Data.Bool
open import Data.Product

open import Level

open import Staged.Denote

module _ where

  SeqExpr : Sig
  Sig.S SeqExpr = ⊤
  Sig.P SeqExpr tt = Bool

module _ {V : Set} where

  ⟦seq⟧ : SeqExpr ⟨ ζ ⟩⇒ V
  denote ⟦seq⟧ (tt , p) = p false >> p true

module _ where

  _>>'_ : ⦃ SeqExpr ⊰ σ ⦄ → μ {zero} σ → μ {zero} σ → μ {zero} σ
  f >>' g = injectᶜ (tt , λ { false → f ; true → g })


  
