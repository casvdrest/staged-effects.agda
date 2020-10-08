module Staged.Expression.Seq where

open import Data.Unit
open import Data.Bool
open import Data.Product

open import Level

open import Container
open import Staged.Denote

module _ where

  SeqExpr : Con
  Con.S SeqExpr = ⊤
  Con.P SeqExpr tt = Bool

module _ {V : Set} where

  ⟦seq⟧ : SeqExpr ⟨ ζ ⟩⇒ V
  denote ⟦seq⟧ (tt , p) = p false >> p true

module _ where

  _>>'_ : ⦃ SeqExpr ≺ C ⦄ → μ C → μ C → μ C
  f >>' g = inject (tt , λ { false → f ; true → g })


  
