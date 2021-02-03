module Staged.Expression.Nat where

open import Data.Nat
open import Data.Empty
open import Data.Product

open import Container
open import Staged.Denote
open import Staged.Effects.Nat

module _ where

  NatExpr : Con
  Con.S NatExpr   = ℕ
  Con.P NatExpr _ = ⊥

module _ {V : Set} where

  ⟦nat⟧ :   ⦃ NatOpSig V ⊏ ζ ⦄
            ------------------
          → NatExpr ⟨ ζ ⟩⇒ V


  denote ⟦nat⟧ (n , _) = nat n

module _ where 

  nat' : ⦃ NatExpr ≺ C ⦄ → ℕ → μ C
  nat' n = inject (n , λ())

