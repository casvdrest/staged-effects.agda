module Staged.Expression.Nat where

open import Data.Nat
open import Data.Empty
open import Data.Product

open import Staged.Denote
open import Staged.Effects.Nat

module _ where

  NatExpr : Sig
  Sig.S NatExpr   = ℕ
  Sig.P NatExpr _ = ⊥

module _ {V : Set} where

  ⟦nat⟧ :   ⦃ NatOpSig V ⊏ ζ ⦄
          → ⦃ ℕ ⊂ V ⦄
            ------------------
          → NatExpr ⟨ ζ ⟩⇒ V


  denote ⟦nat⟧ (n , _) = nat n

module _ where 

  nat' : ⦃ NatExpr ⊰ σ ⦄ → ℕ → μ σ
  nat' n = injectᶜ (n , λ())

