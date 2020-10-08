module Expression.Nat where

open import Data.Nat
open import Data.Empty
open import Data.Product

open import Denote
open import Effects.Nat

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

  natᴱ : ⦃ NatExpr ⊰ σ ⦄ → ℕ → μ σ
  natᴱ n = injectᶜ (n , λ())

