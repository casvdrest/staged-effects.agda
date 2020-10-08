module Scoped.Except where

open import Function

open import Data.Empty
open import Data.Sum
open import Data.Maybe using (Maybe ; just ; nothing)

open import Container
open import Scoped.Prog

module _ where

  open Con

  data ThrowOp (X : Set) : Set where
    `throw : X → ThrowOp X

  ThrowSig : Set → Con
  S (ThrowSig X) = ThrowOp X
  P (ThrowSig X) (`throw x) = ⊥


  data Catch (X : Set) : Set where
    `catch : Catch X

  CatchScope : Set → Con
  S (CatchScope X) = Catch X
  P (CatchScope X) `catch = Maybe X

module _ {X : Set} where 

  catch : Prog σ (CatchScope X) A →
          (X → Prog σ (CatchScope X) A) →
          Prog σ (CatchScope X) A
  catch p h =
    scope `catch
          (λ where
            nothing → p
            (just x) → h x)
          var

  hEx : Prog (ThrowSig X ∪ σ) (CatchScope X ∪ γ) A → Prog σ γ (A ⊎ X)
  hEx (var x) = var (inj₁ x)
  hEx (op (inj₁ (`throw x)) k) = var (inj₂ x)
  hEx (op (inj₂ c) k) = op c (hEx ∘ k)
  hEx (scope (inj₁ `catch) sc k) = do
    (inj₁ x) ← hEx (sc nothing)
      where
        (inj₂ x) →
          do (inj₁ x) ← hEx (sc (just x))
                   where (inj₂ x) → var (inj₂ x)
             hEx (k x)
    hEx (k x)
  hEx (scope (inj₂ g) sc k) =
    scope g (hEx ∘ sc) (λ where
                          (inj₁ b) → hEx (k b)
                          (inj₂ x) → var (inj₂ x))
