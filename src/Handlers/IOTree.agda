

module Handlers.IOTree where

open import Level
open import Function

open import Container

open import Relation.Binary.PropositionalEquality

module _ where

  variable σ σ₁ σ₂ : Con

  data IO (σ : Con) : Set → Set where
    end  : A → IO σ A
    cmd  : (c : S σ) → (P σ c → IO σ A) → IO σ A

  return : A → IO σ A
  return = end

  _>>=_ : IO σ A → (A → IO σ B) → IO σ B
  end x    >>= k = k x
  cmd c p  >>= k = cmd c (λ x → p x >>= k)

  _>>_ : IO σ A → IO σ B → IO σ B
  f >> g = f >>= const g

  fold : (gen : A → B)
         (alg : (c : S σ) (p : P σ c → B) → B) →
         IO σ A → B
  fold gen alg (end x) = gen x
  fold gen alg (cmd c p) =
    alg c (fold gen alg ∘ p)


  record _≪_ {ℓ} (σ₁ σ₂ : Con {ℓ}) : Set (suc ℓ) where
    field  inj  : S σ₁ → S σ₂
           ret≡ : ∀ {op} → P σ₂ (inj op) ≡ P σ₁ op 
  open _≪_ ⦃...⦄

  IO≺ : ⦃ σ₁ ≪ σ₂ ⦄ → IO σ₁ A → IO σ₂ A
  IO≺ (end x) = end x
  IO≺ ⦃ w ⦄ (cmd c p) = cmd (inj c) (IO≺ ∘ p ∘ subst id (ret≡ ⦃ w ⦄))
