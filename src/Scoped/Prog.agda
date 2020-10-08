module Scoped.Prog where 

open import Container

open import Function using (const)

module _ where

  open Con

  variable σ σ₁ σ₂ γ γ₁ γ₂ : Con
  
  data Prog (σ γ : Con) (A : Set) : Set₁ where
    var   : A → Prog σ γ A
    op    : (c : S σ) → (P σ c → Prog σ γ A) → Prog σ γ A
    scope : (g : S γ) → (P γ g → Prog σ γ B) → (B → Prog σ γ A) → Prog σ γ A

  return : A → Prog σ γ A
  return = var
  
  _>>=_ : Prog σ γ A → (A → Prog σ γ B) → Prog σ γ B
  var x >>= g = g x
  op c k >>= g = op c (λ x → k x >>= g)
  scope s vs k >>= g = scope s vs (λ x → k x >>= g)

  _>>_ : Prog σ γ A → Prog σ γ B → Prog σ γ B
  f >> g = f >>= const g
