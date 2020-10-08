module Scoped.Prog where 

open import Scoped.Sig

open import Function using (const)

module _ where

  open Sig
  
  variable A B : Set
           
  data Prog (σ γ : Sig) (A : Set) : Set₁ where
    var   : A → Prog σ γ A
    op    : (c : C σ) → (R σ c → Prog σ γ A) → Prog σ γ A
    scope : (g : C γ) → (R γ g → Prog σ γ B) → (B → Prog σ γ A) → Prog σ γ A

  return : A → Prog σ γ A
  return = var
  
  _>>=_ : Prog σ γ A → (A → Prog σ γ B) → Prog σ γ B
  var x >>= g = g x
  op c k >>= g = op c (λ x → k x >>= g)
  scope s vs k >>= g = scope s vs (λ x → k x >>= g)

  _>>_ : Prog σ γ A → Prog σ γ B → Prog σ γ B
  f >> g = f >>= const g
