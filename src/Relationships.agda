module Relationships where

open import Container
open import Handlers.IOTree
open import Scoped.Prog
open import Staged.Denote.Sig
open import Staged.Denote.Tree

open import Level
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

IOTree-to-Prog : {σ γ : Con} {A : Set} → IO σ A → Prog σ γ A
IOTree-to-Prog (end x) = var x
IOTree-to-Prog (cmd c k) = op c (IOTree-to-Prog ∘ k)

Cmd-Con-to-Sig : {ℓ : Level} → Con {ℓ} → Sig {ℓ}
Cmd-Con-to-Sig (S₁ ▹ P₁) = S₁ ▹ P₁ ∣ const (Lift _ ⊥) ▹ (⊥-elim ∘ lower)

Scope-Con-to-Sig : Con {zero} → Sig {suc zero}
Scope-Con-to-Sig (S₁ ▹ P₁) =
  (∃ λ (X : Set) → S₁) ▹ (Lift _ ∘ proj₁) ∣ Lift _ ∘ P₁ ∘ proj₂ ▹ λ{ {p} _ → Lift _ (proj₁ p) } 

Prog-to-Tree : {σ : Con {suc zero}} {γ : Con {zero}} {A : Set} →
               Prog σ γ A →
               Tree id (Cmd-Con-to-Sig σ ⊕ Scope-Con-to-Sig γ) (Lift _ A)
Prog-to-Tree (var x) = leaf (lift x)
Prog-to-Tree (op c k) = node (inj₁ c) (lift tt) (λ ()) (Prog-to-Tree ∘ k)
Prog-to-Tree (scope g sc k) =
  node (inj₂ (_ , g)) (lift tt)
       (λ s _ → Prog-to-Tree (sc (lower s)))
       (Prog-to-Tree ∘ k ∘ lower)
