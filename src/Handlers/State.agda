module Handlers.State where 

open import Function

open import Data.Unit
open import Data.Sum

open import Container
open import Handlers.IOTree

open import Relation.Binary.PropositionalEquality

module _ where 
  
  data StateOp (S : Set) : Set where
    `get : StateOp S
    `put : S → StateOp S
  
  StateCon : Set → Con
  S (StateCon S) = StateOp S
  P (StateCon S) `get = S
  P (StateCon S) (`put s) = ⊤
  
module _ {St : Set} where 
  
  open _≪_ ⦃...⦄

  handleState : IO (StateCon St ∪ σ) A → St → IO σ A
  handleState {σ = σ} {A = A} =
    fold (flip (const end))
         λ where
           (inj₁ `get) p s → p s s
           (inj₁ (`put s)) p _ → p tt s
           (inj₂ c) p s → cmd c (flip p s)
  
  hSt : St → IO (StateCon St ∪ σ) A → IO σ A
  hSt _  (end x)                  = end x
  hSt s  (cmd (inj₁ `get) k)      = hSt s (k s)
  hSt _  (cmd (inj₁ (`put s)) k)  = hSt s (k tt)
  hSt s  (cmd (inj₂ y) k)         = cmd y (hSt s ∘ k)
  
  get : ⦃ StateCon St ≪ σ ⦄ → IO σ St
  get ⦃ w ⦄ = cmd (inj `get) (end ∘ subst id (ret≡ ⦃ w ⦄))
  
  put : ⦃ StateCon St ≪ σ ⦄ → St → IO σ ⊤
  put ⦃ w ⦄ s = cmd (inj (`put s)) (end ∘ subst id (ret≡ ⦃ w ⦄))
  
  record StateMonad (M : Set → Set) (S : Set) : Set₁ where
    field  recall     : M S
           memorize   : S → M ⊤
  
  
  open StateMonad

  lift : σ₁ ≪ σ₂ → (c : S σ₁) → IO σ₂ (P σ₁ c)
  lift w c = cmd (inj ⦃ w ⦄ c)  (end ∘ subst id (ret≡ ⦃ w ⦄))

  StateInst : StateCon St ≪ σ → StateMonad (IO σ) St
  recall (StateInst w)      = lift w `get
  memorize (StateInst w) s  = lift w (`put s)
  
  
