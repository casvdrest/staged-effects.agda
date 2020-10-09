module Staged.Effects.Except where

open import Function

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Maybe using (Maybe ; just ; nothing)

open import Staged.Denote.Sig
open import Staged.Denote.Tree

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Category.Functor

module _ where

  open Sig
  open RawFunctor ⦃ ... ⦄

  data ExceptOp (X : Set) : Set where
    `throw : X → ExceptOp X
    `catch : ExceptOp X

  ExcSig : Set → Set → Sig
  S₁ (ExcSig X V) = ExceptOp X
  P₁ (ExcSig X V) (`throw x) = ⊥
  P₁ (ExcSig X V) `catch     = V
  S₂ (ExcSig X V) (`throw x) = ⊥
  S₂ (ExcSig X V) `catch = Maybe X
  P₂ (ExcSig X V) {s₁ = `throw x} ()
  P₂ (ExcSig X V) {s₁ = `catch} _ = V

  instance
    SumFunctor : ∀ {a} {ℓ} {F : Set a → Set a} {X : Set ℓ} → ⦃ RawFunctor F ⦄ →
                 RawFunctor ((_⊎ X) ∘ F)
    (SumFunctor RawFunctor.<$> f) (inj₁ x) = inj₁ (f <$> x)
    (SumFunctor RawFunctor.<$> f) (inj₂ y) = inj₂ y

  variable X A : Set

  hEx : ∀ {V} ⦃ F : RawFunctor L ⦄ →
        Tree L (ExcSig X V ⊕ ζ) A →
        Tree ((_⊎ (L ⊤ × X)) ∘ L) ζ (A ⊎ (L ⊤ × X))
  hEx (leaf x) = leaf (inj₁ x)
  hEx (node (inj₁ (`throw x)) l _ _) = leaf (inj₂ (l , x))
  hEx (node (inj₁ `catch) l st k) = do
   m ← hEx (st nothing l)
   case m of λ where
     (inj₁ lv) → hEx (k lv)
     (inj₂ (l' , x)) → do
       m ← hEx (st (just x) (const tt <$> l'))
       case m of λ where
         (inj₁ lv) → hEx (k lv)
         (inj₂ lx) → leaf (inj₂ lx)
  hEx (node (inj₂ y) l st k) =
    node y (inj₁ l)
         (λ{ z (inj₁ x) → hEx (st z x)
           ; z (inj₂ y) → leaf (inj₂ y) })
         λ{ (inj₁ lv) → hEx (k lv)
          ; (inj₂ y) → leaf (inj₂ y) }

  open _⊏_ ⦃...⦄

  throw : ∀ {V} → ⦃ ExcSig X V ⊏ ζ ⦄ → X → Tree id ζ ⊥
  throw ⦃ w ⦄ x = node (inj (`throw x)) tt
                       (λ z _ → ⊥-elim (subst id (S₂≡ ⦃ w ⦄) z))
                       (λ r   → return (subst id (P₁≡ ⦃ w ⦄) r))

  catch : ∀ {V} → ⦃ ExcSig X V ⊏ ζ ⦄ →
          Tree id ζ V → (X → Tree id ζ V) → Tree id ζ V
  catch ⦃ w ⦄ p h = node (inj `catch) tt
                         (λ z l' →
                           case (subst id (S₂≡ ⦃ w ⦄) z) of λ where
                             nothing →
                               subst (Tree id _) (P₂≡ ⦃ w ⦄) p
                             (just x) →
                               subst (Tree id _) (P₂≡ ⦃ w ⦄) (h x))
                         (λ r → return (subst id (P₁≡ ⦃ w ⦄) r))
