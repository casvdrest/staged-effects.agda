module Staged.Denote.Tree where

open import Function using (id ; _∘_ ; const)

open import Data.Unit

open import Container
open import Staged.Denote.Sig
open import Category.Monad

module _ where

  variable L : Set → Set

  data Tree (L : Set → Set) (ζ : Sig) (A : Set) : Set where

    leaf : A → Tree L ζ A

    node : let open Sig ζ in 

             (c  : S₁)                                
           → (l  : L ⊤)
           → (st : (s₂ : S₂ c) → L ⊤ → Tree L ζ (L (P₂ s₂)))
           → (k  : L (P₁ c) → Tree L ζ A) 
           → Tree L ζ A

-- Tree L ζ is an applicative functor
module _ where

  mapᵀ : (f : A → B) → Tree L ζ A → Tree L ζ B 
  mapᵀ f (leaf x)        = leaf (f x)
  mapᵀ f (node c l st k) = node c l st (mapᵀ f ∘ k)


  pure : A → Tree L ζ A
  pure = leaf

  _<*>_ : Tree L ζ (A → B) → Tree L ζ A → Tree L ζ B
  leaf f <*> tx = mapᵀ f tx
  node c l st k <*> tx = node c l st (_<*> tx ∘ k)

-- Tree L ζ is a monad
module _ where 

  mutual
    _>>=_ : Tree L ζ A → (A → Tree L ζ B) → Tree L ζ B
    leaf x        >>= t = t x
    node c l st k >>= t = node c l st (k >=> t)

    _>=>_ : ∀ {C} → (A → Tree L ζ B) → (B → Tree L ζ C) → (A → Tree L ζ C)
    (f >=> g) x = f x >>= g

  _>>_ : Tree L ζ A → Tree L ζ B → Tree L ζ B
  t₁ >> t₂ = t₁ >>= const t₂

  return : A → Tree L ζ A
  return = pure

  Tree-RawMonad : ∀ {L ζ} → RawMonad (Tree L ζ)
  Tree-RawMonad = record { return = return ; _>>=_ = _>>=_ }


-- Algebra-encoded semantic functions + composition
module _ where

  record _⟨_⟩⇒_ (C : Con) (ζ : Sig) (A : Set) : Set₁ where
    field denote : ⟦ C ⟧ᶜ (Tree id ζ A) → Tree id ζ A

  open _⟨_⟩⇒_

  ⟪_⟫ : (f : C ⟨ ζ ⟩⇒ A) → (x : μ C) → Tree id ζ A
  ⟪ f ⟫ = foldᶜ (denote f)

  infixr 10 _`⊙_
  _`⊙_ :   (f : C₁ ⟨ ζ ⟩⇒ A)
         → (g : C₂ ⟨ ζ ⟩⇒ A)
           ------------------
         → (C₁ ∪ C₂) ⟨ ζ ⟩⇒ A

  denote (f `⊙ g) = run (record { run = denote f } ⊙ record { run = denote g })

module _ where

  open _⟨_⟩⇒_ public
