module Denote.Tree where

open import Function using (id ; _∘_ ; const)

open import Data.Unit

open import Denote.Sig
open import Denote.StagedSig


module _ where


  variable L : Set → Set


  data Tree (L : Set → Set) (ζ : StagedSig) (A : Set) : Set₁ where

    leaf : A → Tree L ζ A

    node : let open StagedSig ζ in 

             (c  : C)                                
           → (l  : L ⊤)
           → (sc : (z : Z c) → L ⊤ → Tree L ζ (L (I z)))
           → (k  : L (R c) → Tree L ζ A) 
           → Tree L ζ A

-- Tree L ζ is an applicative functor
module _ where

  mapᵀ : (f : A → B) → Tree L ζ A → Tree L ζ B 
  mapᵀ f (leaf x)        = leaf (f x)
  mapᵀ f (node c l sc k) = node c l sc (mapᵀ f ∘ k)


  pure : A → Tree L ζ A
  pure = leaf

  _<*>_ : Tree L ζ (A → B) → Tree L ζ A → Tree L ζ B
  leaf f <*> tx = mapᵀ f tx
  node c l sc k <*> tx = node c l sc (_<*> tx ∘ k)

-- Tree L ζ is a monad
module _ where 

  mutual 
    _>>=_ : Tree L ζ A → (A → Tree L ζ B) → Tree L ζ B
    leaf x        >>= t = t x
    node c l sc k >>= t = node c l sc (k >=> t)

    _>=>_ : ∀ {C} → (A → Tree L ζ B) → (B → Tree L ζ C) → (A → Tree L ζ C)
    (f >=> g) x = f x >>= g

  _>>_ : Tree L ζ A → Tree L ζ B → Tree L ζ B
  t₁ >> t₂ = t₁ >>= const t₂

  return : A → Tree L ζ A
  return = pure


-- Algebra-encoded semantic functions + composition
module _ where

  record _⟨_⟩⇒_ (σ : Sig) (ζ : StagedSig) (A : Set) : Set₁ where
    field denote : σ ⇒ Tree id ζ A

  open _⟨_⟩⇒_

  ⟪_⟫ : (f : σ ⟨ ζ ⟩⇒ A) → (x : μ {ℓ} σ) → Tree id ζ A
  ⟪ f ⟫ = foldᶜ (denote f) 


  _`⊙_ :   (f : σ₁ ⟨ ζ ⟩⇒ A)
         → (g : σ₂ ⟨ ζ ⟩⇒ A)
           ------------------
         → (σ₁ ∪ σ₂) ⟨ ζ ⟩⇒ A

  denote (f `⊙ g) x = (denote f ⊙ denote g) x

module _ where

  open _⟨_⟩⇒_ public
