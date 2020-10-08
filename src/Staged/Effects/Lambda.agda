{-# OPTIONS --type-in-type #-}

module Staged.Effects.Lambda where

open import Function
open import Level

open import Data.Maybe using (Maybe ; just ; nothing ; maybe)
open import Data.Nat hiding (_⊔_)
open import Data.List
open import Data.Bool using (Bool ; true ; false)
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Data.Sum

open import Staged.Denote

open import Staged.Value.Core

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Category.Functor

module _ where 

  open Sig
  open RawFunctor ⦃...⦄

  Name = ℕ

  data LamOp (V : Set) : Set where
    `app      :  V → V → LamOp V
    `fetch    :  Name → LamOp V
    `abs      :  Name → LamOp V
    `letbind  :  Name → V → LamOp V

  LamOpSig : (V : Set) → Sig
  S₁ (LamOpSig V) = LamOp V
  P₁ (LamOpSig V) _                = V
  S₂ (LamOpSig V) (`app v₁ v₂)     = ⊥
  S₂ (LamOpSig V) (`fetch x)       = ⊥
  S₂ (LamOpSig V) (`abs x)         = ⊤
  S₂ (LamOpSig V) (`letbind x x₁)  = ⊤
  P₂ (LamOpSig V) _                = V

  variable V : Set

  instance
    ProdFunctor : ∀ {ℓ} {a} {X : Set ℓ} → RawFunctor {a} {a ⊔ ℓ} (X ×_)
    RawFunctor._<$>_ ProdFunctor f (x , a) = x , f a  -- x , f a

  instance
    MaybeFunctor : ∀ {a b} {F} → ⦃ RawFunctor F ⦄ → RawFunctor {a} {b} (Maybe {b} ∘ F)
    (MaybeFunctor {_} RawFunctor.<$> f) nothing = nothing
    (MaybeFunctor {_} RawFunctor.<$> f) (just x) = just (f <$> x)

  FunLabel = ℕ

  Env : Set → Set; Env V = List (Name × V)

  data Closure (V : Set) : Set where
    clos : Name → FunLabel → Env V → Closure V

  variable A B : Set

  retrieve : List A → FunLabel → Maybe A
  retrieve [] _ = nothing
  retrieve (x ∷ _) 0 = just x
  retrieve (_ ∷ xs) (suc n) = retrieve xs n

  lookupₐ : Env V → Name → Maybe V
  lookupₐ [] _ = nothing
  lookupₐ ((x , v) ∷ nv) y with x ≟ y
  ... | yes _ = just v
  ... | no  _ = lookupₐ nv y

  Resumptions : (Set → Set) → Sig → Set → Set₁
  Resumptions L ζ V =
    List (L ⊤ → Tree L (LamOpSig V ⊕ ζ) (L V))

  try : Maybe A → (A → Tree L ζ (Maybe B)) → Tree L ζ (Maybe B)
  try m f = maybe f (leaf nothing) m
  
  hLam' :  ⦃ Closure V ⊂ V ⦄ → ⦃ RawFunctor L ⦄ →
           Env V → Resumptions L ζ V → ℕ →
           Tree L (LamOpSig V ⊕ ζ) A →
           Tree  (Maybe ∘ (Resumptions L ζ V ×_) ∘ L)
                 ζ (Maybe (Resumptions L ζ V × A))
  hLam' _ _ zero _ = leaf nothing
  hLam' E funs (suc m) (leaf x)  = leaf (just (funs , x))
  hLam' E funs (suc m) (node (inj₁ (`app v₁ v₂)) l _ k) =
    try (projectᵛ v₁) λ{ (clos n f E') →
      try (retrieve funs f) (λ r →
        hLam' ((n , v₂) ∷ E') funs m (r l) >>=
          flip try (λ{ (funs' , lv) →
              hLam' E funs' m (k lv) }))}
  hLam' E funs (suc m) (node (inj₁ (`fetch n)) l _ k) = 
    try (lookupₐ E n) (λ v →
      hLam' E funs m (k (const v <$> l)))
  hLam' E funs (suc m) (node (inj₁ (`abs n)) l st k) =
    hLam'   E (funs ++ [ st tt ]) m
            (k (const (injectᵛ (clos n (length funs) E)) <$> l))
  hLam' E funs (suc m) (node (inj₁ (`letbind n v)) l st k) =
    hLam' ((n , v) ∷ E) funs m (st tt l) >>=
      flip try λ{ (funs' , lv) → hLam' E funs' m (k lv) }
  hLam' E funs (suc m) (node (inj₂ c) l st k) =
    node      c (just (funs , l))
              (λ r → flip try (λ{ (funs' , l') →
                                  hLam' E funs' m (st r l') }))
              (flip try λ{ (funs' , lr) → hLam' E funs' m (k lr) })

  open _⊏_ ⦃...⦄

  fetch : ⦃ LamOpSig V ⊏ ζ ⦄ → Name → Tree id ζ V
  fetch ⦃ w ⦄ x = node (inj (`fetch x)) tt
                       (λ z _ → ⊥-elim (subst id (S₂≡ ⦃ w ⦄) z))
                       (λ r   → return (subst id (P₁≡ ⦃ w ⦄) r))

  abs : ⦃ LamOpSig V ⊏ ζ ⦄ → Name → Tree id ζ V → Tree id ζ V
  abs ⦃ w ⦄ x e = node (inj (`abs x)) tt
                 (λ z _ → subst (Tree id _) (P₂≡ ⦃ w ⦄) e)
                 (λ r → return (subst id (P₁≡ ⦃ w ⦄) r)) 

  app : ⦃ LamOpSig V ⊏ ζ ⦄ → V → V → Tree id ζ V
  app ⦃ w ⦄ x y = node (inj (`app x y)) tt
                       (λ z _ → ⊥-elim (subst id (S₂≡ ⦃ w ⦄) z))
                       (λ r → return (subst id (P₁≡ ⦃ w ⦄) r))

  letbind : ⦃ LamOpSig V ⊏ ζ ⦄ → Name → V → Tree id ζ V → Tree id ζ V 
  letbind ⦃ w ⦄ x v e = node (inj (`letbind x v)) tt
                             (λ z _ → subst (Tree id _) (P₂≡ ⦃ w ⦄) e)
                             (λ r → return (subst id (P₁≡ ⦃ w ⦄) r))


  
