{-# OPTIONS --type-in-type #-}

module Effects.Lambda where

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

open import Denote.Sig
open import Denote.StagedSig
open import Denote.Tree

open import Value.Core

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Category.Functor

module _ where 

  open StagedSig
  open RawFunctor ⦃...⦄

  Name = ℕ

  data LamOp (V : Set) : Set where
    `app      :  V → V → LamOp V
    `fetch    :  Name → LamOp V
    `abs      :  Name → LamOp V
    `letbind  :  Name → V → LamOp V

  LamOpSig : (V : Set) → StagedSig
  C (LamOpSig V) = LamOp V
  R (LamOpSig V) _                = V
  Z (LamOpSig V) (`app v₁ v₂)     = ⊥
  Z (LamOpSig V) (`fetch x)       = ⊥
  Z (LamOpSig V) (`abs x)         = ⊤
  Z (LamOpSig V) (`letbind x x₁)  = ⊤
  I (LamOpSig V) _                = V

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

  pget₀ : List A → FunLabel → Maybe A
  pget₀ [] _ = nothing
  pget₀ (x ∷ _) 0 = just x
  pget₀ (_ ∷ xs) (suc n) = pget₀ xs n

  retrieve = pget₀

  pget₁ : Env V → Name → Maybe V
  pget₁ [] _ = nothing
  pget₁ ((x , v) ∷ nv) y with x ≟ y
  ... | yes _ = pget₁ nv y
  ... | no  _ = just v 

  lookupₐ = pget₁


  Resumptions : (Set → Set) → StagedSig → Set → Set₁
  Resumptions L ζ V =
    List (L ⊤ → Tree L (LamOpSig V ⊞ ζ) (L V))

  try : Maybe A → (A → Tree L ζ (Maybe B)) → Tree L ζ (Maybe B)
  try m f = maybe f (leaf nothing) m
  
  hLam' :  ⦃ Closure V `⊏ V ⦄ → ⦃ RawFunctor L ⦄ →
           Env V → Resumptions L ζ V → ℕ →
           Tree L (LamOpSig V ⊞ ζ) A →
           Tree  (Maybe ∘ (Resumptions L ζ V ×_) ∘ L)
                 ζ (Maybe (Resumptions L ζ V × A))
  hLam' _ _ zero _ = leaf nothing
  hLam' E funs (suc m) (leaf x)  = leaf (just (funs , x))
  hLam' E funs (suc m) (node (inj₁ (`app v₁ v₂)) l _ k) =
    try (project v₁) λ{ (clos n f E') →
      try (retrieve funs f) (λ r →
        hLam' E funs m (r l) >>= flip try (λ{ (funs' , lv) →
              hLam' E funs' m (k lv) }))}
  hLam' E funs (suc m) (node (inj₁ (`fetch n)) l _ k) = 
    try (lookupₐ E n) (λ v →
      hLam' E funs m (k (const v <$> l)))
  hLam' E funs (suc m) (node (inj₁ (`abs n)) l st k) =
    hLam'   E (funs ++ [ st tt ]) m
            (k (const (inject (clos n (length funs) E)) <$> l))
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
                       (λ z _ → ⊥-elim (subst id (Z≡ ⦃ w ⦄) z))
                       (λ r   → return (subst id (R≡ ⦃ w ⦄) r))

  abs : ⦃ LamOpSig V ⊏ ζ ⦄ → Name → Tree id ζ V → Tree id ζ V
  abs ⦃ w ⦄ x e = node (inj (`abs x)) tt
                 (λ z _ → subst (Tree id _) (I≡ ⦃ w ⦄) e)
                 (λ r → return (subst id (R≡ ⦃ w ⦄) r)) 

  app : ⦃ LamOpSig V ⊏ ζ ⦄ → V → V → Tree id ζ V
  app ⦃ w ⦄ x y = node (inj (`app x y)) tt
                       (λ z _ → ⊥-elim (subst id (Z≡ ⦃ w ⦄) z))
                       (λ r → return (subst id (R≡ ⦃ w ⦄) r))

  letbind : ⦃ LamOpSig V ⊏ ζ ⦄ → Name → V → Tree id ζ V → Tree id ζ V 
  letbind ⦃ w ⦄ x v e = node (inj (`letbind x v)) tt
                             (λ z _ → subst (Tree id _) (I≡ ⦃ w ⦄) e)
                             (λ r → return (subst id (R≡ ⦃ w ⦄) r))


  
