module Staged.TC where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Bool 

open import Relation.Binary.PropositionalEquality

module _ where 

  data Ty : Set where
    nat : Ty
    fun : (s t : Ty) → Ty

  tyEq : (s t : Ty) → Bool
  tyEq nat nat = true
  tyEq nat (fun t t₁) = false
  tyEq (fun s s₁) nat = false
  tyEq (fun s s₁) (fun t t₁) = tyEq s t ∧ tyEq s₁ t₁

  Name = ℕ 

  data Expr : Set where
    var : Name → Expr 
    abs : Name → Expr → Expr
    app : Expr → Expr →  Expr
    val : ℕ → Expr 

  Env : Set → Set
  Env A = List (Name × A)

  _≟ᵇ_ : (n m : ℕ) → Bool
  zero ≟ᵇ zero = true
  zero ≟ᵇ suc m = false
  suc n ≟ᵇ zero = false
  suc n ≟ᵇ suc m = n ≟ᵇ m
 
  data TCMode : Set where
    inference checking : TCMode

  TCResult : TCMode → Set
  TCResult inference = Maybe Ty
  TCResult checking  = Ty → Bool

  switch : TCResult inference → TCResult checking
  switch nothing _    = false
  switch (just t) t′  = tyEq t t′
 
  _!_ : ∀ {A : Set} → List (Name × A) → Name → Maybe A 
  []             ! n = nothing
  ((x , v) ∷ xs) ! y = if x ≟ᵇ y then just v else (xs ! y)

  tc : (mode : TCMode) → Expr → Env Ty →  TCResult mode
  
  tc inference (var x)       Γ = Γ ! x
  tc inference (abs x tm)    Γ = nothing
  tc inference (app tm₁ tm₂) Γ with tc inference tm₁ Γ
  ... | nothing  = nothing
  ... | just nat = nothing
  ... | just (fun s t) with tc checking tm₂ Γ s
  ... | false = nothing
  ... | true = just t
  tc inference (val x) Γ = just nat
  
  tc checking (abs x tm) Γ nat       = false
  tc checking (abs x tm) Γ (fun s t) = tc checking tm ((x , s) ∷ Γ) t
  tc checking tm@(var _)   Γ = switch (tc inference tm Γ)
  tc checking tm@(val _)   Γ = switch (tc inference tm Γ)
  tc checking tm@(app tm₁ tm₂) Γ t′ with tc inference tm₁ Γ
  ... | nothing  = false
  ... | just nat = false
  ... | just (fun s t) with tc checking tm₂ Γ s
  ... | false = false
  ... | true = tyEq t t′

  -- λ x . x 
  example₀ : Expr
  example₀ = abs 0 (var 0)

  -- [] ⊢ λ x . x <= nat → nat 
  test₀ : tc checking example₀ [] (fun nat nat) ≡ true
  test₀ = refl

  -- f 10
  example₁ : Expr
  example₁ = app (var 0) (val 10)

  -- [ f ↦ nat → nat ] ⊢ f 10 => nat 
  test₁ : tc inference example₁ ((0 , fun nat nat) ∷ []) ≡ just nat
  test₁ = refl

  -- λ x . λ y . x y 
  example₂ : Expr
  example₂ = abs 0 (abs 1 (app (var 0) (var 1)))

  -- [] ⊢ λ f . λ x . f x => (nat → nat) → (nat → (nat → nat)) 
  test₂ : tc checking example₂ [] (fun (fun nat nat) (fun nat nat)) ≡ true
  test₂ = refl
