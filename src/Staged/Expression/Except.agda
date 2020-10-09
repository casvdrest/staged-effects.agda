module Staged.Expression.Except where

open import Function
open import Data.Sum
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product

open import Container
open import Staged.Denote
open import Staged.Effects.Except
open import Staged.Effects.Lambda
open import Staged.Value.Core

module _ where

  ExcExpr : Con
  Con.S ExcExpr = Maybe Name
  P ExcExpr nothing  = ⊤      -- throw e
  P ExcExpr (just x) = Bool  -- catch e₁ x e₂

module _ {V : Set} where 

  ⟦except⟧ :   ⦃ ExcSig V V ⊏ ζ ⦄
             → ⦃ LamSig V ⊏ ζ ⦄
               ------------------
             → ExcExpr ⟨ ζ ⟩⇒ V
  
  denote ⟦except⟧ (nothing , p) = do
    v ← p tt
    () ← throw v
  denote ⟦except⟧ (just n , p) = do
    catch (p true) (λ v → letbind n v (p false))

module _ where 

  throw' : ⦃ ExcExpr ≺ C ⦄ → μ C → μ C
  throw' x = inject (nothing , const x)

  catch' : ⦃ ExcExpr ≺ C ⦄ → μ C → Name → μ C → μ C
  catch' p n h = inject (just n , λ{ true → p ; false → h })
