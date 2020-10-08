module Everything where

--------------------------------------------------------------------------------
-- Misc

-- Container definition
open import Container


--------------------------------------------------------------------------------
-- Section 2 (Compositional Semantics for Languages with
-- λ-abstraction and state)

open import Compositional.Core


--------------------------------------------------------------------------------
-- Section 3 (Effects and Handlers)

-- IO Trees
open import Handlers.IOTree

-- State/Except handlers
open import Handlers.State
open import Handlers.Except


--------------------------------------------------------------------------------
-- Section 4 (Scoped Effects and Handlers)

-- Section 4.1 (Trees with Scoped Effects)
open import Scoped.Prog

-- Bonus: Exceptions
open import Scoped.Except

-- Section 4.2 (Effect Weaving)
open import Scoped.State
open import Scoped.LetBind


--------------------------------------------------------------------------------
-- Section 5 (Staged Effects and Handlers)

-- Section 5.1 (Trees with Staged Effects)
open import Staged.Denote.StagedSig
open import Staged.Denote.Tree

-- Section 5.2 (Effect Staging)
open import Staged.Effects.State

-- Section 5.3 (Defining and Handling Let Binding and Lambda)
open import Staged.Effects.Lambda
open import Staged.Effects.Nat


-- Modular expression types for the object language introduced in section 2
open import Staged.Expression.State
open import Staged.Expression.Lambda
open import Staged.Expression.Nat
open import Staged.Expression.Seq

-- Subtyping for value types
open import Staged.Value.Core

-- Modular implementation of the object langugage
open import Staged.Lang
