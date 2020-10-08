module Everything where


--------------------------------------------------------------------------------
-- Section 2 (Compositional Semantics for Languages with
-- λ-abstraction and state)

open import Compositional.Core


--------------------------------------------------------------------------------
-- Section 3 (Effects and Handlers)




--------------------------------------------------------------------------------
-- Section 4 (Scoped Effects and Handlers)

-- Signatures
open import Scoped.Sig

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
open import Staged.Denote.Sig
open import Staged.Denote.StagedSig
open import Staged.Denote.Tree

-- Section 5.2 (Effect Staging)
import Staged.Effects.State

-- Section 5.3 (Defining and Handling Let Binding and Lambda)
import Staged.Effects.Lambda
import Staged.Effects.Nat


-- Modular expression types for the object language introduced in section 2
import Staged.Expression.State
import Staged.Expression.Lambda
import Staged.Expression.Nat
import Staged.Expression.Seq

-- Subtyping for value types
import Staged.Value.Core

-- Modular implementation of the object langugage
import Staged.Lang
