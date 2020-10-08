module Staged.Effects.NoOp where

open import Data.Empty

open import Staged.Denote

module _ where

  open Sig

  NoOpSig : Sig
  S₁ NoOpSig = ⊥
  P₁ NoOpSig ()
  S₂ NoOpSig ()
  P₂ NoOpSig {()}
