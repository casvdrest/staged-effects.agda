module Staged.Effects.NoOp where

open import Data.Empty

open import Staged.Denote

module _ where

  open StagedSig

  NoOpSig : StagedSig
  C NoOpSig = ⊥
  R NoOpSig ()
  Z NoOpSig ()
  I NoOpSig {()}
