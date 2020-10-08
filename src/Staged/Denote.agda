module Staged.Denote where

import Staged.Denote.Sig
import Staged.Denote.StagedSig
import Staged.Denote.Tree

open Staged.Denote.Sig public
open Staged.Denote.StagedSig public
open Staged.Denote.Tree public

import Staged.Value.Core
open Staged.Value.Core public

open import Category.Functor
open import Function
open import Level

open import Data.Maybe
open import Data.Product


module _ where

  instance id-functor : RawFunctor {zero} id
  RawFunctor._<$>_ id-functor = id



