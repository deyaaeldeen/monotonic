open import MonoRef.Static.Types

module MonoRef.Dynamics.Original.PureReduction where

open import MonoRef.Coercions.NoSpaceEfficiency.Syntax
open import MonoRef.Dynamics.PureReduction

module PureReductionNoSE = MonoRef.Dynamics.PureReduction  _⟹_ _! coerce
open PureReductionNoSE public
