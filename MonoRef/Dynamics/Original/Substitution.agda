module MonoRef.Dynamics.Original.Substitution where

open import MonoRef.Coercions.NoSpaceEfficiency.Syntax
open import MonoRef.Dynamics.Substitution


module SubstitutionNoSE = MonoRef.Dynamics.Substitution _⟹_ _!
open SubstitutionNoSE public
