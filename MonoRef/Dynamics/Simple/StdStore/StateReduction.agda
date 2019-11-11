module MonoRef.Dynamics.Simple.StdStore.StateReduction where

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.Frames
open import MonoRef.Dynamics.Simple.StdStore.ApplyCast
open import MonoRef.Dynamics.Simple.StdStore.Store
open import MonoRef.Dynamics.Reduction.StdStore.StateReduction
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Value

open ParamStateReduction/Pre Value
open ParamStateReduction
  make-coercion Value ref⟹T ref⟹∈ ref⟹⊑ typeprecise-strenthen-val
  apply-cast public
