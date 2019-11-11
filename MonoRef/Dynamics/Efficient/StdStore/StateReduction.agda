module MonoRef.Dynamics.Efficient.StdStore.StateReduction where

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.Frames
open import MonoRef.Dynamics.Efficient.StdStore.ApplyCast
open import MonoRef.Dynamics.Efficient.StdStore.Store
open import MonoRef.Dynamics.Reduction.StdStore.StateReduction
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Value

open ParamStateReduction/Pre Value
open ParamStateReduction
  make-coercion SimpleValue ref⟹T ref⟹∈ ref⟹⊑ typeprecise-strenthen-val
  apply-cast public
