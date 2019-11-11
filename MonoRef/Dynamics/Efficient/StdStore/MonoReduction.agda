module MonoRef.Dynamics.Efficient.StdStore.MonoReduction where

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.StdStore.ApplyCast
open import MonoRef.Dynamics.Efficient.StdStore.Store
open import MonoRef.Dynamics.Reduction.StdStore.MonoReduction
  _⟹_ Inert public
open import MonoRef.Dynamics.Efficient.Value

open ParamMonoReduction make-coercion SimpleValue Value ref⟹T ref⟹∈ ref⟹⊑
open ParamMonoReduction/store/apply-cast
  store apply-cast typeprecise-strenthen-val public
