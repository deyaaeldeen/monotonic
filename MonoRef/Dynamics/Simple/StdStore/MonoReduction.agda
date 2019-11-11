module MonoRef.Dynamics.Simple.StdStore.MonoReduction where

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.Value
open import MonoRef.Dynamics.Simple.StdStore.Store
open import MonoRef.Dynamics.Reduction.StdStore.MonoReduction
  _⟹_ Inert public
open import MonoRef.Dynamics.Simple.StdStore.ApplyCast

open ParamMonoReduction make-coercion Value Value ref⟹T ref⟹∈ ref⟹⊑
open ParamMonoReduction/store/apply-cast
  store apply-cast typeprecise-strenthen-val public
