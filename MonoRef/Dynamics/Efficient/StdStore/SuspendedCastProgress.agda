module MonoRef.Dynamics.Efficient.StdStore.SuspendedCastProgress where

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.StdStore.ApplyCast
open import MonoRef.Dynamics.Efficient.StdStore.Store
open import MonoRef.Dynamics.Efficient.Value
open import MonoRef.Dynamics.Progress.StdStore
  _⟹_ Inert
open ParamStdStoreProgress/Pre Value
open ParamStdStoreProgress
  make-coercion SimpleValue ref⟹T ref⟹∈ ref⟹⊑ typeprecise-strenthen-val
  apply-cast public
