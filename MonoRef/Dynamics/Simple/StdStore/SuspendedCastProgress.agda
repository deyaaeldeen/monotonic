module MonoRef.Dynamics.Simple.StdStore.SuspendedCastProgress where

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.StdStore.ApplyCast
open import MonoRef.Dynamics.Simple.Value
open import MonoRef.Dynamics.Simple.StdStore.Store
open import MonoRef.Dynamics.Progress.StdStore
  _⟹_ Inert
open ParamStdStoreProgress/Pre Value
open ParamStdStoreProgress
  make-coercion Value ref⟹T ref⟹∈ ref⟹⊑ typeprecise-strenthen-val
  apply-cast public
