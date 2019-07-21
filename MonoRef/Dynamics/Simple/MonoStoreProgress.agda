module MonoRef.Dynamics.Simple.MonoStoreProgress where

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.Store
open import MonoRef.Dynamics.Simple.SValue
open import MonoRef.Dynamics.MonoStoreProgress
  _⟹_ Inert

open ParamMonoStoreProgress Value Value DelayedCast ReducibleDelayedCast ref⟹T ref⟹∈ ref⟹⊑
open ParamMonoStoreProgress/ν-cast ν-cast public
