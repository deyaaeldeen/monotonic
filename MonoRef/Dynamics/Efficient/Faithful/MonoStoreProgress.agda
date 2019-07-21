module MonoRef.Dynamics.Efficient.Faithful.MonoStoreProgress where

open import MonoRef.Dynamics.Efficient.Faithful.Coercions
open import MonoRef.Dynamics.Efficient.Faithful.Store
open import MonoRef.Dynamics.Efficient.Faithful.Value
open import MonoRef.Dynamics.MonoStoreProgress
  _⟹_ Inert

open ParamMonoStoreProgress SimpleValue Value DelayedCast ReducibleDelayedCast ref⟹T ref⟹∈ ref⟹⊑
open ParamMonoStoreProgress/ν-cast ν-cast public
