module MonoRef.Dynamics.Efficient.EvStore.ReflTransClosure where

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.EvStore.Reduction
open import MonoRef.Dynamics.Efficient.EvStore.Store
open import MonoRef.Dynamics.Reduction.EvolvingStore.ReflTransClosure
  _⟹_ Inert public


open ParamReflTransClosure Value DelayedCast
open ParamReflTransClosure/⟶ _,_⟶_,_ public
