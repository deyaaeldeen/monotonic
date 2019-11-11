module MonoRef.Dynamics.Efficient.StdStore.ReflTransClosure where

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Reduction.StdStore.ReflTransClosure
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.StdStore.Reduction
open import MonoRef.Dynamics.Efficient.StdStore.Store


open ParamReflTransClosure Value
open ParamReflTransClosure/⟶ _,_,_⟶_,_,_ public
