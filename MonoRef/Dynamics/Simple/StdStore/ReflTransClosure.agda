module MonoRef.Dynamics.Simple.StdStore.ReflTransClosure where

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.Value
open import MonoRef.Dynamics.Reduction.StdStore.ReflTransClosure
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.StdStore.Reduction
open import MonoRef.Dynamics.Simple.StdStore.Store


open ParamReflTransClosure Value
open ParamReflTransClosure/⟶ _,_,_⟶_,_,_ public
