module MonoRef.Dynamics.Simple.EvStore.ReflTransClosure where

open import MonoRef.Coercions.Syntax
open import MonoRef.Dynamics.Reduction.EvolvingStore.ReflTransClosure
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.EvStore.SReduction
open import MonoRef.Dynamics.Simple.EvStore.Store


open ParamReflTransClosure Value DelayedCast
open ParamReflTransClosure/⟶ _,_⟶_,_ public
