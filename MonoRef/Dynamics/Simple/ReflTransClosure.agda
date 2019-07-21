module MonoRef.Dynamics.Simple.ReflTransClosure where

open import MonoRef.Coercions.Syntax
open import MonoRef.Dynamics.Reduction.ReflTransClosure
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.SReduction
open import MonoRef.Dynamics.Simple.Store


open ParamReflTransClosure Value DelayedCast ReducibleDelayedCast
open ParamReflTransClosure/⟶ₛ _,_⟶ₛ_,_ public
