module MonoRef.Dynamics.Efficient.Faithful.ReflTransClosure where

open import MonoRef.Coercions.NormalForm.Faithful.Syntax
open import MonoRef.Dynamics.Reduction.ReflTransClosure
  NormalFormCoercion InertNormalForm
open import MonoRef.Dynamics.Efficient.Faithful.Reduction
open import MonoRef.Dynamics.Efficient.Faithful.Store


open ParamReflTransClosure Value CastedValue StrongCastedValue
open ParamReflTransClosure/⟶ₛ _,_⟶ₛ_,_ public

