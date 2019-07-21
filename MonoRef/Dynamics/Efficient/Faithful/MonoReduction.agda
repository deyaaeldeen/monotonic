module MonoRef.Dynamics.Efficient.Faithful.MonoReduction where

open import MonoRef.Dynamics.Efficient.Faithful.Coercions
open import MonoRef.Dynamics.Efficient.Faithful.Store
open import MonoRef.Dynamics.Efficient.Faithful.Value
open import MonoRef.Dynamics.Reduction.MonoReduction
  _⟹_ Inert make-coercion

open ParamMonoReduction
  SimpleValue Value DelayedCast ReducibleDelayedCast ref⟹T ref⟹∈ ref⟹⊑ public
open ParamMonoReduction/ν-update/ref/store ν-update/ref store public
