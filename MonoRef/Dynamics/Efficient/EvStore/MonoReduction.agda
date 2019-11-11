module MonoRef.Dynamics.Efficient.EvStore.MonoReduction where

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.EvStore.Store
open import MonoRef.Dynamics.Efficient.Value
open import MonoRef.Dynamics.Reduction.EvolvingStore.MonoReduction
  _⟹_ Inert

open ParamMonoReduction
  SimpleValue Value valueP DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑ public
open ParamMonoReduction/ν-update/ref/store make-coercion ν-update/ref store public
