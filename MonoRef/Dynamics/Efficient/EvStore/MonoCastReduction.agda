{-

  MonoRef.Dynamics.Efficient.EvStore.MonoCastReduction provides a reduction
  relation for casts on monotonic references with faithful coercions.

-}

module MonoRef.Dynamics.Efficient.EvStore.MonoCastReduction where

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.EvStore.Store
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Dynamics.Efficient.Value
open import MonoRef.Dynamics.Reduction.EvolvingStore.MonoCastReduction
  _⟹_ Inert
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations

open ParamMonoCastReduction
  SimpleValue Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑ public
open ParamMonoCastReduction/ν-cast
  ν-cast ((λ {A}{B} C x → final (middle (Ref C x)))) public
