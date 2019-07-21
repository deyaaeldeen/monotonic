module MonoRef.Dynamics.Simple.SReduction where

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.Reduction
  _⟹_ Inert make-coercion public
open import MonoRef.Dynamics.Simple.Store
open import MonoRef.Dynamics.Simple.SValue public


open ParamReduction Value DelayedCast ReducibleDelayedCast ref⟹T ref⟹∈ ref⟹⊑ public
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ ν-cast ν-update/ref store _⟶ᵤ_ public
