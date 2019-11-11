module MonoRef.Dynamics.Simple.EvStore.SReduction where

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.EvStore.Reduction
  _⟹_ Inert make-coercion public
open import MonoRef.Dynamics.Simple.EvStore.Store
open import MonoRef.Dynamics.Simple.Value public


open ParamReduction Value valueP DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑ public
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ
  ν-cast (λ {A}{B} _ _ → Ref A B) ν-update/ref store _⟶ᵤ_ public
