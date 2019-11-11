module MonoRef.Dynamics.Efficient.EvStore.StateReduction where

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Reduction.EvolvingStore.StateReduction
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.EvStore.CastReduction
  renaming (_,_⟶_,_ to _,_⟶ᶜ_,_ ; ⟶⟹⊑ₕ to ⟶ᶜ⟹⊑ₕ) public
open import MonoRef.Dynamics.Efficient.EvStore.Store
open import MonoRef.Dynamics.Efficient.Frames
open import MonoRef.Dynamics.Efficient.Value

open ParamStateReduction
    SimpleValue Value valueP DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑
open ParamStateReduction/ν-cast/⟶ᶜ/⟶ᶜ⟹⊑ₕ ν-cast _,_⟶ᶜ_,_ ⟶ᶜ⟹⊑ₕ Frame plug public
