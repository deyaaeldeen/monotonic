module MonoRef.Dynamics.Efficient.Coercions where

open import MonoRef.Coercions.NormalForm.Plain.Compose public
open import MonoRef.Coercions.NormalForm.Plain.Syntax
  renaming ( NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
           public
open import MonoRef.Coercions.NormalForm.Plain.Make
  renaming (make-normal-form-coercion to make-coercion) public
open import MonoRef.Coercions.NormalForm.Plain.Reduction public
open import MonoRef.Coercions.NormalForm.Plain.DelayedCastReduction public
