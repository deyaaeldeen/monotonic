module MonoRef.Dynamics.Efficient.Faithful.Coercions where

open import MonoRef.Coercions.NormalForm.Faithful.Compose public
open import MonoRef.Coercions.NormalForm.Faithful.Syntax
  renaming ( NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
           public
open import MonoRef.Coercions.NormalForm.Faithful.Make
  renaming (make-normal-form-coercion to make-coercion) public
open import MonoRef.Coercions.NormalForm.Faithful.Reduction public
open import MonoRef.Coercions.NormalForm.Faithful.CastedValueReduction public
