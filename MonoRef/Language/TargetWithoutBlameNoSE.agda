module MonoRef.Language.TargetWithoutBlameNoSE where

import MonoRef.Language.TargetWithoutBlame
open import MonoRef.Coercions.NoSpaceEfficiency.Syntax

module TargetWithoutBlameNoSE = MonoRef.Language.TargetWithoutBlame _⟹_ _!
open TargetWithoutBlameNoSE public
