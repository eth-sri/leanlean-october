/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.ProfileFaceUnion

/-! # Original-cap completion survives face gluing and profile saturation

`CapFace` is the relative lifting property of a literal occurrence map.
Gluing two such maps along their common face constructs the property on both
inclusions into the union. Saturation preserves it by the proved profile
lifting theorem. These are boundary and row-family statements; no forcing
condition or new support-plan legality is inferred.
-/

namespace VaughtConjecture.Knight.ProfileFaceGluing



variable {C X Y  : Type*}

variable  (g : C ↪ Y)  
open ProfileFaceUnion

noncomputable instance [Fintype X] [Fintype Y] : Fintype (Carrier (X := X) g) := by
  classical
  unfold Carrier
  infer_instance

