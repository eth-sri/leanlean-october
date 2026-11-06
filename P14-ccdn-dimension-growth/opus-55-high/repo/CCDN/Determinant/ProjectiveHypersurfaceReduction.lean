/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.ProjectiveHypersurfaceLocal
import CCDN.Determinant.ProjectiveReduction
import CCDN.Height.ProjectiveZeroLocus

/-! Projective residue points determine unit charts and integral lifts
in arbitrary dimension. Their reduced affine equations vanish at those lifts. -/

namespace CCDN
section
open MvPolynomial

