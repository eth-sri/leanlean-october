/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.SingularReduction
import CCDN.Determinant.PlaneMultiplicitySmooth
import CCDN.ForMathlib.MvPolynomial

/-! The local exponent at a possibly singular plane reduction, bounded by
the residue-point count plus the singular correction. -/

namespace CCDN
section
open Finset Real MvPolynomial

