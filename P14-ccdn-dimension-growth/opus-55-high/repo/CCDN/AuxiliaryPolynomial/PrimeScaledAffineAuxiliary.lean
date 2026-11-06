/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.ScaledHomogenization
import CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import CCDN.AuxiliaryPolynomial.ScaledAuxiliaryCount
import CCDN.Height.ProjectiveIntegerHeight

/-! The affine auxiliary polynomial obtained from a prime-scaled
homogeneous model. All point and nondivisibility transports are proved. -/

namespace CCDN
section
open MvPolynomial

