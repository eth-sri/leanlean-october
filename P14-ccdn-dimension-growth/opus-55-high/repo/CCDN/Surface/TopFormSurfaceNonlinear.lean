/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Surface.CurveComponents
import CCDN.Surface.TopFormAuxiliary
import CCDN.Surface.NonlinearCount
import CCDN.Surface.TopFormSurfaceComponents

/-! For an auxiliary section of a surface of degree at least sixteen,
all nonlinear components together contribute O(d^18 B) bounded integer points.
The union of the degree-one components is not covered by this estimate. -/

namespace CCDN
section
open MvPolynomial

