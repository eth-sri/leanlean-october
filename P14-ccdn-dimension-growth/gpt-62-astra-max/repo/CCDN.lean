/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AffineCurveBound
public import CCDN.AffineHypersurfaceDimensionGrowth
public import CCDN.ClassGroupBound
public import CCDN.ProjectiveCurveBound
public import CCDN.ProjectiveCurveLowerBound
public import CCDN.ProjectiveDimensionGrowth

/-!
# CCDN

Root module of the formalisation of Castryck, Cluckers, Dittmann and Nguyen, *The dimension
growth conjecture, polynomial in the degree and without logarithmic factors* (Algebra & Number
Theory 14, 2020). It imports every module of the main library, which contains exactly the
modules that the main results need; `scripts/update-root.py` generates it. The rest of the
paper (Section 5, the paper's intermediate statements as printed, the counterexamples and the
results only they use) is in the separate library `CCDNPaper`, which this library does not
import.

The main results are:
* `CCDN.projective_dimension_growth` (Theorem 1);
* `CCDN.projectiveCurveBound` (Theorem 2);
* `CCDN.affineCurveBound` (Theorem 3);
* `CCDN.affine_hypersurface_dimension_growth` and its rational form (Theorem 4);
* `CCDN.projective_integral_curve_lower_bound` (Proposition 5);
* `CCDN.classGroup_two_torsion_bound` (Theorem 6).

`Challenge.lean` states them using Mathlib only, and `Solution.lean` derives those statements
from this library.
-/
