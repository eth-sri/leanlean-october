/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.HypersurfaceHeightDeterminant
import CCDN.Determinant.HomogeneousDeterminantComparison

/-! Exact-rank Bombieri--Vaaler comparison for higher-dimensional hypersurfaces.
Absence of an auxiliary polynomial forces the explicit numerical inequality. -/

namespace CCDN
section
open MvPolynomial

/-- The Hilbert function `s` of a degree-`d` hypersurface in `n + 3` variables, defined by
`s + C(n + 2 + (M - d), M - d) = C(n + 2 + M, M)`, is positive in every degree `M ≥ d`. -/
lemma hypersurface_homogeneous_rank_pos {n d M s : ℕ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (n + 2 + (M - d)).choose (M - d) = (n + 2 + M).choose M) : 0 < s := by
  rw [← Nat.choose_symm_add,
    ← Nat.choose_symm_add] at hr
  have hM := hd.trans_le hdM
  have hmon := Nat.choose_le_choose (n + 2)
    (show n + 2 + (M - d) ≤ n + 1 + M by omega)
  have hpascal : (n + 2 + M).choose (n + 2) =
      (n + 1 + M).choose (n + 1) + (n + 1 + M).choose (n + 2) := by
    convert Nat.choose_succ_succ' (n + 1 + M) (n + 1) using 1
    congr 1
    omega
  have hp : 0 < (n + 1 + M).choose (n + 1) := Nat.choose_pos (by omega)
  omega
