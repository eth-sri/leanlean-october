import GS.MatrixGeometry.Cayley

import GS.UnitaryManifold.CayleyModel
import Mathlib.Analysis.Complex.Basic



/-!
# Smooth rational matrix formulas with the inherited matrix topology

The explicitly selected entrywise supremum norm on `CMat n` is not assumed to make it a
normed algebra under matrix multiplication. Smoothness of multiplication is
proved entrywise; smoothness of inverse follows from det and adjugate.
No matrix determinant nonvanishing assumption is dropped.

The calculus is over real scalars throughout.
-/

namespace GS.UnitaryManifold
export GS.MatrixBase (smooth_mul_at smooth_det smooth_adjugate smooth_inverse_at smooth_inverse_comp_at smooth_cayley_at smooth_cayley_comp_at admissible_open)











end GS.UnitaryManifold
