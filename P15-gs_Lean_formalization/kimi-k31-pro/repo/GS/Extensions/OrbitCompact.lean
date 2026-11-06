module

public import GS.Extensions.FiniteTopology
public import GS.Extensions.ProjectionSmooth

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Actual compactness of orthogonal block factors and their matrix images

Compactness/closedness is not confused with smoothness.
The theorems apply to m=2 and m=3; m=3 can still be singular.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.Extensions
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

 theorem orthogonal_entry_abs_le_one {A : Mat n} (hA : Orthogonal A) (i j : Fin n) :
    |A i j| ≤ 1 := by
  have hg := congrFun (congrFun hA.1 j) j
  have he : (∑ k : Fin n, A k j * A k j)=1 := by
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using hg
  have hs : A i j * A i j ≤ 1 := by
    rw [← he]
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg (A k j)) (Finset.mem_univ i)
  by_contra hn
  have hp : 0 < (|A i j|-1)*(|A i j|+1) := by
    apply mul_pos
    · linarith [lt_of_not_ge hn]
    · positivity
  nlinarith [sq_abs (A i j)]

end GS.Extensions
