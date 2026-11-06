module

public import GS.CayleyCharts.Smooth
public import GS.LieAction.BlockGroup

@[expose] public section

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.LieAction
namespace GS.CayleyCharts
variable {n : ℕ} {block : Fin n → ℕ}

def parameterDomain (block : Fin n → ℕ) : Set (Model block) :=
  {x | admissible x.val}

/-- Reconstruction is an actual rational matrix formula. -/
def chartInv (Q : BlockO block) (x : Model block) : Mat n :=
  Q.val * cayley x.val

@[simp] theorem chartInv_zero (Q : BlockO block) : chartInv Q 0 = Q.val := by
  simp [chartInv]

theorem chartInv_smooth_at (Q : BlockO block) (x : Model block)
    (hx : x ∈ parameterDomain block) : ContDiffAt ℝ ⊤ (chartInv Q) x :=
  smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at (modelInclusion block).contDiff.contDiffAt hx)

/-- Reconstruction is smooth on the entire finite-dimensional coordinate space. -/
theorem chartInv_smooth (Q : BlockO block) : ContDiff ℝ ⊤ (chartInv Q) := by
  exact contDiff_iff_contDiffAt.mpr (fun x => chartInv_smooth_at Q x (admissible_model x))

end GS.CayleyCharts
