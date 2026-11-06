module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationCorridor
import Mathlib.Tactic

/-! # Source cap centers and exact endpoints of physical reference paths -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/- The literal cap-center point has strict margins in the source cap. -/
theorem cap_center_affine {d } (P : KineticPoint d) (r : ℝ) :
    kineticAffine P r (⟨-(3 / 16 : ℝ), 0, 0⟩ : KineticPoint d) =
      ⟨stackStartTime P r, stackStartPosition P r, P.velocity⟩ := by
  ext i
  all_goals simp only [kineticAffine, stackStartTime, stackStartPosition,
    smul_zero, add_zero, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  all_goals ring

/- Every sampling subcylinder's cap center is a valid reference-path start. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
