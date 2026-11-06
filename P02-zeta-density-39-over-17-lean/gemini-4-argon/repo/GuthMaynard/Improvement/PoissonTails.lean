module
public import GuthMaynard.Improvement.SmoothingFourier
public import MathCollab.Density.Packing

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped SchwartzMap FourierTransform
namespace GuthMaynard.Improvement

/-- A uniform shifted lattice majorant, reusing the audited packing estimate. -/
theorem shifted_lattice_decay (α : ℝ) :
    Summable (fun n : ℤ => 1/(1+|(n:ℝ)-α|)^2) ∧
    (∑' n : ℤ, 1/(1+|(n:ℝ)-α|)^2) ≤ MathCollab.Density.separationMass := by
  let q := ⌊-α⌋
  let F : ℤ → ℝ := fun n => 4/(1+|(n:ℝ)|)^2
  have hs : Summable (fun n : ℤ => F (n+q)) :=
    (Equiv.addRight q).summable_iff.mpr MathCollab.Density.summable_separation_majorant
  have hb (n : ℤ) : 1/(1+|(n:ℝ)-α|)^2 ≤ F (n+q) := by
    simpa [F, q, sub_eq_add_neg, Int.floor_intCast_add] using
      MathCollab.Density.decay_le_floor_majorant ((n:ℝ)-α)
  have hi := hs.of_nonneg_of_le (fun n => by positivity) hb
  refine ⟨hi, (hi.tsum_le_tsum hb hs).trans_eq ?_⟩
  exact (Equiv.addRight q).tsum_eq F

def poissonRemainder (ψ : ℝ → ℂ) (R α H : ℝ) (n : ℤ) : ℂ :=
  if H < |R*((n:ℝ)-α)| then 𝓕 ψ (R*((n:ℝ)-α)) else 0

