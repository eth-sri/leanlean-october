module
public import HalfLossTypeIISlab

@[expose] public section

open Complex Filter Set MathCollab.Density
open scoped Topology

namespace GuthMaynard.Improvement

/-- Type-I count before restoring multiplicity and ordinate collisions. -/
abbrev SeparatedTypeI (σ H B : ℝ) : Prop :=
  ∀ R : Finset ℂ, R ⊆ zetaZeroFinset σ H (2*H) →
    (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
    (∀ ρ ∈ R, (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) → (R.card:ℝ) ≤ B

/-- Use the ordinary fourth moment for Type II, restore multiplicities, and sum the slabs. -/
theorem short_density_of_typeI {σ p ε : ℝ} (hσ : 9/13 ≤ σ) (hp : 0 ≤ p)
    (hIIexp : 2-2*σ+1/50 ≤ p) (hε : 0 < ε)
    (hI : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ H : ℝ in atTop, SeparatedTypeI σ H (C*H^(p+δ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T:ℝ) ≤ C*T^(p+ε) := by
  have hη : 0 < ε/2 := by positivity
  obtain ⟨CI,hCI,hI⟩ := hI (ε/2) hη
  obtain ⟨CII,hCII,hII⟩ := half_loss_typeII_zero_slab_count hη
  obtain ⟨C₀,hC₀,hrestore⟩ := short_slab_count_of_separated_branch_bounds
  let D : ℝ := Real.log 2+1/(ε/2)
  have hD : 0 < D := add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (by positivity)
  apply zetaDensity_bound_of_eventual_slabs (add_pos_of_nonneg_of_pos hp hε)
    (show 0 < C₀*(CI+CII)*D by positivity)
  filter_upwards [eventually_ge_atTop (2:ℝ),hI,hII,hrestore] with H hH hi hii hr
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hb := hr σ (CI*H^(p+ε/2)) (CII*H^(p+ε/2)) hσ hi fun R hR hc hs hl =>
    (hii σ R hσ hR hc hs hl).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)) hCII.le)
  have hlog : Real.log (2*H) ≤ D*H^(ε/2) := classical_log_budget hH1 hη
  calc
    _ ≤ C₀*Real.log (2*H)*(CI*H^(p+ε/2)+CII*H^(p+ε/2)) := hb
    _ ≤ C₀*(D*H^(ε/2))*(CI*H^(p+ε/2)+CII*H^(p+ε/2)) := by gcongr
    _ = (C₀*(CI+CII)*D)*(H^(ε/2)*H^(p+ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring

end GuthMaynard.Improvement
