module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ConservationCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalCutoffLimitClassical
public import PDEFoundation.Calculus.RegularityOrder


/-! # Compact approximation of arbitrary bounded smooth full-space data -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous



variable (F : BoundedBorel (EvolutionAmbientState 1))

/-- Multiply a bounded datum by the actual compact cutoff in both physical coordinates. -/
def boundedConservationDatum  (N : ℕ) :
    BoundedBorel (EvolutionAmbientState 1) := by
  refine ⟨fun x => F x * conservationDatum N x,
    F.measurable.mul (conservationDatum N).measurable, ?_⟩
  obtain ⟨C, hC0, hC⟩ := F.exists_bound
  refine ⟨C, hC0, ?_⟩
  intro x
  rw [abs_mul, abs_of_nonneg (conservationDatum_bounds N x).1]
  exact (mul_le_mul_of_nonneg_left (conservationDatum_bounds N x).2
    (abs_nonneg _)).trans (by simpa using hC x)

/-- The compact approximation has the same absolute bound as its terminal datum. -/
theorem boundedConservationDatum_bound
    {C : ℝ} (hC : ∀ x, |F x| ≤ C) (N : ℕ) (x : EvolutionAmbientState 1) :
    |boundedConservationDatum F N x| ≤ C := by
  change |F x * conservationDatum N x| ≤ C
  rw [abs_mul, abs_of_nonneg (conservationDatum_bounds N x).1]
  exact (mul_le_mul_of_nonneg_left (conservationDatum_bounds N x).2
    (abs_nonneg _)).trans (by simpa using hC x)

/-- Both-coordinate approximation preserves smoothness and has compact support. -/
theorem boundedConservationDatum_smoothCompact
     (hF : ContDiff ℝ PDE.smoothOrder F)
    (N : ℕ) (τ : ℝ) :
    IsSmoothCompactTerminalDatum autonomousWholeDomain (fun _ => 0) τ
      (boundedConservationDatum F N) := by
  have hc := conservationDatum_smoothCompact N τ
  refine ⟨hF.mul hc.1, hc.2.1.mul_left, ?_⟩
  exact tsupport_mul_subset_right.trans hc.2.2

variable {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, |F x| ≤ C)

include hC0 hC
/-- The approximation error is controlled by a vanishing quadratic coefficient. -/
theorem boundedConservationDatum_error

    (N : ℕ) (x : EvolutionAmbientState 1) :
    |F x - boundedConservationDatum F N x| ≤ C / ((N : ℝ) + 1) ^ 2 *
      (1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2) := by
  change |F x - F x * conservationDatum N x| ≤ _
  rw [← mul_one_sub, abs_mul, abs_of_nonneg
    (sub_nonneg.mpr (conservationDatum_bounds N x).2)]
  have h := mul_le_mul (hC x) (conservationDatum_deficit N x)
    (sub_nonneg.mpr (conservationDatum_bounds N x).2) hC0
  convert h using 1
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- Ordered compact approximations satisfy the quadratic Cauchy estimate. -/
theorem boundedConservationDatum_sub

    {N M : ℕ} (hNM : N ≤ M) (x : EvolutionAmbientState 1) :
    |boundedConservationDatum F M x - boundedConservationDatum F N x| ≤
      (2 * C) / ((N : ℝ) + 1) ^ 2 *
        (1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2) := by
  let sharedTerm_1bc43129b0 := (((N : ℝ) + 1) ^ 2)
  have hN := boundedConservationDatum_error F hC0 hC N x
  have hM := boundedConservationDatum_error F hC0 hC M x
  have hden : sharedTerm_1bc43129b0 ≤ ((M : ℝ) + 1) ^ 2 := by
    have hn : (N : ℝ) ≤ M := by exact_mod_cast hNM
    nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) M]
  have hR : 0 ≤ 1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2 := by
    linarith [PDE.vecNormSq_nonneg x.1, PDE.vecNormSq_nonneg x.2]
  have hle := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hC0 (by positivity : (0 : ℝ) < sharedTerm_1bc43129b0) hden) hR
  have ht := abs_sub_le (boundedConservationDatum F M x) (F x)
    (boundedConservationDatum F N x)
  rw [abs_sub_comm (boundedConservationDatum F M x) (F x)] at ht
  have he : (2 * C) / sharedTerm_1bc43129b0 = 2 * (C / sharedTerm_1bc43129b0) := by ring
  rw [he]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
