module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionTerminalGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveRegularityExhaustion

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set


/-- A compact terminal support has a uniform Euclidean transported-coordinate bound. -/
theorem exists_transported_terminal_support_bound
    {n : ℕ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hFc : HasCompactSupport (F : EvolutionAmbientState n → ℝ)) :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      PDE.vecEuclideanNorm q.2 ≤ Z := by
  obtain ⟨Z, hZ⟩ := hFc.bddAbove_image
    (PDE.continuous_vecEuclideanNorm.comp continuous_snd).continuousOn
  refine ⟨max Z 0, le_max_right _ _, fun q hq => ?_⟩
  exact (hZ ⟨q, hq, rfl⟩).trans (le_max_left _ _)

/-- Every sufficiently large transported radius satisfies the terminal support margin
condition. The threshold depends only on the fixed diffused radius, collar margin and Z. -/
theorem exists_transportedRadius_terminal_window {r d : ℝ} (hr : 0 < r) (hd : 0 < d)
    (hdr : d < r) (Z : ℝ) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 ≤ R →
      (r - d) ^ 2 / r ^ 2 + Z ^ 2 / R ^ 2 < 1 := by
  have hsq : (r - d) ^ 2 < r ^ 2 := by nlinarith
  let η := 1 - (r - d) ^ 2 / r ^ 2
  have hη : 0 < η := sub_pos.mpr ((div_lt_one (sq_pos_of_pos hr)).mpr hsq)
  let R0 := 1 + (Z ^ 2 + 1) / η
  have hR01 : 1 < R0 := by
    have : 0 < (Z ^ 2 + 1) / η := div_pos (by positivity) hη
    linarith
  refine ⟨R0, by linarith, fun R hR => ?_⟩
  have hR1 := hR01.le.trans hR
  have hRsq : R0 ≤ R ^ 2 := by nlinarith
  have he : η * R0 = η + (Z ^ 2 + 1) := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ hη.ne']
  have hz : Z ^ 2 < η * R ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hRsq hη.le
    linarith
  have hf : Z ^ 2 / R ^ 2 < η := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  dsimp only [η] at hf
  linarith



/-- A fixed common inner cylinder is contained in all sufficiently large ellipsoids
whose diffused radii have a common lower bound separated from the inner cylinder. -/
theorem exists_transportedRadius_common_innerCylinder
    {rmin ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 ≤ η) (hgap : ρ + η < rmin) (S : ℝ) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ r R : ℝ, rmin ≤ r → R0 ≤ R →
      (ρ + η) ^ 2 / r ^ 2 + S ^ 2 / R ^ 2 < 1 := by
  have hrmin : 0 < rmin := lt_trans (by linarith) hgap
  obtain ⟨R0, hR0, hR⟩ := exists_transportedRadius_terminal_window hrmin
    (sub_pos.mpr hgap) (by linarith : rmin - (ρ + η) < rmin) S
  refine ⟨R0, hR0, fun r R hr hRR => ?_⟩
  have hsize := hR R hRR
  have he : rmin - (rmin - (ρ + η)) = ρ + η := by ring
  rw [he] at hsize
  have hdiv : (ρ + η) ^ 2 / r ^ 2 ≤ (ρ + η) ^ 2 / rmin ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hrmin)
      (pow_le_pow_left₀ hrmin.le hr 2)
  linarith

/-- The original terminal support margin survives the source inner-ball approximation
with radius loss α and centre error at most α/2, once α ≤ d. -/
theorem terminal_support_margin_of_innerBall_close
    {n : ℕ} {Γ g : ℝ → PDE.Vec n} {τ r0 α d : ℝ} (hαd : α ≤ d)
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ))
    (hc : PDE.vecEuclideanNorm (g τ - Γ τ) ≤ α / 2) :
    ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ (r0 - α) - PDE.vecEuclideanNorm (q.1 - g τ) := by
  intro q hq
  have hclose := vecEuclideanNorm_sub_add_le (c := 0) hc q.1
  simp at hclose
  have hs := hsupp q hq
  have hα0 : 0 ≤ α := by
    have := (PDE.vecEuclideanNorm_nonneg _).trans hc
    linarith
  linarith

end HypoellipticAleksandrov.KineticAleksandrov

