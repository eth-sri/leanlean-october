module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Ring

/-! # The exact spatial--velocity Jacobian of kinetic dilation -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- Product Lebesgue volume scales by the reciprocal of the kinetic determinant. -/
theorem map_dilate_volume (d : ℕ) (r : ℝ) (hr : 0 < r) :
    Measure.map (dilate (d := d) r) volume =
      ENNReal.ofReal (r⁻¹ ^ (4 * d)) • volume := by
  rw [Measure.volume_eq_prod]
  change Measure.map (Prod.map (fun x : PDE.Vec d => r ^ 3 • x)
    (fun v : PDE.Vec d => r • v)) ((volume : Measure (PDE.Vec d)).prod volume) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_addHaar_smul volume (pow_ne_zero 3 hr.ne'),
    Measure.map_addHaar_smul volume hr.ne',
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  simp only [Module.finrank_pi, Fintype.card_fin]
  congr 2
  rw [abs_of_pos (inv_pos.mpr (pow_pos (pow_pos hr 3) _)),
    abs_of_pos (inv_pos.mpr (pow_pos hr _)), ← mul_inv, ← pow_mul,
    ← pow_add, inv_pow]
  congr 1
  ring

section
variable {d : ℕ} (q : XV d)

/-- The gauge's defining Euclidean polynomial is its sixth power. -/
theorem rho_pow_six :
    rho q ^ (6 : ℕ) = PDE.vecNormSq q.1 + PDE.vecNormSq q.2 ^ (3 : ℕ) := by
  unfold rho
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul_natCast
    (add_nonneg (PDE.vecNormSq_nonneg _) (pow_nonneg (PDE.vecNormSq_nonneg _) _))]
  norm_num

/-- Euclidean coordinates obey the exact anisotropic gauge weights. -/
theorem rho_coordinate_bounds :
    PDE.vecEuclideanNorm q.1 ≤ rho q ^ 3 ∧ PDE.vecEuclideanNorm q.2 ≤ rho q := by
  have hr := rho_nonneg q
  have he := rho_pow_six q
  have hx := PDE.vecNormSq_nonneg q.1
  have hv := PDE.vecNormSq_nonneg q.2
  constructor
  · apply (sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg _) (pow_nonneg hr _)).mp
    rw [PDE.vecEuclideanNorm_sq, ← pow_mul]
    norm_num only at *
    linarith only [he, pow_nonneg hv 3]
  · apply (pow_le_pow_iff_left₀ (PDE.vecEuclideanNorm_nonneg _) hr
      (by decide : (6 : ℕ) ≠ 0)).mp
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, PDE.vecEuclideanNorm_sq, show (2 * 3 : ℕ) = 6 by decide, he]
    exact le_add_of_nonneg_left hx

end

/-- Bounded gauge sublevels have bounded native product norm. -/
theorem norm_le_of_rho_le {d : ℕ} (R : ℝ) (q : XV d)
    (hq : rho q ≤ R) : ‖q‖ ≤ max (R ^ 3) R := by
  have hb := rho_coordinate_bounds q
  rw [Prod.norm_def]
  exact max_le
    ((PDE.norm_le_vecEuclideanNorm _).trans
      (hb.1.trans ((pow_le_pow_left₀ (rho_nonneg q) hq 3).trans (le_max_left _ _))))
    ((PDE.norm_le_vecEuclideanNorm _).trans (hb.2.trans (hq.trans (le_max_right _ _))))

/-- Every closed gauge sublevel is compact in the native finite-dimensional topology. -/
theorem isCompact_rho_sublevel (d : ℕ) (R : ℝ) :
    IsCompact {q : XV d | rho q ≤ R} := by
  apply Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_rho d) continuous_const)
  exact isBounded_iff_forall_norm_le.2
    ⟨max (R ^ 3) R, fun q hq => norm_le_of_rho_le R q hq⟩

/-- The positive kinetic dilation carrying every nonzero point to the unit gauge shell. -/
noncomputable def normalizeGauge {d : ℕ} (q : XV d) : XV d := dilate (rho q)⁻¹ q

section
variable {d : ℕ} (q : XV d) (hq : q ≠ 0)
include hq

/-- A nonzero point normalizes to the unit gauge shell. -/
theorem rho_normalizeGauge : rho (normalizeGauge q) = 1 := by
  have hr := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
  rw [normalizeGauge, rho_dilate _ (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

/-- Gauge normalization preserves nonzero points. -/
theorem normalizeGauge_ne_zero : normalizeGauge q ≠ 0 := by
  intro hz
  have hh := rho_normalizeGauge q hq
  simp [hz] at hh

/-- Positive dilation by the gauge recovers the original nonzero point. -/
theorem dilate_normalizeGauge :
    dilate (rho q) (normalizeGauge q) = q := by
  have hr : rho q ≠ 0 := (rho_eq_zero_iff q).not.mpr hq
  rw [normalizeGauge, dilate_mul, mul_inv_cancel₀ hr, dilate_one]

end

/-- Normalization is continuous throughout the punctured kinetic space. -/
theorem continuousOn_normalizeGauge (d : ℕ) :
    ContinuousOn (normalizeGauge (d := d)) ({0}ᶜ) := by
  have hi := (continuous_rho d).continuousOn.inv₀ (fun q hq => (rho_eq_zero_iff q).not.mpr hq)
  exact (hi.pow 3 |>.smul continuous_fst.continuousOn).prodMk
    (hi.smul continuous_snd.continuousOn)

/-- The unit kinetic gauge shell is compact in native coordinates. -/
theorem isCompact_unitGaugeShell (d : ℕ) : IsCompact {q : XV d | rho q = 1} :=
  (isCompact_rho_sublevel d 1).of_isClosed_subset
    (isClosed_eq (continuous_rho d) continuous_const) (fun _ h => le_of_eq h)

/-- A positive continuous scalar weight on a compact set has joint positive finite bounds. -/
theorem exists_positive_bounds_on_compact {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (w : X → ℝ) (hw : ContinuousOn w K)
    (hpos : ∀ x ∈ K, 0 < w x) :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧
      ∀ x ∈ K, lower ≤ w x ∧ w x ≤ upper := by
  by_cases hne : K.Nonempty
  · obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hw
    obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne hw
    refine ⟨w a, w b, hpos a ha, hmin hb, ?_⟩
    intro x hx
    exact ⟨hmin hx, hmax hx⟩
  · refine ⟨1, 1, zero_lt_one, le_rfl, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

theorem ne_zero_of_rho_eq_one {d : ℕ} {q : XV d} (hq : rho q = 1) : q ≠ 0 := by
  rintro rfl
  simp at hq

/-- Positive-degree homogeneity transports compact shell bounds to the whole space. -/
theorem homogeneous_profile_comparison {d : ℕ} (alpha : ℝ) (ha : 0 < alpha)
    (H : XV d → ℝ) (hzero : H 0 = 0) (hcont : ContinuousOn H ({0}ᶜ))
    (hpos : ∀ q, q ≠ 0 → 0 < H q)
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ q,
      c * Real.rpow (rho q) alpha ≤ H q ∧ H q ≤ C * Real.rpow (rho q) alpha := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_positive_bounds_on_compact _
    (isCompact_unitGaugeShell d) H (hcont.mono fun _ h => ne_zero_of_rho_eq_one h)
    (fun q h => hpos q (ne_zero_of_rho_eq_one h))
  refine ⟨c, C, hc, hC, fun q => ?_⟩
  by_cases hq : q = 0
  · simp [hq, hzero, Real.zero_rpow ha.ne']
  have hr := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
  have he := hhom (rho q) hr (normalizeGauge q)
  rw [dilate_normalizeGauge q hq] at he
  rw [he]
  have hp := (Real.rpow_pos_of_pos hr alpha).le
  obtain ⟨hl, hu⟩ := hb _ (rho_normalizeGauge q hq)
  exact ⟨by simpa only [Real.rpow_eq_pow, mul_comm] using mul_le_mul_of_nonneg_left hl hp,
    by simpa only [Real.rpow_eq_pow, mul_comm] using mul_le_mul_of_nonneg_left hu hp⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
