module

public import RequestProject.LocalDirichletHigherDifferences

/-!
# Higher tangential energy for the actual flattened Dirichlet problem

Every boundary test in this file is a finite difference of the original
continuous zero-boundary function. No continuity or zero boundary value
of a derivative is presumed in the energy argument.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff

/-- The actual two-coordinate gradient energy density. -/
def dirichletGradientSq (v : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2

variable {μ : Measure ℂ} {v : ℂ → ℂ} {A b : ℝ} {U : Set ℂ}

theorem dirichletGradientSq_nonneg (v : ℂ → ℂ) (z : ℂ) :
    0 ≤ dirichletGradientSq v z :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem dirichletGradientSq_integrable (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2 μ) :
    Integrable (dirichletGradientSq v) μ := by
  have hx : MemLp (dirD v 1) 2 μ := by
    continuity
  have hy : MemLp (dirD v Complex.I) 2 μ := by
    continuity
  exact (hx.integrable_norm_pow (by norm_num)).add
    (hy.integrable_norm_pow (by norm_num))

/-- A simultaneous bound for the genuine finite differences. This is
the induction invariant, not an extra original-map assumption. -/
def DirichletDifferenceGradientBound (n : ℕ) (u : ℂ → ℂ)
    (a b ε E : ℝ) : Prop :=
  ∀ h : ℝ, h ∈ Ioo 0 ε → ∀ j : ℕ, j ≤ n →
    (∫ z in smoothDirichletHalfBox a b,
      dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z) ≤ E

/-- The already proved boundary energy method applies uniformly to
a family of genuine zero-boundary tests. Its data energies may come
from lower finite differences; the gradient bound is the conclusion. -/
theorem exists_dirichlet_family_gradient_energy {a b ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    (s : ℝ → ℝ) (v Q : ℝ → ℂ → ℂ) (C : ℝ → Fin 2 → ℂ → ℂ)
    (hvc : ∀ h ∈ Ioo 0 ε,
      ContinuousOn (v h) (smoothDirichletClosedHalfBox a b))
    (hvs : ∀ h ∈ Ioo 0 ε,
      ContDiffOn ℝ (⊤ : ℕ∞) (v h) (smoothDirichletHalfBox a b))
    (hvz : ∀ h ∈ Ioo 0 ε, ∀ x : ℝ, |x| < a → v h x = 0)
    (hvm : ∀ h ∈ Ioo 0 ε, MemLp (v h) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    (hvg : ∀ h ∈ Ioo 0 ε, ∀ i : Fin 2, MemLp (dirD (v h) (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    (hQm : ∀ h ∈ Ioo 0 ε, MemLp (Q h) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    (hCm : ∀ h ∈ Ioo 0 ε, ∀ i : Fin 2, MemLp (C h i) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    {Ev EQ EC : ℝ} (hEv : 0 ≤ Ev) (hEQ : 0 ≤ EQ) (hEC : 0 ≤ EC)
    (hvenergy : ∀ h ∈ Ioo 0 ε,
      (∫ z in smoothDirichletHalfBox a b, ‖v h z‖ ^ 2) ≤ Ev)
    (hQenergy : ∀ h ∈ Ioo 0 ε,
      (∫ z in smoothDirichletHalfBox a b, ‖Q h z‖ ^ 2) ≤ EQ)
    (hCenergy : ∀ h ∈ Ioo 0 ε,
      (∫ z in smoothDirichletHalfBox a b, ‖C h 0 z‖ ^ 2 + ‖C h 1 z‖ ^ 2) ≤ EC)
    (hweak : ∀ h ∈ Ioo 0 ε, ∀ φ : ℂ → ℂ,
      TestFunction (smoothDirichletHalfBox a b) φ →
      (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
        (dirichletShiftedFlux f (s h) (v h) i z + C h i z) *
          dirD φ (coordDir i) z) =
        ∫ z in smoothDirichletHalfBox a b, Q h z * φ z) :
    ∃ ρ E : ℝ, 0 < ρ ∧ ρ < a ∧ ρ < b ∧ 0 ≤ E ∧
      ∀ h ∈ Ioo 0 ε,
        (∫ z in smoothDirichletHalfBox ρ ρ, dirichletGradientSq (v h) z) ≤ E := by
  let V := smoothDirichletHalfBox a b
  obtain ⟨r, hr, hra, hrb, η, B, hB, hηsupp, hη, hηgrad, hηone⟩ :=
    exists_dirichlet_boundary_energy_cutoff ha hb
  let M := 2 * (1 + K ^ 2)
  let E := 2 * M * (EQ + (4 * M + 2 * B ^ 2) * EC +
    (32 * B ^ 2 * M ^ 3 + 2) * Ev)
  refine ⟨r / 2, E, by linarith, by linarith, by linarith, by positivity, ?_⟩
  intro h hh
  have hFm (i : Fin 2) : MemLp (dirichletShiftedFlux f (s h) (v h) i) 2
      (volume.restrict V) :=
    dirichletShiftedFlux_memLp hf hLip (s h) (hvg h hh) i
  let W := smoothDirichletHalfBox (r / 2) (r / 2)
  have hWsub : W ⊆ V := fun z hzW =>
    ⟨hzW.1.trans (by linarith), hzW.2.1, hzW.2.2.trans (by linarith)⟩
  have hηx := dirichlet_localized_memLp η
    (by
      simpa only [coordDir] using hvg h hh 0)
  have hW : (∫ z in W, dirichletGradientSq (v h) z) =
      ∫ z in W, ‖η z‖ ^ 2 * dirichletGradientSq (v h) z := by
    apply setIntegral_congr_fun (isOpen_smoothDirichletHalfBox _ _).measurableSet
    intro z hzW
    simp_all 
  rw [hW]
  exact (setIntegral_mono_set (by
    apply ((hηx.integrable_norm_pow (by norm_num)).add
      ((dirichlet_localized_memLp η
    (by
      simpa only [Matrix.cons_val_one] using hvg h hh 1)).integrable_norm_pow (by norm_num))).congr
    filter_upwards with z
    change ‖η z * dirD (v h) 1 z‖ ^ 2 + ‖η z * dirD (v h) Complex.I z‖ ^ 2 =
      ‖η z‖ ^ 2 * dirichletGradientSq (v h) z
    simp only [dirichletGradientSq, norm_mul]
    ring)
    (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
      (dirichletGradientSq_nonneg (v h) z)) hWsub.eventuallyLE).trans (by
    calc
      (∫ z in V, ‖η z‖ ^ 2 * dirichletGradientSq (v h) z) ≤
          (EQ + (4 * M + 2 * B ^ 2) * EC + (32 * B ^ 2 * M ^ 3 + 2) * Ev) *
            (2 * M) := (div_le_iff₀ (by positivity)).mp ((dirichlet_localized_boundary_energy_bound hb (by positivity) hB η
    hηsupp hη hηgrad (hvc h hh) (hvs h hh) (hvz h hh) (hvm h hh)
    (hvg h hh) hFm (hCm h hh) (hQm h hh)
    (fun z _ => dirichletShiftedFlux_coercive hLip (s h) (v h) z)
    (fun z _ => dirichletShiftedFlux_norm_sum_bound hLip (s h) (v h) z)
    (hweak h hh)).trans (add_le_add
      (add_le_add (hQenergy h hh) (mul_le_mul_of_nonneg_left (hCenergy h hh)
        (by positivity)))
      (mul_le_mul_of_nonneg_left (hvenergy h hh)
        (by positivity))))
      _ = E := by ring)

/-- Equality on the larger genuine box is preserved by every finite
quotient on the smaller box, with all translations counted. -/
theorem dirichletTangentialDifferenceIter_congr_on_halfBox {A a b h : ℝ}
    (k : ℕ) (hmargin : a + k * |h| ≤ A) {u v : ℂ → ℂ}
    (heq : EqOn u v (smoothDirichletHalfBox A b)) {z : ℂ}
    (hz : z ∈ smoothDirichletHalfBox a b) :
    dirichletTangentialDifferenceIter h k u z =
      dirichletTangentialDifferenceIter h k v z := by
  induction k generalizing a z with
  | zero =>
      exact heq ⟨hz.1.trans_le (by simp_all), hz.2⟩
  | succ k ih =>
      have hzh : z + h ∈ smoothDirichletHalfBox (a + |h|) b := by
        have hx := (abs_add_le z.re h).trans_lt (add_lt_add_of_lt_of_le hz.1 le_rfl)
        simp_all [smoothDirichletHalfBox]
      change (_ - _) / (h : ℂ) = (_ - _) / h
      grind

/-- The genuine kth quotient of the physical graph equation gives
the higher weak equation, with the exact graph commutator. -/
theorem dirichletTangentialDifferenceIter_weak_equation {A a b h : ℝ}
    (k : ℕ) (hmargin : a + k * |h| ≤ A) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    {φ : ℂ → ℂ} (hφ : TestFunction (smoothDirichletHalfBox a b) φ) :
    (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
      (dirichletShiftedFlux f (k * h)
          (dirichletTangentialDifferenceIter h k u) i z +
        dirichletHigherCoefficientDifferenceFlux f h k u i z) *
          dirD φ (coordDir i) z) =
      ∫ z in smoothDirichletHalfBox a b,
        dirichletTangentialDifferenceIter h k G z * φ z := by
  let U := smoothDirichletHalfBox A b
  let V := smoothDirichletHalfBox a b
  let H  := fun i =>
    dirichletTangentialDifferenceIter h k (dirichletFlattenedFlux f u i)
  have hV := isOpen_smoothDirichletHalfBox a b
  have hflux (i : Fin 2) : ContDiffOn ℝ (⊤ : ℕ∞) (dirichletFlattenedFlux f u i) U :=
    dirichletFlattenedFlux_contDiffOn (isOpen_smoothDirichletHalfBox A b) hf hs i
  have hH (i : Fin 2) : ContDiffOn ℝ (⊤ : ℕ∞) (H i) V :=
    dirichletTangentialDifferenceIter_contDiffOn k hmargin (hflux i)
  have hdiv (z : ℂ) (hz : z ∈ V) :
      (∑ i : Fin 2, dirD (H i) (coordDir i) z) =
        -dirichletTangentialDifferenceIter h k G z := by
    have hd (i : Fin 2) : dirD (H i) (coordDir i) z =
        dirichletTangentialDifferenceIter h k
          (dirD (dirichletFlattenedFlux f u i) (coordDir i)) z :=
      dirichletTangentialDifferenceIter_dirD k hmargin (hflux i) hz _
    simp_rw [hd]
    rw [Fin.sum_univ_two]
    simp only [coordDir, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← congrFun (dirichletTangentialDifferenceIter_add h k
      (dirD (dirichletFlattenedFlux f u 0) 1)
      (dirD (dirichletFlattenedFlux f u 1) Complex.I)) z]
    change dirichletTangentialDifferenceIter h k
      (dirichletFlattenedDivergence f u) z = _
    rw [dirichletTangentialDifferenceIter_congr_on_halfBox k hmargin hstrong hz]
    simpa only [neg_one_mul] using congrFun
      (dirichletTangentialDifferenceIter_const_mul h k (-1) G) z
  have hI (i : Fin 2) : IntegrableOn
      (fun z => H i z * dirD φ (coordDir i) z) V :=
    dirichlet_local_smooth_mul_test_integrable hV (hH i) (hφ.dirD (coordDir i))
  have hDI (i : Fin 2) : IntegrableOn
      (fun z => dirD (H i) (coordDir i) z * φ z) V :=
    dirichlet_local_smooth_mul_test_integrable hV
      (dirichlet_contDiffOn_dirD hV (hH i) (coordDir i)) hφ
  have heq : (∫ z in V, ∑ i : Fin 2, H i z * dirD φ (coordDir i) z) =
      -(∫ z in V, (∑ i : Fin 2, dirD (H i) (coordDir i) z) * φ z) := by
    rw [integral_finset_sum _ (fun i _ => hI i)]
    have hibp (i : Fin 2) :=
      dirichlet_local_smooth_field_test_eq_neg_dirD hV (hH i) hφ i
    rw [Finset.sum_congr rfl (fun i _ => hibp i), Finset.sum_neg_distrib, ← integral_finset_sum _ (fun i _ => hDI i)]
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    rw [Finset.sum_mul]
  have hleft : (∫ z in V, ∑ i : Fin 2,
      (dirichletShiftedFlux f (k * h)
          (dirichletTangentialDifferenceIter h k u) i z +
        dirichletHigherCoefficientDifferenceFlux f h k u i z) * dirD φ (coordDir i) z) =
      ∫ z in V, ∑ i : Fin 2, H i z * dirD φ (coordDir i) z := by
    apply setIntegral_congr_fun hV.measurableSet
    intro z hz
    apply Finset.sum_congr rfl
    intro i _
    rw [← dirichletTangentialDifferenceIter_flux_split k hmargin f hs hz i]
  rw [hleft, heq, ← integral_neg]
  apply setIntegral_congr_fun hV.measurableSet
  intro z hz
  grind

/-- Genuine uniform pointwise bounds for a smooth forcing give its
uniform L² energy on a finite half box. -/
theorem dirichlet_bounded_family_sq_energy {a b ε C : ℝ}
    {Q : ℝ → ℂ → ℂ} (hc : ∀ h : ℝ, Continuous (Q h))
    (hbound : ∀ h ∈ Ioo 0 ε, ∀ z ∈ smoothDirichletHalfBox a b, ‖Q h z‖ ≤ C) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ h ∈ Ioo 0 ε,
      MemLp (Q h) 2 (volume.restrict (smoothDirichletHalfBox a b)) ∧
      (∫ z in smoothDirichletHalfBox a b, ‖Q h z‖ ^ 2) ≤ E := by
  let V := smoothDirichletHalfBox a b
  let μ := volume.restrict V
  letI : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using
    (dirichlet_halfBox_isBounded  ).measure_lt_top⟩
  let E := ∫ z : ℂ, C ^ 2 ∂μ
  refine ⟨E, integral_nonneg (fun _ => sq_nonneg _), ?_⟩
  intro h hh
  have hm : MemLp (Q h) 2 μ := by
    apply MemLp.of_bound (hc h).aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    grind
  refine ⟨hm, ?_⟩
  apply integral_mono_ae (hm.integrable_norm_pow (by norm_num))
    (integrable_const _)
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound h hh z hz) 2

theorem dirichletTangentialDifferenceIter_measurable (hv : Measurable v) (h : ℝ) (k : ℕ) :
    Measurable (dirichletTangentialDifferenceIter h k v) := by
  induction k with
  | zero => assumption
  | succ k ih =>
      exact ((ih.comp (measurable_id.add_const (h : ℂ))).sub ih).div_const h

theorem dirichletHigherCoefficientCommutator_measurable {a v : ℂ → ℂ}
    (ha : Measurable a) (hv : Measurable v) (h : ℝ) (k : ℕ) :
    Measurable (dirichletHigherCoefficientCommutator h k a v) :=
  (dirichletTangentialDifferenceIter_measurable (ha.mul hv) h k).sub
    ((ha.comp (measurable_id.add_const ((k * h : ℝ) : ℂ))).mul
      (dirichletTangentialDifferenceIter_measurable hv h k))

theorem dirichletHigherCoefficientDifferenceFlux_measurable {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (h : ℝ) (k : ℕ) (u : ℂ → ℂ) (i : Fin 2) :
    Measurable (dirichletHigherCoefficientDifferenceFlux f h k u i) := by
  have hd := (dirichletGraphSlope_contDiff hf).continuous.measurable
  have hy := measurable_fderiv_apply_const ℝ u Complex.I
  fin_cases i
  · exact (dirichletHigherCoefficientCommutator_measurable hd hy h k).neg
  · exact (dirichletHigherCoefficientCommutator_measurable hd (measurable_fderiv_apply_const ℝ u 1) h k).neg.add (dirichletHigherCoefficientCommutator_measurable
    (measurable_const.add
      (hd.pow_const 2)) hy h k)

/-- The genuine graph commutator is controlled by lower gradient
quotients. The squared finite-sum estimate includes all binomial
weights; no translated input energy is used. -/
theorem dirichletHigherCoefficientDifferenceFlux_sq_bound
    {A a b h M : ℝ} (k : ℕ) (hmargin : a + k * |h| ≤ A)
    {f : ℝ → ℝ} {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hbound : ∀ (v : ℂ → ℂ) (z : ℂ), z ∈ smoothDirichletClosedHalfBox a b →
      (‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) v z‖ ≤
        M * ∑ j ∈ Finset.range k, k.choose j *
          ‖dirichletTangentialDifferenceIter h j v z‖) ∧
      (‖dirichletHigherCoefficientCommutator h k
          (fun w => 1 + dirichletGraphSlope f w ^ 2) v z‖ ≤
        M * ∑ j ∈ Finset.range k, k.choose j *
          ‖dirichletTangentialDifferenceIter h j v z‖))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) :
    ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ^ 2 +
      ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ^ 2 ≤
      (3 * M ^ 2 * ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2) *
        ∑ j ∈ Finset.range k,
          dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z := by
  let vx  := fun j => ‖dirD (dirichletTangentialDifferenceIter h j u) 1 z‖
  let vy  := fun j => ‖dirD (dirichletTangentialDifferenceIter h j u) Complex.I z‖
  let Sx := ∑ j ∈ Finset.range k, k.choose j * vx j
  let Sy := ∑ j ∈ Finset.range k, k.choose j * vy j
  let P := ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2
  have hdir (j : ℕ) (hj : j ∈ Finset.range k) (w : ℂ) :
      dirichletTangentialDifferenceIter h j (dirD u w) z =
        dirD (dirichletTangentialDifferenceIter h j u) w z := by
    have hjk  := (Finset.mem_range.mp hj).le
    exact (dirichletTangentialDifferenceIter_dirD j ((add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (by simp_all) (abs_nonneg h))).trans hmargin) hs hz w).symm
  have hclosed : z ∈ smoothDirichletClosedHalfBox a b := ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  have hcx : ‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
      (dirD u 1) z‖ ≤ M * Sx := (hbound (dirD u 1) z hclosed).1.trans_eq (congrArg (fun t => M * t) (Finset.sum_congr rfl
      (fun j hj => by grind)))
  have hsy : ‖dirichletHigherCoefficientCommutator h k
      (fun w => 1 + dirichletGraphSlope f w ^ 2) (dirD u Complex.I) z‖ ≤ M * Sy := (hbound (dirD u Complex.I) z hclosed).2.trans_eq (congrArg (fun t => M * t) (Finset.sum_congr rfl
      (fun j hj => by grind)))
  have h0 : ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ≤ M * Sy := by
    simpa only [dirichletHigherCoefficientDifferenceFlux, Matrix.cons_val_zero, norm_neg] using ((hbound (dirD u Complex.I) z hclosed).1.trans_eq (congrArg (fun t => M * t) (Finset.sum_congr rfl
      (fun j hj => by grind))))
  have h1 : ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ≤ M * (Sx + Sy) := (norm_add_le _ _).trans (by rw [norm_neg]; nlinarith )
  have hsum : Sx ^ 2 + Sy ^ 2 ≤ P *
      ∑ j ∈ Finset.range k, dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z := by
    simpa only [dirichletGradientSq, Finset.sum_add_distrib, mul_add] using
      add_le_add (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k) (fun j => (k.choose j : ℝ)) vx) (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k) (fun j => (k.choose j : ℝ)) vy)
  have hc0 := pow_le_pow_left₀ (norm_nonneg _) h0 2
  have hc1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hab : Sy ^ 2 + (Sx + Sy) ^ 2 ≤ 3 * (Sx ^ 2 + Sy ^ 2) := by
    nlinarith 
  nlinarith

/-- Fixed-step commutators are honest L² functions. Their measurable
representatives are the actual coefficient products and derivatives. -/
theorem dirichletHigherCoefficientDifferenceFlux_memLp
    {A a b h M : ℝ} (k : ℕ) (hmargin : a + k * |h| ≤ A)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u : ℂ → ℂ} (hM : 0 ≤ M)
    (hbound : ∀ (v : ℂ → ℂ) (z : ℂ), z ∈ smoothDirichletClosedHalfBox a b →
      (‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) v z‖ ≤
        M * ∑ j ∈ Finset.range k, k.choose j *
          ‖dirichletTangentialDifferenceIter h j v z‖) ∧
      (‖dirichletHigherCoefficientCommutator h k
          (fun w => 1 + dirichletGraphSlope f w ^ 2) v z‖ ≤
        M * ∑ j ∈ Finset.range k, k.choose j *
          ‖dirichletTangentialDifferenceIter h j v z‖))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b))) (i : Fin 2) :
    MemLp (dirichletHigherCoefficientDifferenceFlux f h k u i) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let V := smoothDirichletHalfBox a b
  let μ := volume.restrict V
  let vx  := fun j z => ‖dirichletTangentialDifferenceIter h j (dirD u 1) z‖
  let vy  := fun j z => ‖dirichletTangentialDifferenceIter h j (dirD u Complex.I) z‖
  let B  := fun z => M * ∑ j ∈ Finset.range k,
    k.choose j * (vx j z + vy j z)
  have hBm : MemLp B 2 μ := by
    apply MemLp.const_mul _ M
    apply memLp_finset_sum
    intro j hj
    have hjk  := (Finset.mem_range.mp hj).le
    have hm : a + j * |h| ≤ A :=
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by simp_all)
        (abs_nonneg h))).trans hmargin
    exact ((dirichletTangentialDifferenceIter_memLp j hm (by
    continuity)).norm.add
      (dirichletTangentialDifferenceIter_memLp j hm (by
    continuity)).norm).const_mul (k.choose j)
  apply hBm.mono' (dirichletHigherCoefficientDifferenceFlux_measurable hf h k u i).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  have hz' : z ∈ smoothDirichletClosedHalfBox a b := ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  let Sx := ∑ j ∈ Finset.range k, k.choose j * vx j z
  let Sy := ∑ j ∈ Finset.range k, k.choose j * vy j z
  have hSx : 0 ≤ Sx := Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hBS : B z = M * (Sx + Sy) := by
    simp [B, Sx, Sy, mul_add, Finset.sum_add_distrib]
  have hcx  := (hbound (dirD u 1) z hz').1
  have hcy  := (hbound (dirD u Complex.I) z hz').1
  have hsy  :=
    (hbound (dirD u Complex.I) z hz').2
  fin_cases i
  · change ‖-dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
      (dirD u Complex.I) z‖ ≤ B z
    rw [norm_neg]
    nlinarith
  · calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ M * Sx + M * Sy := by rw [norm_neg]; linarith
      _ = B z := by linarith

/-- Integration of the exact squared commutator bound converts
simultaneous lower quotient energies into the next data energy. -/
theorem dirichletHigherCoefficientDifferenceFlux_energy_le
    {A a b h M E : ℝ} (k : ℕ) (hmargin : a + k * |h| ≤ A)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b)) (hM : 0 ≤ M)
    (hbound : ∀ (v : ℂ → ℂ) (z : ℂ), z ∈ smoothDirichletClosedHalfBox a b →
      (‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) v z‖ ≤
        M * ∑ j ∈ Finset.range k, k.choose j *
          ‖dirichletTangentialDifferenceIter h j v z‖) ∧
      (‖dirichletHigherCoefficientCommutator h k
          (fun w => 1 + dirichletGraphSlope f w ^ 2) v z‖ ≤
        M * ∑ j ∈ Finset.range k, k.choose j *
          ‖dirichletTangentialDifferenceIter h j v z‖))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (henergy : ∀ j ∈ Finset.range k,
      (∫ z in smoothDirichletHalfBox a b,
        dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z) ≤ E) :
    (∫ z in smoothDirichletHalfBox a b,
      ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ^ 2 +
        ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ^ 2) ≤
      (3 * M ^ 2 * ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2) * (k * E) := by
  let V := smoothDirichletHalfBox a b
  let D := 3 * M ^ 2 * ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2
  have hCm (i : Fin 2) :=
    dirichletHigherCoefficientDifferenceFlux_memLp k hmargin hf hM hbound hg i
  have hgi (j : ℕ) (hj : j ∈ Finset.range k) : IntegrableOn
      (dirichletGradientSq (dirichletTangentialDifferenceIter h j u)) V := by
    have hjk  := (Finset.mem_range.mp hj).le
    exact dirichletGradientSq_integrable
      (fun i => dirichletTangentialDifferenceIter_gradient_memLp j ((add_le_add le_rfl (mul_le_mul_of_nonneg_right (by simp_all)
        (abs_nonneg h))).trans hmargin) hs (hg i))
  have hbnd : (∫ z in V,
      ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ^ 2 +
        ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ^ 2) ≤
      ∫ z in V, D * ∑ j ∈ Finset.range k,
        dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z := by
    apply integral_mono_ae (((hCm 0).integrable_norm_pow (by norm_num)).add
    ((hCm 1).integrable_norm_pow (by norm_num))) ((integrable_finset_sum _ (fun j hj => hgi j hj)).const_mul D)
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    exact dirichletHigherCoefficientDifferenceFlux_sq_bound k hmargin hs hbound hz
  rw [integral_const_mul, integral_finset_sum _ (fun j hj => hgi j hj)] at hbnd
  exact hbnd.trans (mul_le_mul_of_nonneg_left
    (by simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j hj => henergy j hj)) (by
    positivity))

/-- Actual induction of the higher gradient energies. At every
finite order the tested functions are finite quotients of the original
zero-boundary function. Smooth coefficients and forcing supply their
own compact derivative bounds. No higher estimate is a premise. -/
theorem exists_dirichlet_halfBox_higher_difference_gradient_energy
    (hA : 0 < A) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    {u G : ℂ → ℂ} (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u x = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiff ℝ (⊤ : ℕ∞) G) (n : ℕ) :
    ∃ ρ ε E : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧ 0 < ε ∧ 0 ≤ E ∧
      DirichletDifferenceGradientBound n u ρ ρ ε E := by
  let U := smoothDirichletHalfBox A b
  induction n with
  | zero =>
      let ρ := min A b / 4
      have hρ : 0 < ρ := div_pos (lt_min hA hb) (by norm_num)
      have hρA : ρ < A / 2 := by
        grind
      have hρb : ρ < b := by
        grind
      let E := ∫ z in U, dirichletGradientSq u z
      have hsub : smoothDirichletHalfBox ρ ρ ⊆ U := fun z hz' =>
        ⟨hz'.1.trans (by linarith), hz'.2.1, hz'.2.2.trans hρb⟩
      refine ⟨ρ, 1, E, hρ, hρA, hρb, by norm_num, integral_nonneg (dirichletGradientSq_nonneg u), ?_⟩
      intro h hh j hj
      have hj0  := Nat.eq_zero_of_le_zero hj
      subst j
      exact setIntegral_mono_set (dirichletGradientSq_integrable hg)
        (Eventually.of_forall (dirichletGradientSq_nonneg u)) hsub.eventuallyLE
  | succ n ih =>
      obtain ⟨ρ, ε₀, E₀, hρ, hρA, hρb, hε₀, hE₀, hprev⟩ := ih
      let k := n + 1
      let W := smoothDirichletHalfBox ρ ρ
      let V := smoothDirichletHalfBox (ρ / 2) ρ
      let ε := min ε₀ (ρ / (4 * (k + 1)))
      have hε : 0 < ε := lt_min hε₀ (div_pos hρ (by positivity))
      have hVW : V ⊆ W := fun z hz' => ⟨hz'.1.trans (by linarith), hz'.2⟩
      have hsteps (h : ℝ) (hh : h ∈ Ioo 0 ε) :
          h ∈ Ioo 0 ε₀ ∧ ρ / 2 + k * |h| ≤ ρ ∧
            ρ + k * |h| ≤ A ∧ ρ / 2 + h < ρ := by
        have hh₀ := hh.2.trans_le (min_le_left _ _)
        have hkh : (k + 1) * h < ρ / 4 := by
          have hh' := (lt_div_iff₀ (by positivity)).mp (hh.2.trans_le (min_le_right _ _))
          nlinarith
        rw [abs_of_pos hh.1]
        refine ⟨⟨hh.1, hh₀⟩, ?_, ?_, ?_⟩ <;>
          nlinarith
      have hmargin (h : ℝ) (hh : h ∈ Ioo 0 ε) :
          ρ / 2 + k * |h| ≤ A :=
        ((hsteps h hh).2.1).trans (by linarith)
      have hpositiveMargin (h : ℝ) (hh : h ∈ Ioo 0 ε) :
          ρ / 2 + k * h ≤ ρ := by
        grind
      have hsmallgrad (h : ℝ) (hh : h ∈ Ioo 0 ε) (j : ℕ) (hj : j ≤ k)
          (i : Fin 2) : MemLp
            (dirD (dirichletTangentialDifferenceIter h j u) (coordDir i)) 2
            (volume.restrict W) := by
        have hmj : ρ + j * |h| ≤ A :=
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right
            (by simp_all) (abs_nonneg h))).trans (hsteps h hh).2.2.1
        exact (dirichletTangentialDifferenceIter_gradient_memLp j hmj hs (hg i)).mono_measure (Measure.restrict_mono_set volume
          (show W ⊆ smoothDirichletHalfBox ρ b from
            fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩))
      have hlower (h : ℝ) (hh : h ∈ Ioo 0 ε) (j : ℕ) (hj : j ≤ n) :
          (∫ z in V, dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z) ≤ E₀ := by
        exact (setIntegral_mono_set (dirichletGradientSq_integrable
          (hsmallgrad h hh j (hj.trans (Nat.le_succ n))))
          (Eventually.of_forall (dirichletGradientSq_nonneg _)) hVW.eventuallyLE).trans
          (hprev h (hsteps h hh).1 j hj)
      let v  := fun h => dirichletTangentialDifferenceIter h k u
      let Q  := fun h => dirichletTangentialDifferenceIter h k G
      let C  := fun h =>
        dirichletHigherCoefficientDifferenceFlux f h k u
      have hvc (h : ℝ) (hh : h ∈ Ioo 0 ε) :
          ContinuousOn (v h) (smoothDirichletClosedHalfBox (ρ / 2) ρ) :=
        (dirichletTangentialDifferenceIter_continuousOn k (hmargin h hh) hc).mono
          (fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb.le⟩)
      have hvs (h : ℝ) (hh : h ∈ Ioo 0 ε) : ContDiffOn ℝ (⊤ : ℕ∞) (v h) V :=
        (dirichletTangentialDifferenceIter_contDiffOn k (hmargin h hh) hs).mono
          (fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩)
      have hvz (h : ℝ) (hh : h ∈ Ioo 0 ε) (x : ℝ) (hx : |x| < ρ / 2) :
          v h x = 0 :=
        dirichletTangentialDifferenceIter_zero_bottom k (hmargin h hh) hz hx
      have hvm (h : ℝ) (hh : h ∈ Ioo 0 ε) : MemLp (v h) 2 (volume.restrict V) :=
        (dirichletTangentialDifferenceIter_memLp k (hmargin h hh) hm).mono_measure
          (Measure.restrict_mono_set volume
            (show V ⊆ smoothDirichletHalfBox (ρ / 2) b from
              fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩))
      have hvg (h : ℝ) (hh : h ∈ Ioo 0 ε) (i : Fin 2) :
          MemLp (dirD (v h) (coordDir i)) 2 (volume.restrict V) :=
        (hsmallgrad h hh k le_rfl i).mono_measure (Measure.restrict_mono_set volume hVW)
      have hvenergy (h : ℝ) (hh : h ∈ Ioo 0 ε) :
          (∫ z in V, ‖v h z‖ ^ 2) ≤ E₀ := by
        have hnmargin : ρ + n * |h| ≤ A :=
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right
            (by grind) (abs_nonneg h))).trans (hsteps h hh).2.2.1
        have hnx : MemLp (dirD (dirichletTangentialDifferenceIter h n u) 1) 2
            (volume.restrict W) := by
          simpa only [coordDir, Matrix.cons_val_zero] using hsmallgrad h hh n (Nat.le_succ n) 0
        exact (dirichlet_halfBox_tangential_difference_energy_le
          (by linarith) hρ hh.1 (hsteps h hh).2.2.2 ((dirichletTangentialDifferenceIter_contDiffOn n hnmargin hs).mono
          (fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩)) ((dirichletTangentialDifferenceIter_memLp n hnmargin hm).mono_measure
          (Measure.restrict_mono_set volume
            (show W ⊆ smoothDirichletHalfBox ρ b from
              fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩))) hnx).trans ((integral_mono_ae (hnx.integrable_norm_pow (by norm_num)) (dirichletGradientSq_integrable
          (hsmallgrad h hh n (Nat.le_succ n)))
            (Eventually.of_forall fun z => le_add_of_nonneg_right (sq_nonneg _))).trans (hprev h (hsteps h hh).1 n le_rfl))
      obtain ⟨MQ, hQbound⟩ := exists_dirichletTangentialDifferenceIter_bound hGs ρ ρ k
      obtain ⟨EQ, hEQ, hQdata⟩ := dirichlet_bounded_family_sq_energy
        (fun h => (dirichletTangentialDifferenceIter_contDiff hGs h k).continuous)
        (fun h hh z hz' => hQbound.2 (ρ / 2) h hh.1
          (hpositiveMargin h hh) z
          ⟨hz'.1.le, hz'.2.1.le, hz'.2.2.le⟩)
      obtain ⟨MC, hMC, hCbound⟩ := exists_dirichletGraphHigherCommutator_bound hf ρ ρ k
      let D := 3 * MC ^ 2 * ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2
      let EC := D * (k * E₀)
      have hCb (h : ℝ) (hh : h ∈ Ioo 0 ε) :=
        hCbound (ρ / 2) h hh.1
          (hpositiveMargin h hh)
      have hug (i : Fin 2) : MemLp (dirD u (coordDir i)) 2
          (volume.restrict (smoothDirichletHalfBox A ρ)) :=
        (hg i).mono_measure (Measure.restrict_mono_set volume
          (show smoothDirichletHalfBox A ρ ⊆ smoothDirichletHalfBox A b from
            fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩))
      have hus : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A ρ) :=
        hs.mono (fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩)
      have hCm (h : ℝ) (hh : h ∈ Ioo 0 ε) (i : Fin 2) :
          MemLp (C h i) 2 (volume.restrict V) :=
        dirichletHigherCoefficientDifferenceFlux_memLp k (hmargin h hh) hf hMC (hCb h hh) hug i
      have hCenergy (h : ℝ) (hh : h ∈ Ioo 0 ε) :
          (∫ z in V, ‖C h 0 z‖ ^ 2 + ‖C h 1 z‖ ^ 2) ≤ EC :=
        dirichletHigherCoefficientDifferenceFlux_energy_le k (hmargin h hh) hf hus hMC
          (hCb h hh) hug (fun j hj => hlower h hh j (by
            grind))
      have hweak (h : ℝ) (hh : h ∈ Ioo 0 ε) (φ : ℂ → ℂ) (hφ : TestFunction V φ) :
          (∫ z in V, ∑ i : Fin 2,
            (dirichletShiftedFlux f (k * h) (v h) i z + C h i z) *
              dirD φ (coordDir i) z) = ∫ z in V, Q h z * φ z :=
        dirichletTangentialDifferenceIter_weak_equation k (hmargin h hh) hf hus
          (fun z hz' => hstrong z ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩) hφ
      obtain ⟨r, E₁, hr, hra, hrρ, hE₁, hnew⟩ := exists_dirichlet_family_gradient_energy
        (by linarith) hρ hf hLip (fun h => k * h) v Q C
        hvc hvs hvz hvm hvg (fun h hh => (hQdata h hh).1) hCm hE₀ hEQ (by
        positivity)
        hvenergy (fun h hh => (hQdata h hh).2) hCenergy hweak
      let E := max E₀ E₁
      have hrW : smoothDirichletHalfBox r r ⊆ W := fun z hz' =>
        ⟨hz'.1.trans hrρ, hz'.2.1, hz'.2.2.trans hrρ⟩
      refine ⟨r, ε, E, hr, by linarith, hrρ.trans hρb, hε,
        hE₀.trans (le_max_left _ _), ?_⟩
      intro h hh j hj
      rcases Nat.eq_or_lt_of_le hj with hjk | hjk
      · grind
      · have hjn  := Nat.le_of_lt_succ hjk
        exact (setIntegral_mono_set (dirichletGradientSq_integrable (hsmallgrad h hh j (hjn.trans (Nat.le_succ n))))
          (Eventually.of_forall (dirichletGradientSq_nonneg _)) hrW.eventuallyLE).trans
          ((hprev h (hsteps h hh).1 j hjn).trans (le_max_left _ _))

theorem dirichletTangentialDerivative_contDiffOn (hU : IsOpen U)
    {u : ℂ → ℂ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) u U) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletTangentialDerivative n u) U := by
  induction n with
  | zero => assumption
  | succ n ih => exact dirichlet_contDiffOn_dirD hU ih 1

/-- Interior mixed symmetry puts the genuine limit derivatives in
the order used by the later normal recovery. -/
theorem dirichletTangentialDerivative_dirD_comm (hU : IsOpen U)
    {u : ℂ → ℂ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) u U) (n : ℕ) (w : ℂ) :
    EqOn (dirD (dirichletTangentialDerivative n u) w)
      (dirichletTangentialDerivative n (dirD u w)) U := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
      intro z hz
      change dirD (dirD (dirichletTangentialDerivative n u) 1) w z =
        dirD (dirichletTangentialDerivative n (dirD u w)) 1 z
      rw [dirichlet_dirD_comm hU (dirichletTangentialDerivative_contDiffOn hU hs n) hz 1 w]
      have heq : dirD (dirichletTangentialDerivative n u) w =ᶠ[𝓝 z]
          dirichletTangentialDerivative n (dirD u w) := by
        filter_upwards [hU.mem_nhds hz] with x hx
        grind
      exact congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) (heq.fderiv_eq )

/-- The real-energy version of Fatou for an actual measurable family.
This uses the true L² seminorm limit theorem and retains the actual
limit function as the representative. -/
theorem dirichlet_memLp_of_energy_limit {f : ℝ → ℂ → ℂ} {g : ℂ → ℂ}
    {ε E : ℝ} (hε : 0 < ε)
    (hm : ∀ h ∈ Ioo 0 ε, MemLp (f h) 2 μ)
    (he : ∀ h ∈ Ioo 0 ε, (∫ z, ‖f h z‖ ^ 2 ∂μ) ≤ E)
    (hf : ∀ h : ℝ, AEStronglyMeasurable (f h) μ)
    (hg : AEStronglyMeasurable g μ)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun h  => f h z) (𝓝[>] 0) (𝓝 (g z))) :
    MemLp g 2 μ := by
  have hbound : ∀ᶠ h : ℝ in 𝓝[>] 0,
      eLpNorm (f h) 2 μ ≤ ENNReal.ofReal (Real.sqrt E) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with h hh hhε
    have hhI : h ∈ Ioo 0 ε := ⟨hh, hhε⟩
    apply (ENNReal.toReal_le_toReal (hm h hhI).eLpNorm_ne_top (by simp)).mp
    rw [dirichlet_eLpNorm_toReal_eq_sqrt_energy (hm h hhI),
      ENNReal.toReal_ofReal (Real.sqrt_nonneg E)]
    exact Real.sqrt_le_sqrt (he h hhI)
  exact lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto hbound hf hg hlim) (by simp)

/-- The proved higher quotient energies and the genuine smooth
interior quotient limit give all tangential derivatives of both
coordinate gradients in L² on a smaller actual half box. -/
theorem exists_dirichlet_halfBox_higher_tangential_gradient_memLp
    (hA : 0 < A) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    {u G : ℂ → ℂ} (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u x = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiff ℝ (⊤ : ℕ∞) G) (n : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ j : ℕ, j ≤ n → ∀ i : Fin 2,
        MemLp (dirichletTangentialDerivative j (dirD u (coordDir i))) 2
          (volume.restrict (smoothDirichletHalfBox ρ ρ)) := by
  obtain ⟨ρ, ε₀, E, hρ, hρA, hρb, hε₀, _, henergy⟩ :=
    exists_dirichlet_halfBox_higher_difference_gradient_energy
      hA hb hf hLip hc hs hz hm hg hstrong hGs n
  let W := smoothDirichletHalfBox ρ ρ
  let U := smoothDirichletHalfBox A b
  let μ := volume.restrict W
  let ε := min ε₀ ((A - ρ) / (n + 1))
  have hε : 0 < ε := lt_min hε₀ (div_pos (by linarith) (by positivity))
  have hWU : W ⊆ U := fun z hz' =>
    ⟨hz'.1.trans (by linarith), hz'.2.1, hz'.2.2.trans hρb⟩
  refine ⟨ρ, hρ, hρA, hρb, ?_⟩
  intro j hj i
  let F  := fun h => dirD (dirichletTangentialDifferenceIter h j u) (coordDir i)
  have hstep (h : ℝ) (hh : h ∈ Ioo 0 ε) :
      h ∈ Ioo 0 ε₀ ∧ ρ + j * |h| ≤ A := by
    have hh' := (lt_div_iff₀ (by positivity)).mp (hh.2.trans_le (min_le_right _ _))
    have hj' : (j : ℝ) ≤ n := by simp_all
    have hjh  :=
      mul_le_mul_of_nonneg_right hj' hh.1.le
    rw [abs_of_pos hh.1]
    grind
  have hmem (h : ℝ) (hh : h ∈ Ioo 0 ε) (l : Fin 2) : MemLp
      (dirD (dirichletTangentialDifferenceIter h j u) (coordDir l)) 2 μ :=
    (dirichletTangentialDifferenceIter_gradient_memLp j (hstep h hh).2 hs (hg l)).mono_measure
      (Measure.restrict_mono_set volume
        (fun z hz' =>
          (show z ∈ smoothDirichletHalfBox ρ b from
            ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩)))
  have he (h : ℝ) (hh : h ∈ Ioo 0 ε) : (∫ z, ‖F h z‖ ^ 2 ∂μ) ≤ E := by
    have hle (z : ℂ) : ‖F h z‖ ^ 2 ≤
        dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z := by
      fin_cases i
      · exact le_add_of_nonneg_right (sq_nonneg _)
      · exact le_add_of_nonneg_left (sq_nonneg _)
    exact (integral_mono_ae ((hmem h hh i).integrable_norm_pow (by norm_num)) (dirichletGradientSq_integrable (hmem h hh)) (Eventually.of_forall hle)).trans
      (henergy h (hstep h hh).1 j hj)
  have hmeas (h : ℝ) : AEStronglyMeasurable (F h) μ :=
    (measurable_fderiv_apply_const ℝ (dirichletTangentialDifferenceIter h j u)
      (coordDir i)).aestronglyMeasurable
  exact dirichlet_memLp_of_energy_limit hε (fun h hh => hmem h hh i) he hmeas (((dirichletTangentialDerivative_contDiffOn
    (isOpen_smoothDirichletHalfBox A b)
    (dirichlet_contDiffOn_dirD (isOpen_smoothDirichletHalfBox A b) hs (coordDir i)) j).continuousOn.aestronglyMeasurable (isOpen_smoothDirichletHalfBox A b).measurableSet).mono_measure (Measure.restrict_mono_set volume hWU)) (by
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox ρ ρ).measurableSet]
      with z hzW
    exact (dirichletTangentialDifferenceIter_tendsto_of_contDiffOn
      (isOpen_smoothDirichletHalfBox A b)
      (dirichlet_contDiffOn_dirD (isOpen_smoothDirichletHalfBox A b) hs (coordDir i)) j (hWU hzW)).congr' (by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with h hh hhε
      exact (dirichletTangentialDifferenceIter_dirD j (hstep h ⟨hh, hhε⟩).2 hs
        (⟨hzW.1, hzW.2.1, hzW.2.2.trans hρb⟩) (coordDir i)).symm))

/-- Both the value and the first normal derivative of every actual
horizontal derivative have genuine L² representatives. -/
theorem exists_dirichlet_halfBox_higher_tangential_memLp
    (hA : 0 < A) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    {u G : ℂ → ℂ} (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u x = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiff ℝ (⊤ : ℕ∞) G) (n : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ j : ℕ, j ≤ n →
        MemLp (dirichletTangentialDerivative j u) 2
          (volume.restrict (smoothDirichletHalfBox ρ ρ)) ∧
        MemLp (dirD (dirichletTangentialDerivative j u) Complex.I) 2
          (volume.restrict (smoothDirichletHalfBox ρ ρ)) := by
  obtain ⟨ρ, hρ, hρA, hρb, hd⟩ :=
    exists_dirichlet_halfBox_higher_tangential_gradient_memLp
      hA hb hf hLip hc hs hz hm hg hstrong hGs n
  let W := smoothDirichletHalfBox ρ ρ
  have hWU : W ⊆ smoothDirichletHalfBox A b := fun z hz' =>
    ⟨hz'.1.trans (by linarith), hz'.2.1, hz'.2.2.trans hρb⟩
  refine ⟨ρ, hρ, hρA, hρb, ?_⟩
  intro j hj
  constructor
  · cases j with
    | zero => exact hm.mono_measure (Measure.restrict_mono_set volume hWU)
    | succ j =>
        simpa only [coordDir, Matrix.cons_val_zero, dirichletTangentialDerivative_succ_right] using hd j (by omega) 0
  · have hdy : MemLp (dirichletTangentialDerivative j (dirD u Complex.I)) 2
        (volume.restrict W) := by
      simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hd j hj 1
    apply hdy.ae_eq
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox ρ ρ).measurableSet]
      with z hzW
    exact (dirichletTangentialDerivative_dirD_comm (isOpen_smoothDirichletHalfBox A b)
      hs j Complex.I (hWU hzW)).symm

end PolyaNeumann

end
