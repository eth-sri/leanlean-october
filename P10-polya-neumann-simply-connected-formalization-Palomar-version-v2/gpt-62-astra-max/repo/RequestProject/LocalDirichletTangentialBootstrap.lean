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

section

variable (v : ℂ → ℂ) (z : ℂ)
include v z

/-- The actual two-coordinate gradient energy density. -/
def dirichletGradientSq : ℝ :=
  ‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2

theorem dirichletGradientSq_nonneg :
    0 ≤ dirichletGradientSq v z :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

end

theorem dirichletGradientSq_integrable {μ : Measure ℂ} {v : ℂ → ℂ}
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2 μ) :
    Integrable (dirichletGradientSq v) μ := by
  have hx := hg 0
  have hy := hg 1
  exact (hx.norm.integrable_sq).add
    (hy.norm.integrable_sq)

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
    (hf : ContDiff ℝ ∞ f) {K : NNReal} (hLip : LipschitzWith K f)
    (s : ℝ → ℝ) (v Q : ℝ → ℂ → ℂ) (C : ℝ → Fin 2 → ℂ → ℂ)
    (hvc : ∀ h ∈ Ioo 0 ε,
      ContinuousOn (v h) (smoothDirichletClosedHalfBox a b))
    (hvs : ∀ h ∈ Ioo 0 ε,
      ContDiffOn ℝ ∞ (v h) (smoothDirichletHalfBox a b))
    (hvz : ∀ h ∈ Ioo 0 ε, ∀ x : ℝ, |x| < a → v h (x : ℂ) = 0)
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
  let M := 2 * (1 + (K : ℝ) ^ 2)
  let E := 2 * M * (EQ + (4 * M + 2 * B ^ 2) * EC +
    (32 * B ^ 2 * M ^ 3 + 2) * Ev)
  
  
  refine ⟨r / 2, E, by linarith, by linarith, by linarith, (by dsimp [E]; positivity), ?_⟩
  intro h hh
  have hFm (i : Fin 2)  :=
    dirichletShiftedFlux_memLp hf hLip (s h) (hvg h hh) i
  have henergy := dirichlet_localized_boundary_energy_bound hb (by positivity) hB η
    hηsupp hη hηgrad (hvc h hh) (hvs h hh) (hvz h hh) (hvm h hh)
    (hvg h hh) hFm (hCm h hh) (hQm h hh)
    (fun z _ => dirichletShiftedFlux_coercive hLip (s h) (v h) z)
    (fun z _ => dirichletShiftedFlux_norm_sum_bound hLip (s h) (v h) z)
    (hweak h hh)
  have hJbound : (∫ z in V, ‖η z‖ ^ 2 * dirichletGradientSq (v h) z) ≤ E := by
    
    have hd := (div_le_iff₀ (show 0 < 2 * M by positivity)).mp (henergy.trans (add_le_add
      (add_le_add (hQenergy h hh) (mul_le_mul_of_nonneg_left (hCenergy h hh)
        (show 0 ≤ 4 * M + 2 * B ^ 2 by positivity)))
      (mul_le_mul_of_nonneg_left (hvenergy h hh)
        (show 0 ≤ 32 * B ^ 2 * M ^ 3 + 2 by positivity))))
    calc
      _ ≤
          _ := hd
      _ = E := by ring
  let W := smoothDirichletHalfBox (r / 2) (r / 2)
  have hWsub : W ⊆ V := fun z hzW =>
    ⟨hzW.1.trans (by linarith), hzW.2.1, hzW.2.2.trans (by linarith)⟩
  
  
  have hJi : IntegrableOn (fun z => ‖η z‖ ^ 2 * dirichletGradientSq (v h) z) V := by
    apply (((dirichlet_localized_memLp η
      (show MemLp (dirD (v h) 1) 2 (volume.restrict V) by
        exact hvg h hh 0)).integrable_norm_pow (by positivity)).add
      ((dirichlet_localized_memLp η
        (show MemLp (dirD (v h) Complex.I) 2 (volume.restrict V) by
          exact hvg h hh 1)).integrable_norm_pow (by positivity))).congr
    filter_upwards with z
    change ‖η z * dirD (v h) 1 z‖ ^ 2 + ‖η z * dirD (v h) Complex.I z‖ ^ 2 =
      ‖η z‖ ^ 2 * dirichletGradientSq (v h) z
    simp [dirichletGradientSq, norm_mul, mul_pow]
    ring
  have hW : (∫ z in W, dirichletGradientSq (v h) z) =
      ∫ z in W, ‖η z‖ ^ 2 * dirichletGradientSq (v h) z := by
    apply setIntegral_congr_fun (isOpen_smoothDirichletHalfBox _ _).measurableSet
    intro z hzW
    simp [*]
  rw [hW]
  exact (setIntegral_mono_set hJi
    (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
      (dirichletGradientSq_nonneg (v h) z)) hWsub.eventuallyLE).trans hJbound

/-- Equality on the larger genuine box is preserved by every finite
quotient on the smaller box, with all translations counted. -/
theorem dirichletTangentialDifferenceIter_congr_on_halfBox {A a b h : ℝ}
    (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A) {u v : ℂ → ℂ}
    (heq : EqOn u v (smoothDirichletHalfBox A b)) {z : ℂ}
    (hz : z ∈ smoothDirichletHalfBox a b) :
    dirichletTangentialDifferenceIter h k u z =
      dirichletTangentialDifferenceIter h k v z := by
  induction k generalizing a z with
  | zero =>
      
      refine heq ⟨hz.1.trans_le ?_, hz.2⟩
      simpa using hmargin
  | succ k ih =>
      have hm : (a + |h|) + k * |h| ≤ A := by
        grind
      
      have hzh : z + h ∈ smoothDirichletHalfBox (a + |h|) b := by
        have hx := (abs_add_le z.re h).trans_lt (add_lt_add_of_lt_of_le hz.1 le_rfl)
        simpa [smoothDirichletHalfBox] using (show |z.re + h| < a + |h| ∧ 0 < z.im ∧ z.im < b from ⟨hx, hz.2⟩)
      change (_ - _) / (h : ℂ) = (_ - _) / (h : ℂ)
      rw [ih hm hzh, ih hm (⟨hz.1.trans_le (le_add_of_nonneg_right (abs_nonneg h)), hz.2⟩)]

/-- The genuine kth quotient of the physical graph equation gives
the higher weak equation, with the exact graph commutator. -/
theorem dirichletTangentialDifferenceIter_weak_equation {A a b h : ℝ}
    (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {u G : ℂ → ℂ}
    (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    {φ : ℂ → ℂ} (hφ : TestFunction (smoothDirichletHalfBox a b) φ) :
    (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
      (dirichletShiftedFlux f ((k : ℝ) * h)
          (dirichletTangentialDifferenceIter h k u) i z +
        dirichletHigherCoefficientDifferenceFlux f h k u i z) *
          dirD φ (coordDir i) z) =
      ∫ z in smoothDirichletHalfBox a b,
        dirichletTangentialDifferenceIter h k G z * φ z := by
  
  let V := smoothDirichletHalfBox a b
  let H  := fun i =>
    dirichletTangentialDifferenceIter h k (dirichletFlattenedFlux f u i)
  
  have hV := isOpen_smoothDirichletHalfBox a b
  have hflux (i : Fin 2)  :=
    dirichletFlattenedFlux_contDiffOn (isOpen_smoothDirichletHalfBox A b) hf hs i
  have hH (i : Fin 2)  :=
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
    calc _ = dirichletTangentialDifferenceIter h k (dirichletFlattenedDivergence f u) z :=
            (congrFun ((dirichletTangentialDifferenceIter h k).map_add _ _) z).symm
         _ = dirichletTangentialDifferenceIter h k (-G) z :=
            dirichletTangentialDifferenceIter_congr_on_halfBox k hmargin hstrong hz
         _ = _ := congrFun (map_neg (dirichletTangentialDifferenceIter h k) G) z
  have hI (i : Fin 2)  :=
    dirichlet_local_smooth_mul_test_integrable hV (hH i) (hφ.dirD (coordDir i))
  have hDI (i : Fin 2)  :=
    dirichlet_local_smooth_mul_test_integrable hV
      (dirichlet_contDiffOn_dirD hV (hH i) (coordDir i)) hφ
  have heq : (∫ z in V, ∑ i : Fin 2, H i z * dirD φ (coordDir i) z) =
      -(∫ z in V, (∑ i : Fin 2, dirD (H i) (coordDir i) z) * φ z) := by
    rw [integral_finset_sum _ (fun i _ => hI i)]
    have hibp (i : Fin 2) :=
      dirichlet_local_smooth_field_test_eq_neg_dirD hV (hH i) hφ i
    have hsum : (∑ i : Fin 2, ∫ z in V, H i z * dirD φ (coordDir i) z) =
        ∑ i : Fin 2, -(∫ z in V, dirD (H i) (coordDir i) z * φ z) := by
      exact Finset.sum_congr rfl (fun i _ => hibp i)
    rw [hsum, Finset.sum_neg_distrib, ← integral_finset_sum _ (fun i _ => hDI i)]
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
  change -((∑ i : Fin 2, dirD (H i) (coordDir i) z) * φ z) =
    dirichletTangentialDifferenceIter h k G z * φ z
  rw [hdiv z hz]
  ring

/-- Genuine uniform pointwise bounds for a smooth forcing give its
uniform L² energy on a finite half box. -/
theorem dirichlet_bounded_family_sq_energy {a b ε C : ℝ}
    {Q : ℝ → ℂ → ℂ} (hc : ∀ h : ℝ, Continuous (Q h))
    (hbound : ∀ h ∈ Ioo 0 ε, ∀ z ∈ smoothDirichletHalfBox a b, ‖Q h z‖ ≤ C) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ h ∈ Ioo 0 ε,
      MemLp (Q h) 2 (volume.restrict (smoothDirichletHalfBox a b)) ∧
      (∫ z in smoothDirichletHalfBox a b, ‖Q h z‖ ^ 2) ≤ E := by
  
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  letI : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using
    (dirichlet_halfBox_isBounded (a := a) (b := b)).measure_lt_top⟩
  
  refine ⟨(∫ z : ℂ, C ^ 2 ∂μ), (by positivity), ?_⟩
  intro h hh
  have hm : MemLp (Q h) 2 μ := by
    apply MemLp.of_bound (by fun_prop) C
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    exact hbound h hh z hz
  refine ⟨hm, ?_⟩
  apply integral_mono_ae (hm.norm.integrable_sq)
    (integrable_const _)
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  grind [pow_le_pow_left₀]

theorem dirichletTangentialDifferenceIter_measurable {v : ℂ → ℂ}
    (hv : Measurable v) (h : ℝ) (k : ℕ) :
    Measurable (dirichletTangentialDifferenceIter h k v) := by
  induction k with
  | zero => exact hv
  | succ k ih =>
      exact ((ih.comp (measurable_id.add_const (h : ℂ))).sub ih).div_const (h : ℂ)

theorem dirichletHigherCoefficientCommutator_measurable {a v : ℂ → ℂ}
    (ha : Measurable a) (hv : Measurable v) (h : ℝ) (k : ℕ) :
    Measurable (dirichletHigherCoefficientCommutator h k a v) :=
  (dirichletTangentialDifferenceIter_measurable (ha.mul hv) h k).sub
    ((ha.comp (measurable_id.add_const (((k : ℝ) * h : ℝ) : ℂ))).mul
      (dirichletTangentialDifferenceIter_measurable hv h k))

theorem dirichletHigherCoefficientDifferenceFlux_measurable {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (h : ℝ) (k : ℕ) (u : ℂ → ℂ) (i : Fin 2) :
    Measurable (dirichletHigherCoefficientDifferenceFlux f h k u i) := by
  have hd := (dirichletGraphSlope_contDiff hf).continuous.measurable
  have hx := measurable_fderiv_apply_const ℝ u 1
  have hy := measurable_fderiv_apply_const ℝ u Complex.I
  
  
  have hsy := dirichletHigherCoefficientCommutator_measurable
    ((measurable_const : Measurable (fun _ : ℂ => (1 : ℂ))).add
      (hd.pow_const 2)) hy h k
  fin_cases i
  · exact (dirichletHigherCoefficientCommutator_measurable hd hy h k).neg
  · exact (dirichletHigherCoefficientCommutator_measurable hd hx h k).neg.add hsy

/-- The genuine graph commutator is controlled by lower gradient
quotients. The squared finite-sum estimate includes all binomial
weights; no translated input energy is used. -/
theorem dirichletHigherCoefficientDifferenceFlux_sq_bound
    {A a b h M : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {f : ℝ → ℝ} {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    (hbound : ∀ (v : ℂ → ℂ) (z : ℂ), z ∈ smoothDirichletClosedHalfBox a b →
      (‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) v z‖ ≤
        M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
          ‖dirichletTangentialDifferenceIter h j v z‖) ∧
      (‖dirichletHigherCoefficientCommutator h k
          (fun w => 1 + dirichletGraphSlope f w ^ 2) v z‖ ≤
        M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
          ‖dirichletTangentialDifferenceIter h j v z‖))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) :
    ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ^ 2 +
      ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ^ 2 ≤
      (3 * M ^ 2 * ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2) *
        ∑ j ∈ Finset.range k,
          dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z := by
  let vx  := fun j => ‖dirD (dirichletTangentialDifferenceIter h j u) 1 z‖
  let vy  := fun j => ‖dirD (dirichletTangentialDifferenceIter h j u) Complex.I z‖
  let Sx := ∑ j ∈ Finset.range k, (k.choose j) * vx j
  let Sy := ∑ j ∈ Finset.range k, (k.choose j) * vy j
  let P := ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2
  
  
  have hdir (j : ℕ) (hj : j ∈ Finset.range k) (w : ℂ) :
      dirichletTangentialDifferenceIter h j (dirD u w) z =
        dirD (dirichletTangentialDifferenceIter h j u) w z := by
    have hjk  := (Finset.mem_range.mp hj).le
    
    refine (dirichletTangentialDifferenceIter_dirD j ?_ hs hz w).symm
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hjk) (abs_nonneg h))).trans hmargin
  have hclosed : z ∈ smoothDirichletClosedHalfBox a b := ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  have hcx : ‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
      (dirD u 1) z‖ ≤ M * Sx := by
    have hb := (hbound (dirD u 1) z hclosed).1
    exact hb.trans_eq (congrArg (fun t => M * t) (Finset.sum_congr rfl
      (fun j hj => by rw [hdir j hj])))
  have hcy : ‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
      (dirD u Complex.I) z‖ ≤ M * Sy := by
    
    exact ((hbound (dirD u Complex.I) z hclosed).1).trans_eq (congrArg (fun t => M * t) (Finset.sum_congr rfl
      (fun j hj => by rw [hdir j hj])))
  have hsy : ‖dirichletHigherCoefficientCommutator h k
      (fun w => 1 + dirichletGraphSlope f w ^ 2) (dirD u Complex.I) z‖ ≤ M * Sy := by
    have hb := (hbound (dirD u Complex.I) z hclosed).2
    exact hb.trans_eq (congrArg (fun t => M * t) (Finset.sum_congr rfl
      (fun j hj => by rw [hdir j hj])))
  have h0 : ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ≤ M * Sy := by
    simpa only [dirichletHigherCoefficientDifferenceFlux, Matrix.cons_val_zero, norm_neg] using hcy
  have h1 : ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ≤ M * (Sx + Sy) := by
    
    exact (norm_add_le _ _).trans (by rw [norm_neg]; linarith)
  have hsx  :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k) (fun j => (k.choose j : ℝ)) vx
  have hsy'  :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k) (fun j => (k.choose j : ℝ)) vy
  have hsum : Sx ^ 2 + Sy ^ 2 ≤ P *
      ∑ j ∈ Finset.range k, dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z := by
    simpa only [dirichletGradientSq, Finset.sum_add_distrib, vx, vy, mul_add] using
      add_le_add hsx hsy'
  have hc0 := pow_le_pow_left₀ (norm_nonneg _) h0 2
  have hc1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hab : Sy ^ 2 + (Sx + Sy) ^ 2 ≤ 3 * (Sx ^ 2 + Sy ^ 2) := by
    nlinarith [sq_nonneg (Sx - Sy), sq_nonneg Sx]
  
  have hmain : ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ^ 2 +
      ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ^ 2 ≤
        3 * M ^ 2 * (Sx ^ 2 + Sy ^ 2) := by nlinarith
  exact hmain.trans (by
    have hp := mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ 3 * M ^ 2 by positivity)
    simpa [mul_assoc] using hp)

/-- Fixed-step commutators are honest L² functions. Their measurable
representatives are the actual coefficient products and derivatives. -/
theorem dirichletHigherCoefficientDifferenceFlux_memLp
    {A a b h M : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {u : ℂ → ℂ} (hM : 0 ≤ M)
    (hbound : ∀ (v : ℂ → ℂ) (z : ℂ), z ∈ smoothDirichletClosedHalfBox a b →
      (‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) v z‖ ≤
        M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
          ‖dirichletTangentialDifferenceIter h j v z‖) ∧
      (‖dirichletHigherCoefficientCommutator h k
          (fun w => 1 + dirichletGraphSlope f w ^ 2) v z‖ ≤
        M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
          ‖dirichletTangentialDifferenceIter h j v z‖))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b))) (i : Fin 2) :
    MemLp (dirichletHigherCoefficientDifferenceFlux f h k u i) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let vx  := fun j z => ‖dirichletTangentialDifferenceIter h j (dirD u 1) z‖
  let vy  := fun j z => ‖dirichletTangentialDifferenceIter h j (dirD u Complex.I) z‖
  let B  := fun z => M * ∑ j ∈ Finset.range k,
    (k.choose j) * (vx j z + vy j z)
  
  
  have hBm : MemLp B 2 μ := by
    apply MemLp.const_mul _ M
    apply memLp_finset_sum
    intro j hj
    
    have hm : a + (j : ℝ) * |h| ≤ A :=
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast ((Finset.mem_range.mp hj).le))
        (abs_nonneg h))).trans hmargin
    exact ((dirichletTangentialDifferenceIter_memLp j hm (hg 0)).norm.add
      (dirichletTangentialDifferenceIter_memLp j hm (hg 1)).norm).const_mul (k.choose j)
  apply hBm.mono' (dirichletHigherCoefficientDifferenceFlux_measurable hf h k u i).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  have hz' : z ∈ smoothDirichletClosedHalfBox a b := ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  let Sx := ∑ j ∈ Finset.range k, (k.choose j) * vx j z
  let Sy := ∑ j ∈ Finset.range k, (k.choose j) * vy j z
  have hSx : 0 ≤ Sx := Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hBS : B z = M * (Sx + Sy) := by
    simp [B, Sx, Sy, mul_add, Finset.sum_add_distrib]
  
  
  
  fin_cases i
  · change ‖-dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
      (dirD u Complex.I) z‖ ≤ B z
    rw [norm_neg]
    calc
      _ ≤ _ := ((hbound (dirD u Complex.I) z hz').1)
      _ ≤ M * (Sx + Sy) := by nlinarith
      _ = _ := hBS.symm
  · change ‖-dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
      (dirD u 1) z + dirichletHigherCoefficientCommutator h k
        (fun w => 1 + dirichletGraphSlope f w ^ 2) (dirD u Complex.I) z‖ ≤ B z
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ M * Sx + M * Sy := by rw [norm_neg]; exact add_le_add ((hbound (dirD u 1) z hz').1) ((hbound (dirD u Complex.I) z hz').2)
      _ = _ := by linarith

/-- Integration of the exact squared commutator bound converts
simultaneous lower quotient energies into the next data energy. -/
theorem dirichletHigherCoefficientDifferenceFlux_energy_le
    {A a b h M E : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b)) (hM : 0 ≤ M)
    (hbound : ∀ (v : ℂ → ℂ) (z : ℂ), z ∈ smoothDirichletClosedHalfBox a b →
      (‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) v z‖ ≤
        M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
          ‖dirichletTangentialDifferenceIter h j v z‖) ∧
      (‖dirichletHigherCoefficientCommutator h k
          (fun w => 1 + dirichletGraphSlope f w ^ 2) v z‖ ≤
        M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
          ‖dirichletTangentialDifferenceIter h j v z‖))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (henergy : ∀ j ∈ Finset.range k,
      (∫ z in smoothDirichletHalfBox a b,
        dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z) ≤ E) :
    (∫ z in smoothDirichletHalfBox a b,
      ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ^ 2 +
        ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ^ 2) ≤
      (3 * M ^ 2 * ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2) * ((k : ℝ) * E) := by
  let V := smoothDirichletHalfBox a b
  let D := 3 * M ^ 2 * ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2
  have hD : 0 ≤ D := by
    exact (by positivity)
  have hCm (i : Fin 2) :=
    dirichletHigherCoefficientDifferenceFlux_memLp k hmargin hf hM hbound hg i
  have hCi := ((hCm 0).norm.integrable_sq).add
    ((hCm 1).norm.integrable_sq)
  have hgi (j : ℕ) (hj : j ∈ Finset.range k) : IntegrableOn
      (dirichletGradientSq (dirichletTangentialDifferenceIter h j u)) V := by
    have hjk  := (Finset.mem_range.mp hj).le
    
    exact dirichletGradientSq_integrable
      (fun i => dirichletTangentialDifferenceIter_gradient_memLp j ((add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hjk)
        (abs_nonneg h))).trans hmargin) hs (hg i))
  
  have hbnd : (∫ z in V,
      ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ^ 2 +
        ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ^ 2) ≤
      ∫ z in V, D * ∑ j ∈ Finset.range k,
        dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z := by
    apply integral_mono_ae hCi ((integrable_finset_sum _ (hgi)).const_mul D)
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    exact dirichletHigherCoefficientDifferenceFlux_sq_bound k hmargin hs hbound hz
  rw [integral_const_mul, integral_finset_sum _ hgi] at hbnd
  exact hbnd.trans (mul_le_mul_of_nonneg_left
    (by simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j hj => henergy j hj)) hD)

/-- Actual induction of the higher gradient energies. At every
finite order the tested functions are finite quotients of the original
zero-boundary function. Smooth coefficients and forcing supply their
own compact derivative bounds. No higher estimate is a premise. -/
theorem exists_dirichlet_halfBox_higher_difference_gradient_energy
    {A b : ℝ} (hA : 0 < A) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {K : NNReal} (hLip : LipschitzWith K f)
    {u G : ℂ → ℂ} (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiff ℝ ∞ G) (n : ℕ) :
    ∃ ρ ε E : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧ 0 < ε ∧ 0 ≤ E ∧
      DirichletDifferenceGradientBound n u ρ ρ ε E := by
  let U := smoothDirichletHalfBox A b
  induction n with
  | zero =>
      let ρ := min A b / 4
      have hρ : 0 < ρ := div_pos (lt_min hA hb) (by norm_num)
      have hρA : ρ < A / 2 := by
        dsimp only [ρ]
        linarith [min_le_left A b]
      have hρb : ρ < b := by
        dsimp only [ρ]
        linarith [min_le_right A b]
      let E := ∫ z in U, dirichletGradientSq u z
      have hE : 0 ≤ E := integral_nonneg (dirichletGradientSq_nonneg u)
      have hsub : smoothDirichletHalfBox ρ ρ ⊆ U := fun z hz' =>
        ⟨hz'.1.trans (by linarith), hz'.2.1, hz'.2.2.trans hρb⟩
      refine ⟨ρ, 1, E, hρ, hρA, hρb, by norm_num, hE, ?_⟩
      intro h hh j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      exact setIntegral_mono_set (dirichletGradientSq_integrable hg)
        (Eventually.of_forall (dirichletGradientSq_nonneg u)) hsub.eventuallyLE
  | succ n ih =>
      obtain ⟨ρ, ε₀, E₀, hρ, hρA, hρb, hε₀, hE₀, hprev⟩ := ih
      let k := n + 1
      let W := smoothDirichletHalfBox ρ ρ
      let V := smoothDirichletHalfBox (ρ / 2) ρ
      let ε := min ε₀ (ρ / (4 * ((k : ℝ) + 1)))
      have hε : 0 < ε := lt_min hε₀ (div_pos hρ (by positivity))
      have hVW : V ⊆ W := fun z hz' => ⟨hz'.1.trans (by linarith), hz'.2⟩
      have hsteps (h : ℝ) (hh : h ∈ Ioo 0 ε) :
          h ∈ Ioo 0 ε₀ ∧ ρ / 2 + (k : ℝ) * |h| ≤ ρ ∧
            ρ + (k : ℝ) * |h| ≤ A ∧ ρ / 2 + h < ρ := by
        have hh₀ := hh.2.trans_le (min_le_left _ _)
        have hhs := hh.2.trans_le (min_le_right _ _)
        have hkh : ((k : ℝ) + 1) * h < ρ / 4 := by
          have hh' := (lt_div_iff₀ (show 0 < 4 * ((k : ℝ) + 1) by positivity)).mp hhs
          nlinarith
        
        rw [abs_of_pos hh.1]
        refine ⟨⟨hh.1, hh₀⟩, ?_, ?_, ?_⟩ <;>
          nlinarith
      have hmargin (h : ℝ) (hh : h ∈ Ioo 0 ε) :
          ρ / 2 + (k : ℝ) * |h| ≤ A :=
        ((hsteps h hh).2.1).trans (by linarith)
      have hpositiveMargin (h : ℝ) (hh : h ∈ Ioo 0 ε) :
          ρ / 2 + (k : ℝ) * h ≤ ρ := by
        have hm := (hsteps h hh).2.1
        rwa [abs_of_pos hh.1] at hm
      have hsmallgrad (h : ℝ) (hh : h ∈ Ioo 0 ε) (j : ℕ) (hj : j ≤ k)
          (i : Fin 2) : MemLp
            (dirD (dirichletTangentialDifferenceIter h j u) (coordDir i)) 2
            (volume.restrict W) := by
        have hmj : ρ + (j : ℝ) * |h| ≤ A :=
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right
            (by exact_mod_cast hj) (abs_nonneg h))).trans (hsteps h hh).2.2.1
        have hmj' := dirichletTangentialDifferenceIter_gradient_memLp j hmj hs (hg i)
        exact hmj'.mono_measure (Measure.restrict_mono_set volume
          (show W ⊆ smoothDirichletHalfBox ρ b from
            fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩))
      have hlower (h : ℝ) (hh : h ∈ Ioo 0 ε) (j : ℕ) (hj : j ≤ n) :
          (∫ z in V, dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z) ≤ E₀ := by
        have hi := dirichletGradientSq_integrable
          (hsmallgrad h hh j (hj.trans (Nat.le_succ n)))
        exact (setIntegral_mono_set hi
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
      have hvs (h : ℝ) (hh : h ∈ Ioo 0 ε) : ContDiffOn ℝ ∞ (v h) V :=
        (dirichletTangentialDifferenceIter_contDiffOn k (hmargin h hh) hs).mono
          (fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩)
      have hvz (h : ℝ) (hh : h ∈ Ioo 0 ε) (x : ℝ) (hx : |x| < ρ / 2)  :=
        dirichletTangentialDifferenceIter_zero_bottom k (hmargin h hh) hz hx
      have hvm (h : ℝ) (hh : h ∈ Ioo 0 ε)  :=
        (dirichletTangentialDifferenceIter_memLp k (hmargin h hh) hm).mono_measure
          (Measure.restrict_mono_set volume
            (show V ⊆ smoothDirichletHalfBox (ρ / 2) b from
              fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩))
      have hvg (h : ℝ) (hh : h ∈ Ioo 0 ε) (i : Fin 2)  :=
        (hsmallgrad h hh k le_rfl i).mono_measure (Measure.restrict_mono_set volume hVW)
      have hvenergy (h : ℝ) (hh : h ∈ Ioo 0 ε) :
          (∫ z in V, ‖v h z‖ ^ 2) ≤ E₀ := by
        have hnmargin : ρ + (n : ℝ) * |h| ≤ A :=
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right
            (by exact_mod_cast (Nat.le_succ n)) (abs_nonneg h))).trans (hsteps h hh).2.2.1
        have hnm  :=
          (dirichletTangentialDifferenceIter_memLp n hnmargin hm).mono_measure
          (Measure.restrict_mono_set volume
            (show W ⊆ smoothDirichletHalfBox ρ b from
              fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩))
        have hns : ContDiffOn ℝ ∞ (dirichletTangentialDifferenceIter h n u) W :=
          (dirichletTangentialDifferenceIter_contDiffOn n hnmargin hs).mono
          (fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩)
        have hnx := hsmallgrad h hh n (Nat.le_succ n) 0
        have hv' := dirichlet_halfBox_tangential_difference_energy_le
          hh.1 (hsteps h hh).2.2.2.le hns hnm hnx
        have hi := dirichletGradientSq_integrable
          (hsmallgrad h hh n (Nat.le_succ n))
        have hnorm  :=
          integral_mono_ae (hnx.norm.integrable_sq) hi
            (Eventually.of_forall fun z => le_add_of_nonneg_right (sq_nonneg _))
        exact hv'.trans (hnorm.trans (hprev h (hsteps h hh).1 n le_rfl))
      obtain ⟨MQ, hQbound⟩ := exists_dirichletTangentialDifferenceIter_bound hGs ρ ρ k
      obtain ⟨EQ, hEQ, hQdata⟩ := dirichlet_bounded_family_sq_energy
        (fun h => (dirichletTangentialDifferenceIter_contDiff hGs h k).continuous)
        (fun h hh z hz' => hQbound.2 (ρ / 2) h hh.1
          (hpositiveMargin h hh) z
          ⟨hz'.1.le, hz'.2.1.le, hz'.2.2.le⟩)
      obtain ⟨MC, hMC, hCbound⟩ := exists_dirichletGraphHigherCommutator_bound hf ρ ρ k
      let D := 3 * MC ^ 2 * ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2
      let EC := D * ((k : ℝ) * E₀)
      have hEC : 0 ≤ EC := by
        dsimp [EC, D]
        exact mul_nonneg (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) hE₀)
      have hCb (h : ℝ) (hh : h ∈ Ioo 0 ε) :=
        hCbound (ρ / 2) h hh.1
          (hpositiveMargin h hh)
      have hug (i : Fin 2)  :=
        (hg i).mono_measure (Measure.restrict_mono_set volume
          (show smoothDirichletHalfBox A ρ ⊆ smoothDirichletHalfBox A b from
            fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩))
      have hus : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A ρ) :=
        hs.mono (fun z hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩)
      have hCm (h : ℝ) (hh : h ∈ Ioo 0 ε) (i : Fin 2)  :=
        dirichletHigherCoefficientDifferenceFlux_memLp k (hmargin h hh) hf hMC (hCb h hh) hug i
      have hCenergy (h : ℝ) (hh : h ∈ Ioo 0 ε)  :=
        dirichletHigherCoefficientDifferenceFlux_energy_le k (hmargin h hh) hf hus hMC
          (hCb h hh) hug (fun j hj => hlower h hh j (by
            exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      have hweak (h : ℝ) (hh : h ∈ Ioo 0 ε) (φ : ℂ → ℂ) (hφ : TestFunction V φ)  :=
        dirichletTangentialDifferenceIter_weak_equation k (hmargin h hh) hf hus
          (fun z hz' => hstrong z ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩) hφ
      obtain ⟨r, E₁, hr, hra, hrρ, hE₁, hnew⟩ := exists_dirichlet_family_gradient_energy
        (show 0 < ρ / 2 by linarith) hρ hf hLip (fun h => (k : ℝ) * h) v Q C
        hvc hvs hvz hvm hvg (fun h hh => (hQdata h hh).1) hCm hE₀ hEQ hEC
        hvenergy (fun h hh => (hQdata h hh).2) hCenergy hweak
      let E := max E₀ E₁
      have hrW : smoothDirichletHalfBox r r ⊆ W := fun z hz' =>
        ⟨hz'.1.trans hrρ, hz'.2.1, hz'.2.2.trans hrρ⟩
      refine ⟨r, ε, E, hr, by linarith, hrρ.trans hρb, hε,
        hE₀.trans (le_max_left _ _), ?_⟩
      intro h hh j hj
      rcases Nat.eq_or_lt_of_le hj with hjk | hjk
      · rw [hjk]
        exact (hnew h hh).trans (le_max_right _ _)
      · have hjn  := Nat.le_of_lt_succ hjk
        have hi := dirichletGradientSq_integrable (hsmallgrad h hh j (hjn.trans (Nat.le_succ n)))
        exact (setIntegral_mono_set hi
          (Eventually.of_forall (dirichletGradientSq_nonneg _)) hrW.eventuallyLE).trans
          ((hprev h (hsteps h hh).1 j hjn).trans (le_max_left _ _))

theorem dirichletTangentialDerivative_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hs : ContDiffOn ℝ ∞ u U) (n : ℕ) :
    ContDiffOn ℝ ∞ (dirichletTangentialDerivative n u) U := by
  induction n with
  | zero => exact hs
  | succ n ih => exact dirichlet_contDiffOn_dirD hU ih 1

/-- Interior mixed symmetry puts the genuine limit derivatives in
the order used by the later normal recovery. -/
theorem dirichletTangentialDerivative_dirD_comm {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hs : ContDiffOn ℝ ∞ u U) (n : ℕ) (w : ℂ) :
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
        exact ih hx
      exact congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) heq.fderiv_eq

/-- The real-energy version of Fatou for an actual measurable family.
This uses the true L² seminorm limit theorem and retains the actual
limit function as the representative. -/
theorem dirichlet_memLp_of_energy_limit {μ : Measure ℂ} {f : ℝ → ℂ → ℂ} {g : ℂ → ℂ}
    {ε E : ℝ} (hε : 0 < ε)
    (hm : ∀ h ∈ Ioo 0 ε, MemLp (f h) 2 μ)
    (he : ∀ h ∈ Ioo 0 ε, (∫ z, ‖f h z‖ ^ 2 ∂μ) ≤ E)
    (hf : ∀ h : ℝ, AEStronglyMeasurable (f h) μ)
    (hg : AEStronglyMeasurable g μ)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun h : ℝ => f h z) (𝓝[>] (0 : ℝ)) (𝓝 (g z))) :
    MemLp g 2 μ := by
  have hbound : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      eLpNorm (f h) 2 μ ≤ ENNReal.ofReal (Real.sqrt E) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with h hh hhε
    have hhI : h ∈ Ioo (0 : ℝ) ε := ⟨hh, hhε⟩
    apply (ENNReal.toReal_le_toReal (hm h hhI).eLpNorm_ne_top (by simp)).mp
    rw [toReal_eLpNorm, lpNorm_two_eq (hm h hhI),
      ENNReal.toReal_ofReal (Real.sqrt_nonneg E)]
    exact Real.sqrt_le_sqrt (he h hhI)
  exact lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto hbound hf hg hlim) (by simp)

/-- The proved higher quotient energies and the genuine smooth
interior quotient limit give all tangential derivatives of both
coordinate gradients in L² on a smaller actual half box. -/
theorem exists_dirichlet_halfBox_higher_tangential_gradient_memLp
    {A b : ℝ} (hA : 0 < A) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {K : NNReal} (hLip : LipschitzWith K f)
    {u G : ℂ → ℂ} (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiff ℝ ∞ G) (n : ℕ) :
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
  let g := dirichletTangentialDerivative j (dirD u (coordDir i))
  have hstep (h : ℝ) (hh : h ∈ Ioo 0 ε) :
      h ∈ Ioo 0 ε₀ ∧ ρ + j * |h| ≤ A := by
    
    have hhs := hh.2.trans_le (min_le_right _ _)
    have hh' := (lt_div_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).mp hhs
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    
    rw [abs_of_pos hh.1]
    refine ⟨⟨hh.1, (hh.2.trans_le (min_le_left _ _))⟩, ?_⟩
    nlinarith
  have hmem (h : ℝ) (hh : h ∈ Ioo 0 ε) (l : Fin 2)  :=
    (dirichletTangentialDifferenceIter_gradient_memLp j (hstep h hh).2 hs (hg l)).mono_measure
      (Measure.restrict_mono_set volume
        (fun z (hz' : z ∈ smoothDirichletHalfBox ρ ρ) =>
          (show z ∈ smoothDirichletHalfBox ρ b from
            ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩)))
  have he (h : ℝ) (hh : h ∈ Ioo 0 ε) : (∫ z, ‖F h z‖ ^ 2 ∂μ) ≤ E := by
    
    have hm' := (hmem h hh i).integrable_norm_pow (by positivity)
    have hle (z : ℂ) : ‖F h z‖ ^ 2 ≤
        dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z := by
      fin_cases i
      · exact le_add_of_nonneg_right (sq_nonneg _)
      · exact le_add_of_nonneg_left (sq_nonneg _)
    exact (integral_mono_ae hm' (dirichletGradientSq_integrable (hmem h hh)) (Eventually.of_forall hle)).trans
      (henergy h (hstep h hh).1 j hj)
  have hmeas (h : ℝ) : AEStronglyMeasurable (F h) μ :=
    (measurable_fderiv_apply_const ℝ (dirichletTangentialDifferenceIter h j u)
      (coordDir i)).aestronglyMeasurable
  have hgs := dirichletTangentialDerivative_contDiffOn
    (isOpen_smoothDirichletHalfBox A b)
    (dirichlet_contDiffOn_dirD (isOpen_smoothDirichletHalfBox A b) hs (coordDir i)) j
  
  have hgmeas  :=
    (hgs.continuousOn.aestronglyMeasurable (isOpen_smoothDirichletHalfBox A b).measurableSet).mono_measure (Measure.restrict_mono_set volume hWU)
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun h : ℝ => F h z) (𝓝[>] 0) (𝓝 (g z)) := by
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox ρ ρ).measurableSet]
      with z hzW
    have ht := dirichletTangentialDifferenceIter_tendsto_of_contDiffOn
      (isOpen_smoothDirichletHalfBox A b)
      (dirichlet_contDiffOn_dirD (isOpen_smoothDirichletHalfBox A b) hs (coordDir i)) j (hWU hzW)
    
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with h hh hhε
    exact (dirichletTangentialDifferenceIter_dirD j (hstep h ⟨hh, hhε⟩).2 hs
      (show z ∈ smoothDirichletHalfBox ρ b from
        ⟨hzW.1, hzW.2.1, hzW.2.2.trans hρb⟩) (coordDir i)).symm
  exact dirichlet_memLp_of_energy_limit hε (fun h hh => hmem h hh i) he hmeas hgmeas hlim

/-- Both the value and the first normal derivative of every actual
horizontal derivative have genuine L² representatives. -/
theorem exists_dirichlet_halfBox_higher_tangential_memLp
    {A b : ℝ} (hA : 0 < A) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {K : NNReal} (hLip : LipschitzWith K f)
    {u G : ℂ → ℂ} (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiff ℝ ∞ G) (n : ℕ) :
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
        
        simpa [coordDir, dirichletTangentialDerivative_succ_right] using hd j (by omega) 0
  · 
    apply (hd j hj 1).ae_eq
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox ρ ρ).measurableSet]
      with z hzW
    exact (dirichletTangentialDerivative_dirD_comm (isOpen_smoothDirichletHalfBox A b)
      hs j Complex.I (hWU hzW)).symm

end PolyaNeumann

end
