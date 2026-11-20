module

public import HypoellipticAleksandrov.Parabolic.SourceLocalHarnackScaling
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.SmoothApproximation
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ApproximationBounds

/-! # A Harnack link with bounded forcing

Approximate just the classical jet on the compact comparison box. The error in the source
is uniform there: neither the coefficient nor a weak solution needs to be mollified.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Set MeasureTheory Filter KrylovEstimate
open scoped Topology

private theorem norm_bound_on_compact {d : ℕ} {K L : Set (TimeVelocity d)}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) {F : TimeVelocity d → ℝ}
    (hF : ContinuousOn F K) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ K, |F z| ≤ M) :
    parabolicLpNormOn d F K ≤ M * parabolicLpNormOn d (fun _ => 1) L := by
  let p := parabolicExponent d
  let : IsFiniteMeasure (volume.restrict L) := ⟨by simpa using hL.measure_lt_top⟩
  have hc : MemLp (fun _ : TimeVelocity d => M) p (volume.restrict L) := memLp_const _
  have hle := eLpNorm_mono_ae (μ := volume.restrict K) (p := p) (hF.aestronglyMeasurable hK.measurableSet)
    (g := fun _ => M) (ae_restrict_of_forall_mem hK.measurableSet fun z hz => by
      simpa [Real.norm_eq_abs, abs_of_nonneg hM] using hb z hz)
  have h := ENNReal.toReal_mono hc.eLpNorm_ne_top
    (hle.trans (eLpNorm_mono_measure _ (Measure.restrict_mono_set _ hKL)))
  have he := lpNorm_const_smul M (fun _ : TimeVelocity d => (1 : ℝ)) (volume.restrict L) (p := p)
  exact h.trans_eq (by simpa [Pi.smul_def, Real.norm_eq_abs, abs_of_nonneg hM] using! he)

/-- On a box in the unit cylinder a uniform bound on the scalar residual produces an
additive Harnack error, independent of the position and size of the box. -/
theorem exists_classical_harnack_link (d : ℕ) (hd : 1 ≤ d) (lam : ℝ) (hlam : 0 < lam)
    (Lam : ℝ) (hLL : lam ≤ Lam) :
    let U := parabolicInterior 1 (0 : PDE.Vec d)
    ∃ h E : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 ≤ E ∧
      ∀ (B : CoefficientField d) (u : TimeVelocity d → ℝ) (M : ℝ), 0 ≤ M →
        IsContinuousCoefficientOn B U → HasLowerEllipticityOn lam B U →
        HasUpperEllipticityOn Lam B U → IsScalarC12On u U → IsNonnegativeOn u U →
        (∀ z ∈ U, |residual (coefficientAt B) u z| ≤ M) →
      ∀ (t : ℝ) (x : PDE.Vec d) (r : ℝ), 0 < r → r ≤ 1 →
        parabolicClosedBox 2 r (t-r^2) x ⊆ U → ∀ y ∈ velocityCube x (r/2),
        h * u (t,x) ≤ u (t+r^2,y) + E*M := by
  intro U
  let L := closedParabolicCylinder 1 (0 : PDE.Vec d)
  let V := parabolicLpNormOn d (fun _ => 1) L
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  obtain ⟨h, C, hh, hh1, hC, H⟩ := exists_source_local_parabolic_harnack d hd lam hlam Lam hLL
  refine ⟨h, C*V, hh, hh1, mul_nonneg hC.le hV, ?_⟩
  intro B u M hM hc hlo hhi hu hn hf t x r hr hr1 hKU y hy
  let K := parabolicClosedBox 2 r (t-r^2) x
  have hK : IsCompact K := isCompact_parabolicClosedBox ..
  have hU : IsOpen U := isOpen_Ioo.prod (PDE.isOpen_euclideanBall _ _)
  have hp : (t,x) ∈ K := by
    rw [mem_parabolicClosedBox_iff]; refine ⟨by nlinarith [sq_nonneg r], by nlinarith, ?_⟩
    simp [hr.le]
  have hp' : (t+r^2,y) ∈ K := by
    rw [mem_parabolicClosedBox_iff]; refine ⟨by nlinarith [sq_nonneg r], by nlinarith, ?_⟩
    exact fun i => (hy i).le.trans (by linarith)
  have hc' : ContinuousOn (fun z => ∑ i, ∑ j, |coefficientAt B z i j|) K :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn (hc.mono hKU))).abs
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hc'
  let F (δ : ℝ) := u (t+r^2,y) + 2*δ + C * V * (M + δ*(1+max D 0))
  have bound (δ : ℝ) (hδ : 0 < δ) : h*u (t,x) ≤ F δ := by
    obtain ⟨w, hw, hj⟩ := exists_smooth_scalar_jet_close hU hK hKU u hu hδ
    let f := residual (coefficientAt B) w
    have hfc := continuousOn_residual (coefficientAt B) w hc (isScalarC12On_of_contDiff_two hw U)
    have hnon : IsNonnegativeOn (fun z => w z + δ) K := by
      intro z hz; linarith only [(abs_le.mp (hj z hz).1).1, hn z (hKU hz)]
    have hcmp := H K U B (fun z => w z + δ) f t x r hr hK hKU hU Subset.rfl hc
      (hw.add contDiff_const).contDiffOn hfc hnon (fun z hz => hlo z (hKU hz))
      (fun z hz => hhi z (hKU hz)) (fun z _ => (parabolicOperator_add_const ..).trans
        (scalar_residual_eq_parabolicOperator (coefficientAt B) w hw z).symm) y hy
    have hF : ∀ z ∈ K, |f z| ≤ M + δ*(1+max D 0) := by
      intro z hz
      obtain ⟨_, ht, _, hs⟩ := hj z hz
      have hdiff := residual_difference_le (coefficientAt B z) u w z hδ.le
        (((le_abs_self _).trans (hD z hz)).trans (le_max_left D 0)) ht hs
      have ht := abs_sub_le (f z) (residual (coefficientAt B) u z) 0
      simp only [sub_zero] at ht
      exact ht.trans (add_le_add hdiff (hf z (hKU hz))) |>.trans_eq (add_comm ..)
    have he : 0 ≤ M + δ*(1+max D 0) := by positivity
    have hnorm := norm_bound_on_compact hK (isCompact_closedParabolicCylinder 1 0)
      (hKU.trans (parabolicInterior_subset_closedParabolicCylinder 1 0)) (hfc.mono hKU) he hF
    have hscale : r ^ ((d : ℝ) / (d+1)) ≤ 1 := Real.rpow_le_one hr.le hr1 (by positivity)
    have hem : C * r ^ ((d : ℝ)/(d+1)) * parabolicLpNormOn d f K ≤
        C * ((M + δ*(1+max D 0))*V) :=
      mul_le_mul (mul_le_of_le_one_right hC.le hscale) hnorm ENNReal.toReal_nonneg hC.le
    dsimp only [F]
    linarith only [hcmp, hem, mul_le_mul_of_nonneg_left (abs_le.mp (hj _ hp).1).1 hh.le,
      (abs_le.mp (hj _ hp').1).2]
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 (F 0)) :=
    (show Continuous F by dsimp [F]; fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simpa [F] using ge_of_tendsto hlim (Eventually.mono self_mem_nhdsWithin fun _ hx => bound _ hx)

end HypoellipticAleksandrov.Parabolic
