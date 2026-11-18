module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Cutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Signs
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample


/-- The exact first radial derivative applied to a native vector. -/
theorem fderiv_radialProfile_apply {d : ℕ} (alpha : ℝ) (y w : PDE.Vec d)
    (hy : y ≠ 0) :
    fderiv ℝ (radialProfile alpha) y w =
      alpha * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 1) * PDE.vecDot y w  := by
  have hasFDerivAt_radialProfile :
      HasFDerivAt (radialProfile alpha)
      ((alpha * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 1)) • seedDotLinear y) y := by
    have hb : HasFDerivAt (PDE.vecNormSq) (2 • seedDotLinear y) y := by
      simpa [seedBase, zero_pow (by norm_num : 2 ≠ 0)]
        using hasFDerivAt_seedBase 0 y 0
    convert hb.rpow_const (p := alpha / 2)
      (Or.inl (PDE.vecNormSq_eq_zero_iff.not.mpr hy)) using 1
    · rfl
    · ext w
      simp
      ring
  rw [(hasFDerivAt_radialProfile).fderiv]
  simp [smul_apply, seedDotLinear_apply]

/-- The radial Hessian as a rank-one perturbation of the Euclidean identity. -/
def radialHessianForm {d : ℕ} (alpha : ℝ) (y w u : PDE.Vec d) : ℝ :=
  alpha * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 1) * PDE.vecDot w u +
    alpha * (alpha - 2) * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 2) *
      PDE.vecDot y w * PDE.vecDot y u


/-- The exterior radial Hessian evaluated on arbitrary directions. -/
theorem radialProfile_hessian {d : ℕ} (alpha : ℝ) (y w u : PDE.Vec d)
    (hy : y ≠ 0) :
    fderiv ℝ (fun z => fderiv ℝ (radialProfile alpha) z w) y u =
      radialHessianForm alpha y w u  := by
  have hasFDerivAt_radialProfile_first :
      HasFDerivAt (fun z => fderiv ℝ (radialProfile alpha) z w)
      ((PDE.vecDot y w *
          (alpha * (alpha - 2) * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 2))) •
        seedDotLinear y +
        (alpha * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 1)) • seedDotLinear w) y := by
    have hb : HasFDerivAt (PDE.vecNormSq (d := d)) (2 • seedDotLinear y) y := by
      simpa [seedBase, zero_pow (by norm_num : 2 ≠ 0)]
        using hasFDerivAt_seedBase 0 y 0
    have hd : HasFDerivAt (fun z => PDE.vecDot z w) (seedDotLinear w) y := by
      convert (seedDotLinear w).hasFDerivAt (x := y) using 1
      ext z
      simp only [seedDotLinear_apply, PDE.vecDot, mul_comm]
    have hh := ((hb.rpow_const (p := alpha / 2 - 1) (Or.inl (PDE.vecNormSq_eq_zero_iff.not.mpr hy))).const_mul alpha).mul hd
    have hexp : alpha / 2 - 1 - 1 = alpha / 2 - 2 := by ring
    have hformula : HasFDerivAt
        (fun z => alpha * Real.rpow (PDE.vecNormSq z) (alpha / 2 - 1) * PDE.vecDot z w)
        ((PDE.vecDot y w *
            (alpha * (alpha - 2) * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 2))) •
          seedDotLinear y +
          (alpha * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 1)) • seedDotLinear w) y := by
      convert hh using 1
      ext u
      simp
      ring
    apply hformula.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne.mem_nhds hy)] with z hz
    exact fderiv_radialProfile_apply alpha z w hz
  rw [(hasFDerivAt_radialProfile_first).fderiv]
  simp [radialHessianForm, smul_apply, add_apply, seedDotLinear_apply]
  ring

/-- The radial Hessian has a positive direction in dimensions at least two. -/
theorem radialHessian_positive_direction (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (y : PDE.Vec d) (hy : y ≠ 0) :
    ∃ w : PDE.Vec d, 0 < radialHessianForm alpha y w w := by
  obtain ⟨w, hw, hdot⟩ := exists_native_perpendicular d hd y
  refine ⟨w, ?_⟩
  have hsq :=
    (PDE.vecNormSq_nonneg w).lt_of_ne' (PDE.vecNormSq_eq_zero_iff.not.mpr hw)
  have hypos :=
    (PDE.vecNormSq_nonneg y).lt_of_ne' (PDE.vecNormSq_eq_zero_iff.not.mpr hy)
  simpa [radialHessianForm, hdot, PDE.vecNormSq] using
    mul_pos (mul_pos ha (Real.rpow_pos_of_pos hypos (alpha / 2 - 1))) hsq

/-- The radial direction is strictly negative when alpha is between zero and one. -/
theorem radialHessian_radial_neg {d : ℕ} (alpha : ℝ) (ha : 0 < alpha)
    (ha1 : alpha < 1) (y : PDE.Vec d) (hy : y ≠ 0) :
    radialHessianForm alpha y y y < 0 := by
  have hypos :=
    (PDE.vecNormSq_nonneg y).lt_of_ne' (PDE.vecNormSq_eq_zero_iff.not.mpr hy)
  have hpower : Real.rpow (PDE.vecNormSq y) (alpha / 2 - 1) =
      Real.rpow (PDE.vecNormSq y) (alpha / 2 - 2) * PDE.vecNormSq y := by
    simp
    calc
      PDE.vecNormSq y ^ (alpha / 2 - 1) =
          PDE.vecNormSq y ^ ((alpha / 2 - 2) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hypos, Real.rpow_one]
  have heq : radialHessianForm alpha y y y =
      (alpha * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 2) *
        (PDE.vecNormSq y) ^ 2) * (alpha - 1) := by
    unfold radialHessianForm
    rw [hpower]
    unfold PDE.vecNormSq
    ring
  rw [heq]
  exact mul_neg_of_pos_of_neg
    (mul_pos (mul_pos ha (Real.rpow_pos_of_pos hypos _)) (sq_pos_of_pos hypos))
    (sub_neg.mpr ha1)


/-- The cutoff interpolation on a fixed annulus, with independent constant and scale. -/
def rescaledCutoff {d : ℕ} (alpha sigma s t : ℝ) (e z : PDE.Vec d) : ℝ :=
  radialProfile alpha z + radialCutoff 1 z *
    (s + Real.rpow (seedBase (t * sigma) z (t • e)) (alpha / 2) - radialProfile alpha z)

/-- The zero-parameter interpolation is exactly the radial profile. -/
theorem rescaledCutoff_zero {d : ℕ} (alpha sigma : ℝ) (e z : PDE.Vec d) :
    rescaledCutoff alpha sigma 0 0 e z = radialProfile alpha z := by
  simp [rescaledCutoff, seedBase, radialProfile]



/-- The velocity Hessian is continuous jointly at every regular parameter point. -/
theorem continuousAt_rescaledCutoff_hessian {d : ℕ} (alpha sigma : ℝ)
    (p : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d) (hz : p.2 ≠ 0)
    (hb : seedBase (p.1.2.1 * sigma) p.2 (p.1.2.1 • p.1.2.2) ≠ 0)
    (w u : PDE.Vec d) :
    ContinuousAt
      (fun q : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d =>
        fderiv ℝ (fun z =>
          fderiv ℝ (rescaledCutoff alpha sigma q.1.1 q.1.2.1 q.1.2.2) z w) q.2 u) p  := by
  have contDiffAt_rescaledCutoff_first :
      ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q =>
        fderiv ℝ (rescaledCutoff alpha sigma q.1.1 q.1.2.1 q.1.2.2) q.2) p := by
    have contDiffAt_rescaledCutoff :
        ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q =>
          rescaledCutoff alpha sigma q.1.1 q.1.2.1 q.1.2.2 q.2) p := by
      have hr : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun q => radialProfile alpha q.2) p :=
        (PDE.contDiff_vecNormSq.comp contDiff_snd).contDiffAt.rpow_const_of_ne
          (PDE.vecNormSq_eq_zero_iff.not.mpr hz)
      have hbase : ContDiff ℝ (⊤ : ℕ∞)
          (fun q : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d =>
            seedBase (q.1.2.1 * sigma) q.2 (q.1.2.1 • q.1.2.2)) := by
        unfold seedBase PDE.vecNormSq PDE.vecDot
        fun_prop
      have hs : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun q => q.1.1) p := by fun_prop
      exact hr.add (((contDiff_radialCutoff 1).comp contDiff_snd).contDiffAt.mul
        ((hs.add (hbase.contDiffAt.rpow_const_of_ne hb)).sub hr))
    have hf := contDiffAt_rescaledCutoff
    have hc : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q => (q.1.1, q.2))
        (p, p.2) := by fun_prop
    exact (hf.comp (p, p.2) hc).fderiv contDiffAt_snd (by simp)
  have heval : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q =>
        fderiv ℝ (rescaledCutoff alpha sigma q.1.1 q.1.2.1 q.1.2.2) q.2 w) p :=
    contDiffAt_rescaledCutoff_first.clm_apply contDiffAt_const
  have hc : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => (q.1.1, q.2))
      (p, p.2) := by fun_prop
  exact (((heval.comp (p, p.2) hc).fderiv (m := 0) contDiffAt_snd (by simp)).clm_apply
    contDiffAt_const).continuousAt

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

