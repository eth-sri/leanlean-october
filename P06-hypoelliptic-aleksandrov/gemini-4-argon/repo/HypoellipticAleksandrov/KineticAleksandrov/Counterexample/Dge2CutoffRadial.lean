module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Cutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Signs

/-!
# Exact radial jets for the exterior of the Appendix C cutoff

These formulas use Euclidean dot products on the native coordinate carrier.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/- The first radial jet at a nonzero velocity. -/
def radialHessianForm {d } (alpha : ℝ) (y w u : PDE.Vec d) : ℝ :=
  alpha * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 1) * PDE.vecDot w u +
    alpha * (alpha - 2) * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 2) *
      PDE.vecDot y w * PDE.vecDot y u

/- Differentiating the first radial jet gives the exact second jet. -/
theorem radialProfile_hessian {d } (alpha : ℝ) (y w u : PDE.Vec d)
    (hy : y ≠ 0) :
    fderiv ℝ (fun z => fderiv ℝ (radialProfile alpha) z w) y u =
      radialHessianForm alpha y w u := by
  have _h_inl_9 : HasFDerivAt (fun z => fderiv ℝ (radialProfile alpha) z w)
      ((PDE.vecDot y w *
          (alpha * (alpha - 2) * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 2))) •
        seedDotLinear y +
        (alpha * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 1)) • seedDotLinear w) y := by
      have hb : HasFDerivAt (PDE.vecNormSq (d := d)) (2 • seedDotLinear y) y := by
        simpa only [seedBase, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, sub_zero]
          using hasFDerivAt_seedBase 0 y 0
      have hp := (hb.rpow_const (p := alpha / 2 - 1)
        (Or.inl (PDE.vecNormSq_eq_zero_iff.not.mpr hy))).const_mul alpha
      have hd : HasFDerivAt (fun z => PDE.vecDot z w) (seedDotLinear w) y := by
        convert (seedDotLinear w).hasFDerivAt (x := y) using 1
        ext z
        simp only [seedDotLinear_apply, PDE.vecDot, mul_comm]
      have hh := hp.mul hd
      have hexp : alpha / 2 - 1 - 1 = alpha / 2 - 2 := by ring
      have hformula : HasFDerivAt
          (fun z => alpha * Real.rpow (PDE.vecNormSq z) (alpha / 2 - 1) * PDE.vecDot z w)
          ((PDE.vecDot y w *
              (alpha * (alpha - 2) * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 2))) •
            seedDotLinear y +
            (alpha * Real.rpow (PDE.vecNormSq y) (alpha / 2 - 1)) • seedDotLinear w) y := by
        convert hh using 1
        ext u
        simp only [smul_apply, smul_eq_mul, add_apply, two_smul, Real.rpow_eq_pow, hexp]
        ring
      apply hformula.congr_of_eventuallyEq
      filter_upwards [(isOpen_ne.mem_nhds hy)] with z hz
      have _h_inl_6 : HasFDerivAt (radialProfile alpha)
          ((alpha * Real.rpow (PDE.vecNormSq z) (alpha / 2 - 1)) • seedDotLinear z) z := by
          have hb : HasFDerivAt (PDE.vecNormSq (d := d)) (2 • seedDotLinear z) z := by
            simpa only [seedBase, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, sub_zero]
              using hasFDerivAt_seedBase 0 z 0
          convert hb.rpow_const (p := alpha / 2)
            (Or.inl (PDE.vecNormSq_eq_zero_iff.not.mpr hz)) using 1
          · rfl
          · ext w
            simp only [smul_apply, smul_eq_mul, two_smul, add_apply, Real.rpow_eq_pow]
            ring


      rw [_h_inl_6.fderiv]
      simp only [smul_apply, smul_eq_mul, seedDotLinear_apply]

    /- The exterior radial Hessian evaluated on arbitrary directions. -/
  rw [_h_inl_9.fderiv]
  simp only [radialHessianForm, smul_apply, smul_eq_mul, add_apply, seedDotLinear_apply]
  ring

/- The radial Hessian has a positive direction in dimensions at least two. -/
theorem radialHessian_positive_direction (d ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (y : PDE.Vec d) (hy : y ≠ 0) :
    ∃ w : PDE.Vec d, 0 < radialHessianForm alpha y w w := by
  obtain ⟨w, hw, hdot⟩ := exists_native_perpendicular d hd y
  refine ⟨w, ?_⟩
  have hsq : 0 < PDE.vecNormSq w :=
    (PDE.vecNormSq_nonneg w).lt_of_ne' (PDE.vecNormSq_eq_zero_iff.not.mpr hw)
  have hypos : 0 < PDE.vecNormSq y :=
    (PDE.vecNormSq_nonneg y).lt_of_ne' (PDE.vecNormSq_eq_zero_iff.not.mpr hy)
  simpa [radialHessianForm, hdot, PDE.vecNormSq] using
    mul_pos (mul_pos ha (Real.rpow_pos_of_pos hypos (alpha / 2 - 1))) hsq

/- The radial direction is strictly negative when alpha is between zero and one. -/
theorem radialHessian_radial_neg {d } (alpha : ℝ) (ha : 0 < alpha)
    (ha1 : alpha < 1) (y : PDE.Vec d) (hy : y ≠ 0) :
    radialHessianForm alpha y y y < 0 := by
  have hypos : 0 < PDE.vecNormSq y :=
    (PDE.vecNormSq_nonneg y).lt_of_ne' (PDE.vecNormSq_eq_zero_iff.not.mpr hy)
  have hpower : Real.rpow (PDE.vecNormSq y) (alpha / 2 - 1) =
      Real.rpow (PDE.vecNormSq y) (alpha / 2 - 2) * PDE.vecNormSq y := by
    simp only [Real.rpow_eq_pow]
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

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
