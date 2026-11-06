module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileSpectralJets

/-! # Homogeneity of the full velocity Hessian and stationary transport -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/- Punctured homogeneity is sufficient for the exact velocity derivative scaling. -/
theorem punctured_homogeneous_velocity_jet {d : ℕ} (beta : ℝ) (F : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) F ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, q ≠ 0 →
      F (dilate r q) = Real.rpow r beta * F q)
    (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) (w : PDE.Vec d) :
    fderiv ℝ F (dilate r q) (0, w) = Real.rpow r (beta - 1) * fderiv ℝ F q (0, w) := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hqd := (hsmooth.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by simp)
  have hrqd := (hsmooth.contDiffAt
    (hopen.mem_nhds (dilate_ne_zero r hr q hq))).differentiableAt (by simp)
  have hd : HasFDerivAt (dilate (d := d) r)
      ((r ^ 3 • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d)).prod
        (r • ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))) q :=
    (hasFDerivAt_fst.const_smul (r ^ 3)).prodMk (hasFDerivAt_snd.const_smul r)
  have hh := hrqd.hasFDerivAt.comp q hd
  have hother : HasFDerivAt (fun z => F (dilate r z)) (Real.rpow r beta • fderiv ℝ F q) q := by
    apply (hqd.hasFDerivAt.const_mul (Real.rpow r beta)).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hq] with z hz
    exact hhom r hr z hz
  have heq := congrArg (fun L : XV d →L[ℝ] ℝ => L (0, w)) (hh.unique hother)
  have hsmul : (0, r • w) = r • ((0, w) : XV d) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_zero, smul_eq_mul] at heq
  rw [hsmul, map_smul, smul_eq_mul] at heq
  have hpower : Real.rpow r (beta - 1) = Real.rpow r beta / r := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr, Real.rpow_one]
  rw [hpower, div_mul_eq_mul_div]
  apply (eq_div_iff hr.ne').mpr
  simpa only [mul_comm] using heq

/- The velocity Hessian has the exact kinetic weight alpha minus two. -/
theorem homogeneous_position_jet {d : ℕ} (alpha : ℝ) (H : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) (w : PDE.Vec d) :
    fderiv ℝ H (dilate r q) (w, 0) = Real.rpow r (alpha - 3) * fderiv ℝ H q (w, 0) := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hqd := (hsmooth.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by simp)
  have hrqd := (hsmooth.contDiffAt
    (hopen.mem_nhds (dilate_ne_zero r hr q hq))).differentiableAt (by simp)
  have hd : HasFDerivAt (dilate (d := d) r)
      ((r ^ 3 • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d)).prod
        (r • ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))) q :=
    (hasFDerivAt_fst.const_smul (r ^ 3)).prodMk (hasFDerivAt_snd.const_smul r)
  have hh := hrqd.hasFDerivAt.comp q hd
  have hother : HasFDerivAt (fun z => H (dilate r z)) (Real.rpow r alpha • fderiv ℝ H q) q := by
    convert hqd.hasFDerivAt.const_mul (Real.rpow r alpha) using 1
    funext z
    exact hhom r hr z
  have heq := congrArg (fun L : XV d →L[ℝ] ℝ => L (w, 0)) (hh.unique hother)
  have hsmul : (r ^ 3 • w, 0) = r ^ 3 • ((w, 0) : XV d) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_zero, smul_eq_mul] at heq
  rw [hsmul, map_smul, smul_eq_mul] at heq
  have hpower : Real.rpow r (alpha - 3) = Real.rpow r alpha / r ^ (3 : ℕ) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr]
    norm_num
  rw [hpower, div_mul_eq_mul_div]
  apply (eq_div_iff (pow_ne_zero 3 hr.ne')).mpr
  simpa only [mul_comm] using heq

/- The actual stationary transport has the same kinetic weight as the velocity Hessian. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
