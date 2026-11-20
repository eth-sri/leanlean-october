module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileBounds

/-! # Exact homogeneity and gauge bound for the velocity gradient -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

variable {d : ℕ} (alpha : ℝ) (H : XV d → ℝ) (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) (r : ℝ) (hr : 0 < r)
    (q : XV d) (hq : q ≠ 0)

include hr hq in
/-- Positive kinetic dilation preserves nonzero points. -/
theorem dilate_ne_zero :
    dilate r q ≠ 0 := by
  intro hzero
  exact hq (Prod.ext ((smul_eq_zero_iff_right (pow_ne_zero 3 hr.ne')).mp (congrArg Prod.fst hzero))
    ((smul_eq_zero_iff_right hr.ne').mp (congrArg Prod.snd hzero)))

include hsmooth hhom hr hq in
/-- The derivative of a homogeneous smooth function has the source velocity weight. -/
theorem homogeneous_velocity_jet (w : PDE.Vec d) :
    fderiv ℝ H (dilate r q) (0, w) =
      Real.rpow r (alpha - 1) * fderiv ℝ H q (0, w) := by
  have hqmem := hq
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hrqd := (hsmooth.contDiffAt (hopen.mem_nhds (dilate_ne_zero r hr q hq))).differentiableAt (by simp)
  have hh := hrqd.hasFDerivAt.comp q ((hasFDerivAt_fst.const_smul (r ^ 3)).prodMk (hasFDerivAt_snd.const_smul r))
  have hother : HasFDerivAt (fun z => H (dilate r z))
      (Real.rpow r alpha • fderiv ℝ H q) q := by
    convert ((hsmooth.contDiffAt (hopen.mem_nhds hqmem)).differentiableAt (by simp)).hasFDerivAt.const_mul (Real.rpow r alpha) using 1
    funext z
    exact hhom r hr z
  have heq := congrArg (fun L : XV d →L[ℝ] ℝ => L (0, w)) (hh.unique hother)
  have hsmul : (0, r • w) = r • ((0, w) : XV d) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_zero, smul_eq_mul] at heq
  rw [hsmul, map_smul, smul_eq_mul] at heq
  have hpower : Real.rpow r (alpha - 1) = Real.rpow r alpha / r := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr, Real.rpow_one]
  rw [hpower]
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
