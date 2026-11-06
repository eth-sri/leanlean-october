module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CoordinatesHessian
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileGradient
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Local full-product and slice jet identities away from the profile origin -/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

variable {d : ℕ} (H : XV d → ℝ) (q : XV d) (x v w : PDE.Vec d)

/-- The native full-product velocity derivative agrees with its literal slice derivative. -/
theorem fderiv_velocity_slice 
    (hH : DifferentiableAt ℝ H (x, v)) :
    fderiv ℝ (fun z => H (x, z)) v w = fderiv ℝ H (x, v) (0, w) := by
  have hi : HasFDerivAt (fun z : PDE.Vec d => (x, z))
      ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ _)) v := by
    fun_prop
  have hh := hH.hasFDerivAt.comp v hi
  have hh' : HasFDerivAt (fun z => H (x, z))
      ((fderiv ℝ H (x, v)).comp
        ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ _))) v := by
    aesop
  rw [hh'.fderiv]
  simp

/-- Scalar evaluation of the full first derivative gives its literal second derivative. -/
theorem full_secondDirectional_eq  (q u w : XV d)
    (hH : ContDiffAt ℝ (⊤ : ℕ∞) H q) :
    fderiv ℝ (fun z => fderiv ℝ H z w) q u = fderiv ℝ (fderiv ℝ H) q u w := by
  have hd := (hH.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- A smooth full-product velocity Hessian agrees with the literal velocity slice Hessian. -/
theorem full_velocity_hessian_eq_slice  (x v w u : PDE.Vec d)
    (hH : ContDiffAt ℝ (⊤ : ℕ∞) H (x, v)) :
    fderiv ℝ (fun z => fderiv ℝ H z (0, w)) (x, v) (0, u) =
      fderiv ℝ (fun z => fderiv ℝ (fun a => H (x, a)) z w) v u := by
  have hi : HasFDerivAt (fun z : PDE.Vec d => (x, z))
      ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ _)) v := by
    fun_prop
  have hd := ((hH.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    (contDiffAt_const (c := ((0, w))))).differentiableAt (by simp)
  have hh := hd.hasFDerivAt.comp v hi
  have hevent : (fun z => fderiv ℝ (fun a => H (x, a)) z w) =ᶠ[nhds v]
      (fun z => fderiv ℝ H (x, z) (0, w)) := by
    have hc : Continuous (fun z : PDE.Vec d => (x, z)) := by fun_prop
    have hreg := hc.continuousAt.eventually ((hH.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by
      simp)).eventually (by simp))
    filter_upwards [hreg] with z hz
    exact fderiv_velocity_slice H x z w (hz.differentiableAt (by norm_num))
  rw [hevent.fderiv_eq]
  have hh' : HasFDerivAt (fun z => fderiv ℝ H (x, z) (0, w))
      ((fderiv ℝ (fun z => fderiv ℝ H z (0, w)) (x, v)).comp
        ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ _))) v := by
    fun_prop
  rw [hh'.fderiv]
  simp

/-- The full-product position derivative agrees with its literal position slice. -/
theorem fderiv_position_slice 
    (hH : DifferentiableAt ℝ H (x, v)) :
    fderiv ℝ (fun z => H (z, v)) x w = fderiv ℝ H (x, v) (w, 0) := by
  have hi : HasFDerivAt (fun z : PDE.Vec d => (z, v))
      ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod (0)) x := by
    fun_prop
  have hh := hH.hasFDerivAt.comp x hi
  have hh' : HasFDerivAt (fun z => H (z, v))
      ((fderiv ℝ H (x, v)).comp
        ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod
          (0 : PDE.Vec d →L[ℝ] PDE.Vec d))) x := by
    aesop
  rw [hh'.fderiv]
  simp

/-- Native position selectors conditions to the full directional transport derivative. -/
theorem transport_eq_direction  :
    PDE.vecDot q.2 (dx H q) = fderiv ℝ H q (q.2, 0) := by
  have heq : (q.2, (0)) =
      ∑ i : Fin d, q.2 i • ((Pi.single i 1, 0) : XV d) := by
    apply Prod.ext
    · ext k
      simp [Prod.fst_sum, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [heq, map_sum]
  simp only [map_smul, smul_eq_mul, dx, PDE.vecDot]

/-- The local full-product Hessian matrix is Hermitian at every smooth point. -/
theorem dvv_isHermitian 
    (hH : ContDiffAt ℝ (⊤ : ℕ∞) H q) : (dvv H q).IsHermitian := by
  ext i k
  change fderiv ℝ (fun z => fderiv ℝ H z _) q _ =
    fderiv ℝ (fun z => fderiv ℝ H z _) q _
  rw [full_secondDirectional_eq H q _ _ hH, full_secondDirectional_eq H q _ _ hH]
  exact (hH.isSymmSndFDerivAt (by simp)).eq _ _

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
