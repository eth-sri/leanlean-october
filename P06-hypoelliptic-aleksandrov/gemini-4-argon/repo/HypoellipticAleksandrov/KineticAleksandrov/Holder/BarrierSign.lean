module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierOperator
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.BarrierSignAcceleration
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.BarrierSignMatrix
import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierProfileTransport
import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierProfileVelocity
import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrier
import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierProfile
import HypoellipticAleksandrov.KineticAleksandrov.Holder.MovingFrameOperator
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The reviewed multiplied Gaussian barrier inequality, including zero amplitude -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open MeasureTheory Set Matrix
open scoped MatrixOrder
open Parabolic Scaling
open Filter
open scoped Topology

/- Ellipticity and the covariance trace give the source Gaussian differential sign. -/
theorem gaussianBarrier_sign {d lam h} (hlam : 0 < lam) (hh : 0 < h)
    (Lam H L ell tminus sblock : ℝ) (hLam : lam ≤ Lam) (hH : 0 ≤ H) (hell : 0 ≤ ell)
    (A : FullKineticCoefficient d) (hA : FullElliptic lam Lam A)
    {x v } (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|) :
    ∀ᵐ P ∂(volume.restrict {P : KineticPoint d |
      0 < P.time - tminus - sblock ∧ P.time - tminus - sblock ≤ h}),
      backwardOperator A (gaussianBarrier lam Lam H h L ell tminus sblock x v) P ≤
        -(3 * lam / 2) * ell *
          Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
            qform lam h (P.time - tminus - sblock)
              (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) *
          PDE.vecNormSq (pform lam h (P.time - tminus - sblock)
            (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) ∧
        -(3 * lam / 2) * ell *
          Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
            qform lam h (P.time - tminus - sblock)
              (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) *
          PDE.vecNormSq (pform lam h (P.time - tminus - sblock)
            (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) ≤ 0 := by
  let S := {P : KineticPoint d | 0 < P.time - tminus - sblock ∧
    P.time - tminus - sblock ≤ h}
  have ht : Continuous (fun P : KineticPoint d => P.time - tminus - sblock) :=
    (continuous_time.sub continuous_const).sub continuous_const
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const ht).measurableSet.inter
      (isClosed_le ht continuous_const).measurableSet
  have hlo := hA.2.2.1.filter_mono (ae_restrict_le (μ := volume) (s := S))
  have hup := hA.2.2.2.filter_mono (ae_restrict_le (μ := volume) (s := S))
  filter_upwards [hlo, hup, ae_restrict_mem hS] with P hl hu hP
  let sigma := P.time - tminus - sblock
  let y := P.position - x (P.time - tminus)
  let V := P.velocity - v (P.time - tminus)
  let pvec := pform lam h sigma y V
  let R := (gramian lam h sigma)⁻¹ 1 1
  let B := fullKineticCoefficientAt A P
  let G := Real.exp (-Xi d lam Lam H h * sigma - qform lam h sigma y V)
  have hs := hP
  have hstrip : -(h / 128) ≤ sigma := by linarith only [hh, hs.1]
  have hR := gramian_inv_velocity_nonneg hlam hh hstrip
  have hLam0 := (hlam.trans_le hLam).le
  have hquad := loewner_quadratic_lower hl pvec
  have htrA := loewner_trace_upper hu
  have htrR := gramian_velocity_trace_le d hlam hh hs.1.le hs.2
  rw [Matrix.trace_smul, Matrix.trace_one] at htrR
  simp only [Fintype.card_fin, smul_eq_mul] at htrR
  have htrace : 2 * R * B.trace ≤ 2 * Lam * (128 * (d : ℝ) / lam) / h := by
    calc
      _ ≤ 2 * R * ((d : ℝ) * Lam) :=
        mul_le_mul_of_nonneg_left htrA (mul_nonneg (by norm_num) hR)
      _ = (2 * Lam) * (R * (d : ℝ)) := by ring
      _ ≤ (2 * Lam) * ((128 * (d : ℝ) / lam) / h) :=
        mul_le_mul_of_nonneg_left htrR (mul_nonneg (by norm_num) hLam0)
      _ = _ := by ring
  have hyoung := acceleration_young hlam (deriv v (P.time - tminus)) pvec
    (vecEuclideanNorm_deriv_le hH (hv.differentiable (by norm_num)) hLip _)
  have hfactor : -Xi d lam Lam H h + lam * PDE.vecNormSq pvec +
      2 * PDE.vecDot (deriv v (P.time - tminus)) pvec + 2 * R * B.trace -
      4 * PDE.vecDot pvec (B.mulVec pvec) ≤ -(3 * lam / 2) * PDE.vecNormSq pvec := by
    unfold Xi
    linarith only [hquad, htrace, hyoung]
  have hG : 0 ≤ ell * G := mul_nonneg hell (Real.exp_pos _).le
  have hsign := mul_le_mul_of_nonneg_left hfactor hG
  have _h_xinl_0 : backwardOperator A (gaussianBarrier lam Lam H h L ell tminus sblock x v) P =
      ell * Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
        qform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) *
      (-Xi d lam Lam H h +
        lam * PDE.vecNormSq (pform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) +
        2 * PDE.vecDot (deriv v (P.time - tminus))
          (pform lam h (P.time - tminus - sblock)
            (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) +
        2 * (gramian lam h (P.time - tminus - sblock))⁻¹ 1 1 *
          (fullKineticCoefficientAt A P).trace -
        4 * PDE.vecDot (pform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)))
          ((fullKineticCoefficientAt A P).mulVec
            (pform lam h (P.time - tminus - sblock)
              (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))))) := by
    have hs := hs.1
    let s := P.time - tminus
    let sigma := s - sblock
    let y := P.position - x s
    let V := P.velocity - v s
    let pvec := pform lam h sigma y V
    let G := Real.exp (-Xi d lam Lam H h * sigma - qform lam h sigma y V)
    let B := fullKineticCoefficientAt A P
    have hf := contDiff_gaussianProfile (d := d) hlam hh Lam H L ell sblock
    have hg : kineticVelocityGradient (fun Q : KineticPoint d =>
        gaussianProfile lam Lam H h L ell sblock (s, (Q.position, Q.velocity)))
        ⟨0, y, V⟩ = (-2 * ell * G) • pvec :=
      gaussianProfile_velocityGradient lam Lam H L ell sblock hh hs y V
    have hHess : kineticVelocityHessian (fun Q : KineticPoint d =>
        gaussianProfile lam Lam H h L ell sblock (s, (Q.position, Q.velocity)))
        ⟨0, y, V⟩ =
        (fun i j => ell * G * (4 * pvec i * pvec j -
          2 * (gramian lam h sigma)⁻¹ 1 1 * (1 : PDE.Mat d) i j)) := by
      rw [kineticVelocityHessian_eq_sliceHessian]
      ext i j
      exact gaussianProfile_velocityHessian lam Lam H L ell sblock hh hs y V i j
    have _h_xinl_0 : deriv (fun t => gaussianProfile lam Lam H h L ell sblock (t, (y, V))) s + deriv (fun r : ℝ => gaussianProfile lam Lam H h L ell sblock (s, (y + r • V, V))) 0 = ell * Real.exp (-Xi d lam Lam H h * (s - sblock) - qform lam h (s - sblock) y V) * (-Xi d lam Lam H h + lam * PDE.vecNormSq (pform lam h (s - sblock) y V)) := by
      rw [gaussianProfile_time_deriv hlam hh Lam H L ell sblock hs,
        gaussianProfile_position_deriv lam Lam H L ell sblock hh hs]
      have hstrip : -(h / 128) < s - sblock := by linarith only [hs, hh]
      have hq := quadratic_transport_identity lam h (s - sblock) hlam hh hstrip y V
      calc
        _ = ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
            qform lam h (s - sblock) y V) *
            (-Xi d lam Lam H h - (deriv (fun t => qform lam h t y V) (s - sblock) +
              deriv (fun r : ℝ => qform lam h (s - sblock) (y + r • V) V) 0)) := by ring
        _ = _ := by rw [hq]; ring
    rw [gaussianBarrier_eq_movingLift,
      movingLift_backwardOperator A hf hx hv hkin tminus P,
      _h_xinl_0]
    change ell * G * (-Xi d lam Lam H h + lam * PDE.vecNormSq pvec) -
      PDE.vecDot (deriv v s) _ - matrixContraction B _ = _
    rw [hg, hHess, matrixContraction_gaussian]
    rw [PDE.vecDot_comm (deriv v s), vecDot_smul_left, PDE.vecDot_comm pvec]
    change _ = ell * G * (-Xi d lam Lam H h + lam * PDE.vecNormSq pvec +
      2 * PDE.vecDot (deriv v s) pvec + 2 * (gramian lam h sigma)⁻¹ 1 1 * B.trace -
      4 * PDE.vecDot pvec (B.mulVec pvec))
    ring
  rw [_h_xinl_0]
  constructor
  · convert hsign using 1; ring
  · change -(3 * lam / 2) * ell * G * PDE.vecNormSq pvec ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hell)
        (Real.exp_pos _).le) (PDE.vecNormSq_nonneg pvec)

end HypoellipticAleksandrov.KineticAleksandrov.Holder
