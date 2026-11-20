module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.Profile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffNativeJets
import HypoellipticAleksandrov.Parabolic.ResolventBarrier
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import Mathlib

/-! # A classical space-time barrier

A small positive time slope is paid for by the trace of a positive velocity
quadratic. Taking a smooth convex positive part costs nothing on the upper side
of the source inequality.
-/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Parabolic
open scoped ContDiff MatrixOrder

variable {d : ℕ} {G : XV d → ℝ}

def affineQuad (a b : ℝ) (G : XV d → ℝ) (q : XV d) := a + b * PDE.vecNormSq q.2 - G q

private theorem quad_smooth (a b : ℝ) (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (affineQuad a b G) :=
  (contDiff_const.add (contDiff_const.mul (PDE.contDiff_vecNormSq.comp contDiff_snd))).sub hG

private theorem quad_deriv (a b : ℝ) (hG : Differentiable ℝ G) (q w : XV d) :
    fderiv ℝ (affineQuad a b G) q w = b * (2 * PDE.vecDot q.2 w.2) - fderiv ℝ G q w := by
  have h := (((hasFDerivAt_vecNormSq q.2).comp q hasFDerivAt_snd).const_mul b |>.const_add a).sub (hG q).hasFDerivAt
  rw [show fderiv ℝ (affineQuad a b G) q = _ from h.fderiv]
  simp

private theorem dv_quad (a b : ℝ) (hG : Differentiable ℝ G) (q : XV d) (k : Fin d) :
    dv (affineQuad a b G) q k = (b*2)*q.2 k - dv G q k := by
  simp [dv,quad_deriv a b hG,PDE.vecDot,Pi.single_apply,mul_ite,mul_assoc]

private theorem stat_quad (A : XV d → PDE.Mat d) (a b : ℝ) (hG : ContDiff ℝ ∞ G) (q : XV d) :
    statOp A (affineQuad a b G) q = -(b*2) * (A q).trace - statOp A G q := by
  have hd := hG.differentiable (by simp)
  have hx (i : Fin d) : dx (affineQuad a b G) q i = -dx G q i := by simp [dx,quad_deriv a b hd,PDE.vecDot]
  have hh (i k : Fin d) : dvv (affineQuad a b G) q i k = ((b*2) • (1 : PDE.Mat d)) i k - dvv G q i k := by
    unfold dvv; simp_rw [dv_quad a b hd]
    have hv : DifferentiableAt ℝ (fun z => dv G z k) q :=
      ((hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp) _
    have hk := (hasFDerivAt_apply (𝕜 := ℝ) k q.2).comp q hasFDerivAt_snd
    have he := ((hk.const_mul (b*2)).sub hv.hasFDerivAt).fderiv
    simp only [Pi.sub_def,Function.comp_def] at he
    rw [he]
    simp [Matrix.one_apply,Pi.single_apply,eq_comm]
  simp only [statOp, PDE.vecDot, hx, mul_neg, Finset.sum_neg_distrib]
  rw [show dvv (affineQuad a b G) q = (b*2) • 1 - dvv G q from Matrix.ext hh]
  have hs (X Y : PDE.Mat d) : matrixContraction (A q) (X-Y) = matrixContraction (A q) X - matrixContraction (A q) Y := by simp [matrixContraction,mul_sub,Finset.sum_sub_distrib]
  rw [hs,matrixContraction_smul_right,matrixContraction_one_eq_trace]; ring

private theorem deriv_cut (G : XV d → ℝ) (hG : Differentiable ℝ G) (q w : XV d) :
    fderiv ℝ (timeCutoffTheta ∘ G) q w = deriv timeCutoffTheta (G q) * fderiv ℝ G q w := by
  have hd := (contDiff_timeCutoffTheta.differentiable (by simp) (G q)).hasDerivAt.comp_hasFDerivAt q (hG q).hasFDerivAt
  rw [hd.fderiv]; rfl

private theorem stat_cut {α : ℝ} (m : ClassicalProfile d α) (hG : ContDiff ℝ ∞ G) (q : XV d) :
    statOp m.A (timeCutoffTheta ∘ G) q ≤ deriv timeCutoffTheta (G q) * statOp m.A G q := by
  let s := deriv timeCutoffTheta (G q)
  let t := deriv (deriv timeCutoffTheta) (G q)
  have h := hG.differentiable (by simp)
  have hd : Differentiable ℝ (deriv timeCutoffTheta) :=
    (contDiff_infty_iff_deriv.mp contDiff_timeCutoffTheta).2.differentiable (by simp)
  have H (i k : Fin d) : dvv (timeCutoffTheta ∘ G) q i k = s * dvv G q i k + t * dv G q i * dv G q k := by
    unfold dvv dv; simp_rw [deriv_cut G h]
    have hk : DifferentiableAt ℝ (fun z => fderiv ℝ G z (0,Pi.single k 1)) q :=
      ((hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp) _
    have he := (((hd _).hasDerivAt.comp_hasFDerivAt q (h q).hasFDerivAt).mul hk.hasFDerivAt).fderiv
    simp only [Pi.mul_def,Function.comp_def] at he
    rw [he]
    simp [s,t]; ring
  have hc : matrixContraction (m.A q) (dvv (timeCutoffTheta ∘ G) q) =
      s * matrixContraction (m.A q) (dvv G q) + t * PDE.vecDot ((m.A q).mulVec (dv G q)) (dv G q) := by
    unfold matrixContraction PDE.vecDot Matrix.mulVec dotProduct
    simp only [H,Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,mul_add]
    congr 1 with i : 1; congr 1 with k : 1; ring
  have hb := vecDot_mulVec_lower_of_loewner (m.elliptic q).1 (dv G q)
  have hnn : 0 ≤ PDE.vecDot ((m.A q).mulVec (dv G q)) (dv G q) := by
    simpa only [PDE.vecDot,mul_comm] using (mul_nonneg m.hlam.le (PDE.vecNormSq_nonneg _)).trans hb
  have hx : PDE.vecDot q.2 (dx (timeCutoffTheta ∘ G) q) = s * PDE.vecDot q.2 (dx G q) := by
    simp only [PDE.vecDot, dx, deriv_cut G h, Finset.mul_sum,s,mul_left_comm]
  rw [statOp,hx,hc,statOp]; dsimp only [s,t] at *; nlinarith [mul_nonneg (timeCutoffTheta_deriv2_nonneg (G q)) hnn]

/-- The test on the whole kinetic carrier, with no extension across a spatial collar. -/
def cappedQuad (a b : ℝ) (G : XV d → ℝ) (P : KineticPoint d) :=
  timeCutoffTheta (affineQuad (3/4 + a*P.time) b G (P.position,P.velocity))

theorem cappedQuad_smooth (a b : ℝ) (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞
    (fun q => cappedQuad a b G ((KineticPoint.equivProd d).symm q)) :=
  contDiff_timeCutoffTheta.comp (((contDiff_const.add (contDiff_const.mul contDiff_fst)).add
    (contDiff_const.mul (PDE.contDiff_vecNormSq.comp contDiff_snd.snd))).sub (hG.comp contDiff_snd))

theorem cappedQuad_le {α : ℝ} (m : ClassicalProfile d α) (a b : ℝ) (hb : 0 ≤ b)
    (hab : a ≤ b*2*((d:ℝ)*m.lam)) (hG : ContDiff ℝ ∞ G) (P : KineticPoint d) :
    backwardOperator (fun _ x v => m.A (x,v)) (cappedQuad a b G) P ≤
      max (-statOp m.A G (P.position,P.velocity)) 0 := by
  let q := (P.position,P.velocity)
  let F := affineQuad (3/4+a*P.time) b G
  let s := deriv timeCutoffTheta (F q)
  have hF := quad_smooth (3/4+a*P.time) b hG
  have hd := (contDiff_timeCutoffTheta.differentiable (by simp) (F q)).hasDerivAt.comp P.time
    (((((hasDerivAt_id P.time).const_mul a).const_add (3/4)).add_const (b*PDE.vecNormSq P.velocity)).sub_const (G q))
  have ht : kineticTimeDerivative (cappedQuad a b G) P = s * a := by simpa only [kineticTimeDerivative,cappedQuad,affineQuad,Function.comp_def,id_eq,mul_one,s,F,q] using hd.deriv
  have hFG := contDiff_timeCutoffTheta.comp hF
  have hx := dx_eq_classicalGradient_at (timeCutoffTheta ∘ F) q (hFG.differentiable (by simp) q)
  have hh := dvv_eq_sliceHessian_at (timeCutoffTheta ∘ F) q (hFG.contDiffAt.of_le (by norm_num))
  rw [backwardOperator_apply, ht,add_sub_assoc]
  change s*a + (PDE.vecDot q.2 _ - matrixContraction (m.A q) _) ≤ _
  rw [← show dx (timeCutoffTheta ∘ F) q = kineticPositionGradient (cappedQuad a b G) P from hx,
    ← show dvv (timeCutoffTheta ∘ F) q = kineticVelocityHessian (cappedQuad a b G) P from hh]
  have H := stat_cut m hF q
  rw [show statOp m.A F q = _ from stat_quad m.A _ _ hG q] at H
  have hs := timeCutoffTheta_deriv_bounds (F q)
  have htrace := hab.trans (mul_le_mul_of_nonneg_left (barrier_trace_lower _ _ (m.elliptic q).1) (by positivity))
  have he : s*a + statOp m.A (timeCutoffTheta ∘ F) q ≤ s*(-statOp m.A G q) := by
    dsimp only [s]; nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr htrace)]
  exact he.trans ((mul_le_mul_of_nonneg_left (le_max_left _ _) hs.1).trans
    (mul_le_of_le_one_left (le_max_right _ _) hs.2))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
