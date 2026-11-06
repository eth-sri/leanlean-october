module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftRegularity
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-! # The literal spatial derivative of the radial lift integrand -/

@[expose] public section
open Set Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The joint derivative in a spatial direction has the literal dilation chain factor. -/
theorem bellmanLiftIntegrand_spatial_fderiv (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiff ℝ 1 zeta) (q : ℝ × ℝ) (r : ℝ) (hr : 0 < r) (e : ℝ × ℝ) :
    fderiv ℝ (bellmanLiftIntegrand alpha zeta) (q, r) (e, 0) =
      r ^ (-1 - alpha) * fderiv ℝ zeta (bellmanPlaneDilation r q)
        (bellmanDilationLinear r e) := by
  have hf := bellmanLiftIntegrand_contDiffOn_order 1 alpha zeta hz
  have hd : DifferentiableAt ℝ (bellmanLiftIntegrand alpha zeta) _ :=
    ((hf (q, r) ⟨trivial, hr⟩).contDiffAt
      ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨trivial, hr⟩)).differentiableAt (by norm_num)
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) × ℝ :=
    (ContinuousLinearMap.id ℝ _).prod 0
  have hpair : HasFDerivAt (fun x : ℝ × ℝ => (x, r)) L q :=
    (hasFDerivAt_id q).prodMk (hasFDerivAt_const r q)
  have hcomp := hd.hasFDerivAt.comp q hpair
  have hslice := (((hz.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).comp q
    (bellmanDilationLinear r).hasFDerivAt).const_mul (r ^ (-1 - alpha))
  have he := congrArg (fun D : (ℝ × ℝ) →L[ℝ] ℝ => D e) (hcomp.unique hslice)
  aesop

end HypoellipticAleksandrov.KineticAleksandrov
