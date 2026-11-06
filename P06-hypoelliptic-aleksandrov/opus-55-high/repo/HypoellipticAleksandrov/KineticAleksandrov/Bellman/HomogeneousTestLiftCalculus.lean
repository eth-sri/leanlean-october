module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpace
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-! # Directional chain rules for the literal Bellman dilation -/

@[expose] public section
noncomputable section
open Set Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The anisotropic dilation is a genuine continuous linear map of the plane. -/
def bellmanDilationLinear (r : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (r ^ 3 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (r • ContinuousLinearMap.snd ℝ ℝ ℝ)

variable (r : ℝ) (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ)

/-- The position chain rule has the anisotropic cubic factor. -/
theorem bellmanDx_comp_dilation 
    (hphi : DifferentiableAt ℝ phi (bellmanPlaneDilation r q)) :
    bellmanDx (fun z => phi (bellmanPlaneDilation r z)) q =
      r ^ 3 * bellmanDx phi (bellmanPlaneDilation r q) := by
  have hf := hphi.hasFDerivAt.comp q (bellmanDilationLinear r).hasFDerivAt
  change HasFDerivAt (fun z => phi _) _ q at hf
  rw [bellmanDx, hf.fderiv]
  simp only [ContinuousLinearMap.comp_apply, bellmanDilationLinear,
    ContinuousLinearMap.prod_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one, mul_zero]
  have he : (r ^ 3, (0)) = r ^ 3 • ((1), (0 : ℝ)) := by simp
  rw [he, map_smul]
  rfl

/-- The velocity chain rule has the linear radial factor. -/
theorem bellmanDv_comp_dilation 
    (hphi : DifferentiableAt ℝ phi (bellmanPlaneDilation r q)) :
    bellmanDv (fun z => phi (bellmanPlaneDilation r z)) q =
      r * bellmanDv phi (bellmanPlaneDilation r q) := by
  have hf := hphi.hasFDerivAt.comp q (bellmanDilationLinear r).hasFDerivAt
  change HasFDerivAt (fun z => phi _) _ q at hf
  rw [bellmanDv, hf.fderiv]
  simp only [ContinuousLinearMap.comp_apply, bellmanDilationLinear,
    ContinuousLinearMap.prod_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one, mul_zero]
  have he : ((0), r) = r • ((0 : ℝ), (1)) := by simp
  rw [he, map_smul]
  rfl

/-- The second velocity chain rule has the quadratic radial factor. -/
theorem bellmanDvv_comp_dilation  (hr : 0 < r)
    (phi : (ℝ × ℝ) → ℝ) (hp : ContDiffOn ℝ 2 phi bellmanPuncturedSet)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
    bellmanDvv (fun z => phi (bellmanPlaneDilation r z)) q =
      r ^ 2 * bellmanDvv phi (bellmanPlaneDilation r q) := by
  have hmap (z : ℝ × ℝ) (hz : z ∈ bellmanPuncturedSet) :
      bellmanPlaneDilation r z ∈ bellmanPuncturedSet :=
    bellmanPlaneDilation_ne_zero r hr z hz
  have hd (z : ℝ × ℝ) (hz : z ∈ bellmanPuncturedSet) :
      DifferentiableAt ℝ phi _ :=
    ((hp _ (hmap z hz)).contDiffAt
      (bellmanPuncturedSet_isOpen.mem_nhds (hmap z hz))).differentiableAt (by norm_num)
  have hv : ContDiffOn ℝ 1 (bellmanDv phi) bellmanPuncturedSet :=
    (hp.fderiv_of_isOpen bellmanPuncturedSet_isOpen (m := 1) (by norm_num)).clm_apply
      contDiffOn_const
  have hvd : DifferentiableAt ℝ (bellmanDv phi) _ :=
    ((hv _ (hmap q hq)).contDiffAt
      (bellmanPuncturedSet_isOpen.mem_nhds (hmap q hq))).differentiableAt (by norm_num)
  have he : bellmanDv (fun z => phi (bellmanPlaneDilation r z)) =ᶠ[𝓝 q]
      fun z => r * bellmanDv phi (bellmanPlaneDilation r z) := by
    filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
    exact bellmanDv_comp_dilation r phi z (hd z hz)
  have hf := (hvd.hasFDerivAt.comp q (bellmanDilationLinear r).hasFDerivAt).const_mul r
  change HasFDerivAt (fun z => r * bellmanDv phi _) _ q at hf
  rw [bellmanDvv, he.fderiv_eq, hf.fderiv]
  simp only [ContinuousLinearMap.comp_apply, bellmanDilationLinear,
    ContinuousLinearMap.prod_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one, mul_zero]
  have he0 : ((0), r) = r • ((0 : ℝ), (1)) := by simp
  rw [he0, map_smul]
  change r * (r * bellmanDvv phi _) = _
  ring

/-- Both terms in the Bellman operator acquire the same quadratic factor under dilation. -/
theorem bellmanOperator_comp_dilation  (hr : 0 < r)
    (phi : (ℝ × ℝ) → ℝ) (hp : ContDiffOn ℝ 2 phi bellmanPuncturedSet)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) (b : ℝ) :
    bellmanOperator b (fun z => phi (bellmanPlaneDilation r z)) q =
      r ^ 2 * bellmanOperator b phi (bellmanPlaneDilation r q) := by
  have hmap := bellmanPlaneDilation_ne_zero r hr q hq
  have hd := ((hp _ hmap).contDiffAt
    (bellmanPuncturedSet_isOpen.mem_nhds hmap)).differentiableAt (by norm_num)
  rw [bellmanOperator, bellmanDx_comp_dilation r phi q hd,
    bellmanDvv_comp_dilation r hr phi hp q hq, bellmanOperator]
  simp only [bellmanPlaneDilation]
  ring

end HypoellipticAleksandrov.KineticAleksandrov
