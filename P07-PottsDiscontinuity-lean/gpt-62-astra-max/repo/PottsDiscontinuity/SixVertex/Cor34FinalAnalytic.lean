module
public import PottsDiscontinuity.Bethe.Theorem23Kernel
public import PottsDiscontinuity.Bethe.DiscreteCore
public import PottsDiscontinuity.BetheAnsatz.Scattering

/-! # Analyticity of the two physical eigenvalue formulas

Only the square of the row parameter occurs. For the derivative correction
we reuse the analytic partial derivative of the regularized Bethe phase. -/
@[expose] public section
open Filter Topology Set
namespace PottsDiscontinuity.SixVertex
open BetheAnsatz

noncomputable def rowParameter (d : ℝ) := Real.sqrt (2-2*d)
lemma rowParameter_gt {d : ℝ} (hd : d < -1) : 2 < rowParameter d :=
  (Real.lt_sqrt (by norm_num)).mpr (by linarith)
lemma rowParameter_sq {d : ℝ} (hd : d < -1) : rowParameter d ^ 2 = 2-2*d := Real.sq_sqrt (by linarith)
lemma rowParameter_anisotropy {d : ℝ} (hd : d < -1) : anisotropy (rowParameter d) = d := by
  rw [anisotropy,rowParameter_sq hd]; ring

lemma analytic_complex_cast {f : ℝ → ℝ} {d : ℝ} (h : AnalyticAt ℝ f d) :
    AnalyticAt ℝ (fun t => (f t : ℂ)) d := Complex.ofRealCLM.analyticAt _ |>.comp h
private lemma analytic_row_sq {d : ℝ} (hd : d < -1) : AnalyticAt ℝ (fun t => (rowParameter t : ℂ)^2) d := by
  apply (analytic_complex_cast (f := fun t => 2-2*t) (by fun_prop)).congr
  filter_upwards [gt_mem_nhds hd] with t ht; rw [← rowParameter_sq ht, Complex.ofReal_pow]

variable {n : ℕ} {d : ℝ} {p : ℝ → Fin n → ℝ} (hd : d < -1) (hp : AnalyticAt ℝ p d)
private lemma analytic_component (j : Fin n) (hp : AnalyticAt ℝ p d) : AnalyticAt ℝ (fun t => p t j) d := by
  have h : AnalyticAt ℝ (fun v : Fin n → ℝ => v j) (p d) := by
    convert (ContinuousLinearMap.proj (R := ℝ) j).analyticAt (p d) using 1
    ext v; rfl
  exact h.comp hp
include hd hp
private lemma analytic_factors {j : Fin n} (hq : p d j ∈ Ioo (-Real.pi) Real.pi) (hn : p d j ≠ 0) :
    AnalyticAt ℝ (fun t => L (rowParameter t) (z (p t j))) d ∧
    AnalyticAt ℝ (fun t => M (rowParameter t) (z (p t j))) d := by
  have hcoord : AnalyticAt ℝ (fun t => p t j) d := analytic_component j hp
  have hz : AnalyticAt ℝ (fun t => z (p t j)) d :=
    analyticAt_cexp.restrictScalars.comp (analyticAt_const.mul (analytic_complex_cast hcoord))
  have hden : 1 - z (p d j) ≠ 0 := sub_ne_zero.mpr (z_ne_one hq hn).symm
  have hc := analytic_row_sq hd
  exact ⟨analyticAt_const.add ((hc.mul hz).div (analyticAt_const.sub hz) hden),
    analyticAt_const.sub (hc.div (analyticAt_const.sub hz) hden)⟩

lemma analytic_eigenvalueRegular (hS : p d ∈ Bethe.S_n n)
    (hnz : ∀ j, p d j ≠ 0) : AnalyticAt ℝ (fun t => eigenvalueRegular (rowParameter t) (p t)) d := by
  have h (j) := analytic_factors hd hp (hS.1 j) (hnz j)
  exact (Finset.univ.analyticAt_fun_prod fun j _ => (h j).1).add (Finset.univ.analyticAt_fun_prod fun j _ => (h j).2)

lemma analytic_eigenvalueZero (N : ℕ) (l : Fin n) (hS : p d ∈ Bethe.S_n n)
    (hnz : ∀ j ≠ l, p d j ≠ 0) : AnalyticAt ℝ (fun t => eigenvalueZero N (rowParameter t) (p t) l) d := by
  have hinv := (analyticAt_const (v := (1:ℝ))).div (analyticAt_id (𝕜 := ℝ)) (by linarith : d ≠ 0)
  have hder (j : Fin n) : AnalyticAt ℝ (fun t => (Bethe.d1Theta (anisotropy (rowParameter t)) 0 (p t j) : ℂ)) d := by
    apply analytic_complex_cast
    have h : AnalyticAt ℝ (fun t => Bethe.thetaFirstInv (1/t) 0 (p t j)) d :=
      (Bethe.analyticAt_thetaFirstInv (Bethe.abs_inverse_parameter_lt_one hd) 0 (p d j)).comp (f := fun t : ℝ => (1/t,0,p t j))
        (hinv.prod (analyticAt_const.prod (analytic_component j hp)))
    apply h.congr; filter_upwards [gt_mem_nhds hd] with t ht
    rw [rowParameter_anisotropy ht,Bethe.d1Theta_eq_thetaFirstInv ht]
  have hdC (j : Fin n) : AnalyticAt ℝ (fun t => deriv (fun u => (Bethe.theta (anisotropy (rowParameter t)) u (p t j):ℂ)) 0) d := by
    apply (hder j).congr; filter_upwards [gt_mem_nhds hd] with t ht
    exact (Bethe.analyticAt_theta_left (anisotropy_lt_neg_one (rowParameter_gt ht)) 0 (p t j)).differentiableAt.hasDerivAt.ofReal_comp.deriv.symm
  have hc := analytic_row_sq hd
  exact (((analyticAt_const (v := (2:ℂ))).add (hc.mul (analyticAt_const (v := (N:ℂ)-1)))).add (hc.mul ((Finset.univ.erase l).analyticAt_fun_sum fun j _ => hdC j))).mul
    ((Finset.univ.erase l).analyticAt_fun_prod fun j hj => (analytic_factors hd hp (hS.1 j) (hnz j (Finset.ne_of_mem_erase hj))).2)
end PottsDiscontinuity.SixVertex
