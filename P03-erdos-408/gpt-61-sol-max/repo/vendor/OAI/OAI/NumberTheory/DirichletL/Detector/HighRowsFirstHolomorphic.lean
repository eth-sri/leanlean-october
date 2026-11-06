module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.HighRowsHolomorphic

@[expose] public section

namespace OAI


namespace SevenEighths.ProbeEuler

section
variable (Q : ℝ) (A eta v x w z : ℂ) (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 1/2≤x.re) (hz : 1/3≤z.re)


include hQ hA he hv hx hz in
lemma first_open_region_denominators    
           
        :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hQ0 : 0<Q := by linarith
  
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

include hQ hA he hv hz in
theorem unramifiedClosed_first_analytic_x    
              :
    AnalyticOnNhd ℂ (fun x=>unramifiedClosed Q A eta v x w z) {x : ℂ|1/2<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

include hQ hA he hv hx hz in
theorem unramifiedClosed_first_analytic_w    
           
        :
    AnalyticOnNhd ℂ (fun w=>unramifiedClosed Q A eta v x w z) (Set.univ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro w hw
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

include hQ hA he hv hx in
theorem unramifiedClosed_first_analytic_z    
              :
    AnalyticOnNhd ℂ (unramifiedClosed Q A eta v x w) {z : ℂ|1/3<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

end

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower

variable (p : ActualEisensteinCubic.O) (hp : Prime p) [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

section
variable (eta a rho x w z : ℂ) (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)≤z.re) (j : ℕ)


include hQ ha hz in
lemma ramifiedClosed_first_analytic_x  
            :
    AnalyticOnNhd ℂ (fun x=>ramifiedClosed p hp hg eta a rho x w z j) {x : ℂ|1/2<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simp_all) (by norm_num) (by norm_num) hx.le hz
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho id (fun _=>w) (fun _=>z) x
    differentiableAt_id (differentiableAt_const w) (differentiableAt_const z) hd.2.1 hd.1 j).differentiableWithinAt

include hQ ha hx hz in
lemma ramifiedClosed_first_analytic_w  
       
          :
    Differentiable ℂ (fun w=>ramifiedClosed p hp hg eta a rho x w z j) := by
  intro w
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simp_all) (by norm_num) (by norm_num) hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) id (fun _=>z) w
    (differentiableAt_const x) differentiableAt_id (differentiableAt_const z) hd.2.1 hd.1 j

include hQ ha hx in
lemma ramifiedClosed_first_analytic_z  
            :
    AnalyticOnNhd ℂ (fun z=>ramifiedClosed p hp hg eta a rho x w z j) {z : ℂ|1/3<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simp_all) (by norm_num) (by norm_num) hx hz.le
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) (fun _=>w) id z
    (differentiableAt_const x) (differentiableAt_const w) differentiableAt_id hd.2.1 hd.1 j).differentiableWithinAt

end

end SevenEighths.ProbeEuler


end OAI
