module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsHolomorphic
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

section
variable (Q : ℝ)
include Q
lemma first_open_region_denominators (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 1/2≤x.re) (hz : 1/3≤z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by pm_3844

theorem unramifiedClosed_first_analytic_x (A eta v w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 1/3≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedClosed Q A eta v x w z) {x : ℂ|1/2<x.re} := by pm_3845 first_open_region_denominators

theorem unramifiedClosed_first_analytic_w (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 1/2≤x.re) (hz : 1/3≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedClosed Q A eta v x w z) (Set.univ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  pm_635 first_open_region_denominators

theorem unramifiedClosed_first_analytic_z (A eta v x w : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 1/2≤x.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedClosed Q A eta v x w z) {z : ℂ|1/3<z.re} := by pm_3846 first_open_region_denominators
end

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

lemma ramifiedClosed_first_analytic_x (eta a rho w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hz : (1/3:ℝ)≤z.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun x=>ramifiedClosed p hp hg eta a rho x w z j) {x : ℂ|1/2<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  pm_3931 hx.le hz
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho id (fun _=>w) (fun _=>z) x
    differentiableAt_id (differentiableAt_const w) (differentiableAt_const z) hd.2.1 hd.1 j).differentiableWithinAt

lemma ramifiedClosed_first_analytic_w (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1)
    (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)≤z.re) (j : ℕ) :
    Differentiable ℂ (fun w=>ramifiedClosed p hp hg eta a rho x w z j) := by
  intro w
  pm_3931 hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) id (fun _=>z) w
    (differentiableAt_const x) differentiableAt_id (differentiableAt_const z) hd.2.1 hd.1 j

lemma ramifiedClosed_first_analytic_z (eta a rho x w : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hx : (1/2:ℝ)≤x.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun z=>ramifiedClosed p hp hg eta a rho x w z j) {z : ℂ|1/3<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  pm_3931 hx hz.le
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) (fun _=>w) id z
    (differentiableAt_const x) (differentiableAt_const w) differentiableAt_id hd.2.1 hd.1 j).differentiableWithinAt

end SevenEighths.ProbeEuler
end

end OAI
