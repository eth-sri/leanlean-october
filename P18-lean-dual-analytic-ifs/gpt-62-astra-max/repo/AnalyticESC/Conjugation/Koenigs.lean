module
public import AnalyticESC.Attractor
public import AnalyticESC.Analysis

@[expose] public section
namespace AnalyticESC
open Set Metric Filter Topology

/-- Two primitives produce the increasing coordinate `g = ∫ exp(∫ H)` with `g''/g' = H`. -/
theorem exists_coord {ε : ℝ} (he : 0 < ε) {H : ℂ → ℂ} (hd : DifferentiableOn ℂ H (nbhd ε))
    (hr : ∀ x : ℝ, (x:ℂ) ∈ nbhd ε → (H x).im = 0) : ∃ g, Regular g ∧ EqOn (D g) (H ∘ Complex.ofReal) I := by
  have primitive {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (nbhd ε)) : ∃ F, ∀ z ∈ nbhd ε, HasDerivAt F (f z) z := by
    obtain ⟨F,hF⟩ := (convex_nbhd ε).exists_forall_hasDerivWithinAt hf
    exact ⟨F,fun z hz => (hF z hz).hasDerivAt ((isOpen_nbhd ε).mem_nhds hz)⟩
  obtain ⟨F,hF⟩ := primitive hd
  let A z := Complex.exp (F z - F 0)
  have hA {z} (hz : z ∈ nbhd ε) : HasDerivAt A (A z * H z) z := ((hF z hz).sub_const (F 0)).cexp
  obtain ⟨G,hG⟩ := primitive (fun _ hz => (hA hz).differentiableAt.differentiableWithinAt)
  let g := restr G
  have han : AnalyticOnNhd ℝ g I := analyticOnNhd_re_ofReal he fun _ hz => (hG _ hz).differentiableAt.differentiableWithinAt
  have h1 {x : ℝ} (hx : (x:ℂ) ∈ nbhd ε) : deriv g x = (A x).re :=
    (hG _ hx).real_of_complex.deriv
  have pos {x} (hx : x ∈ I) : 0 < (A (x:ℂ)).re := by
    have d (y : ℝ) (hy : y ∈ I) : HasDerivWithinAt (fun t : ℝ => (F t).im) 0 I y := by
      have h := ofReal_mem_nbhd he hy
      exact (hr y h) ▸ (Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hF _ h).comp_ofReal).hasDerivWithinAt
    simp [A,Complex.exp_re,eq_of_hasDerivWithinAt_zero_I d hx zero_I,Real.exp_pos]
  refine ⟨g,⟨han,fun x hx => (h1 (ofReal_mem_nbhd he hx)) ▸ (pos hx).ne'⟩,fun x hx => ?_⟩
  have hz := ofReal_mem_nbhd he hx
  have eq : deriv g =ᶠ[𝓝 x] fun t : ℝ => (A t).re := eventually_of_mem (near_real (isOpen_nbhd _) hz) fun _ => h1
  have h2 := (hA hz).real_of_complex.deriv
  apply Complex.ext <;> simp [D,logDer,eq.deriv_eq,h2,h1 hz,Complex.mul_re,hr x hz,(pos hx).ne']

end AnalyticESC
