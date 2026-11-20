module

public import AnalyticESC.Basic
public import AnalyticESC.Words

@[expose] public section

/-!
# The dual natural projection

Convergence and holomorphy of the series (1.4) defining `H_w`, its uniform bounds, the cocycle
identity for prepended words, the formula (2.7) `H_{v^←} = f_v''/f_v'` for finite words, and
Lemma 2.5, analyticity and Hölder continuity: `H_w ∈ C^ω_ε([0,1])` and Hölder dependence on the word.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} (Φ : IFS N)

/-! ## The terms of the series -/

/-- A bound on distortion along the orbit gives geometric decay of the series. -/
lemma term_bound {B : ℝ} (hB : 0 ≤ B) (l : ℕ∞) (w : Address N) (n : ℕ) {z : ℂ} (hz : z ∈ Φ.box)
    (hb : ∀ i a, ‖Φ.nonlin i (Φ.comp a z)‖ ≤ B) : ‖Φ.dualTerm l w n z‖ ≤ B * Φ.cmax ^ n := by
  unfold dualTerm; split
  · simpa [block] using mul_le_mul (hb (w n) (block n w).reverse) (Φ.bounds (block n w).reverse hz).2 (norm_nonneg _) hB
  · simpa using mul_nonneg hB (pow_nonneg Φ.cmax_nonneg n)

lemma term_le (l w n) {z : ℂ} (hz : z ∈ Φ.box) : ‖Φ.dualTerm l w n z‖ ≤ Φ.outerBeta * Φ.cmax^n :=
  Φ.term_bound (norm_nonneg _) l w n hz fun i a => eval_le (fun j => Φ.onBox (Φ.analytic_nonlin j).continuousOn) i ⟨_,Φ.mapsTo_comp_closure a hz⟩

lemma geom : HasSum (fun n : ℕ => Φ.cmax^n) (1-Φ.cmax)⁻¹ := hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one

theorem summable_dualTerm (l w) {z : ℂ} (hz : z ∈ Φ.box) :
    Summable fun n => Φ.dualTerm l w n z := Summable.of_norm_bounded (Φ.geom.summable.mul_left _) fun n => Φ.term_le l w n hz

lemma finite_sum (w : Address N) (m : ℕ) (z : ℂ) : Φ.dualProj m w z = ∑ n ∈ Finset.range m, Φ.dualTerm ⊤ w n z := by
  rw [dualProj,tsum_eq_sum (s := Finset.range m) (f := fun n => Φ.dualTerm m w n z) (by intro n hn; simp [dualTerm,Finset.mem_range.not.mp hn])]
  exact Finset.sum_congr rfl fun n hn => by simp_all [dualTerm]

/-- The finite sum telescopes by the chain rule for logarithmic derivatives. -/
lemma partial_log (w : Address N) (m : ℕ) {z} (hz : z ∈ Φ.box) : Φ.dualProj m w z = logDer (Φ.comp (block m w).reverse) z := by
  induction m with
  | zero => rw [Φ.finite_sum]; simp [block,logDer]
  | succ m ih =>
    rw [Φ.finite_sum,Finset.sum_range_succ,← Φ.finite_sum,ih,add_comm m 1,block_add]
    simp only [block,pref,List.ofFn_succ,List.ofFn_zero,shift,zero_add,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append,comp_cons]
    simpa [dualTerm,nonlin,mul_comm] using (logDer_comp (Φ.analytic_f (w m) _ (Φ.mapsTo_comp_closure (block m w).reverse hz)) (Φ.analytic_comp _ _ hz) ((Φ.inClass _).deriv_ne_zero _ (Φ.mapsTo_comp_closure _ hz))).symm

/-! ## Bounds -/

lemma tail_bound {B : ℝ} {l w z} (h : ∀ n, ‖Φ.dualTerm l w n z‖ ≤ B*Φ.cmax^n) (m : ℕ) :
    ‖∑' n, Φ.dualTerm l w (n+m) z‖ ≤ B*Φ.cmax^m/(1-Φ.cmax) := by
  rw [div_eq_mul_inv]; apply tsum_of_norm_bounded (Φ.geom.mul_left _)
  intro n; simpa [pow_add,mul_assoc,mul_comm,mul_left_comm] using h (n+m)

noncomputable abbrev amp := Φ.outerBeta/(1-Φ.cmax)
lemma amp_nonneg : 0 ≤ Φ.amp := div_nonneg (norm_nonneg _) (sub_nonneg.mpr Φ.cmax_lt_one.le)
lemma proj_le (l w) {z} (hz : z ∈ Φ.box) : ‖Φ.dualProj l w z‖ ≤ Φ.amp := by
  simpa [dualProj] using Φ.tail_bound (fun n => Φ.term_le l w n hz) 0

/-! ## Holomorphy and realness -/

theorem analytic_dual (l w) : AnalyticOnNhd ℂ (Φ.dualProj l w) Φ.tube := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_nbhd _)
  apply Complex.differentiableOn_tsum_of_summable_norm (Φ.geom.summable.mul_left _) _ (isOpen_nbhd _) fun n _ hz => Φ.term_le l w n (subset_closure hz)
  intro n; unfold dualTerm; split
  · exact (((Φ.analytic_nonlin _).comp (Φ.analytic_comp _) (Φ.mapsTo_comp_closure _)).mul
      (Φ.analytic_comp _).deriv).differentiableOn.mono subset_closure
  · exact differentiableOn_const _

theorem im_dualProj_ofReal (l w) {t : ℝ} (ht : (t : ℂ) ∈ Φ.tube) : (Φ.dualProj l w t).im = 0 := by
  rw [dualProj, Complex.im_tsum (Φ.summable_dualTerm l w (subset_closure ht))]
  have h n : (Φ.dualTerm l w n t).im = 0 := by
    unfold dualTerm; split
    · let a := (block n w).reverse
      have e : Φ.comp a t = (Φ.R a t : ℂ) := (Φ.R_jet a 0 ht).symm
      have h2 := e ▸ Φ.mapsTo_comp a ht
      change (logDer (Φ.comp [w n]) (Φ.comp a t) * deriv^[1] (Φ.comp a) t).im = 0
      rw [e,← Φ.R_logDer [w n] h2,← Φ.R_jet a 1 ht]; norm_cast
    · rfl
  simp [h]

/-- Splitting after `m` letters factors the remaining series through the prefix map. -/
lemma expand (l : ℕ∞) (w : Address N) {m : ℕ} (hm : (m:ℕ∞) ≤ l) {z} (hz : z ∈ Φ.box) :
    Φ.dualProj l w z = logDer (Φ.comp (block m w).reverse) z + deriv (Φ.comp (block m w).reverse) z * Φ.dualProj (l-m) (shift m w) (Φ.comp (block m w).reverse z) := by
  rw [← Φ.partial_log w m hz,Φ.finite_sum,dualProj,← (Φ.summable_dualTerm l w hz).sum_add_tsum_nat_add m,dualProj,← tsum_mul_left]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp [dualTerm,lt_of_lt_of_le (by exact_mod_cast Finset.mem_range.mp hn : (n:ℕ∞) < m) hm]
  · refine tsum_congr fun n => ?_
    have e : (n:ℕ∞) < l-m ↔ ((n+m:ℕ):ℕ∞) < l := by enat_to_nat <;> omega
    simp only [dualTerm,e]; split <;> simp only [Pi.zero_apply,mul_zero]
    rw [block_add,List.reverse_append,Φ.deriv_comp_append _ _ hz,Φ.comp_append,Function.comp_apply]; dsimp [shift]; ring

end IFS
end AnalyticESC
