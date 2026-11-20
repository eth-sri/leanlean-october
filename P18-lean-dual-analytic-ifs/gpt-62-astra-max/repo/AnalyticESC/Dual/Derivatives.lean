module

public import AnalyticESC.Dual.Projection

@[expose] public section

/-! # Convergence of projections and their jets -/
namespace AnalyticESC
open Set Metric Filter Topology

/-- Locally uniform convergence of holomorphic functions passes to all jets. -/
lemma jet_convergence {α : Type*} {l : Filter α} {F : α → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ} (ho : IsOpen U)
    (ha : ∀ k, AnalyticOnNhd ℂ (F k) U) (lim : TendstoLocallyUniformlyOn F g l U) (r : ℕ) :
    TendstoLocallyUniformlyOn (fun k => deriv^[r] (F k)) (deriv^[r] g) l U := by
  induction r with
  | zero => exact lim
  | succ r ih =>
    simpa only [Function.iterate_succ_apply',Function.comp_def] using
      (ih.deriv (.of_forall fun k => ((ha k).iterated_deriv r).differentiableOn) ho)

lemma pref_limit {N α} {l : Filter α} {v : α → Address N} {w} (hv : Tendsto v l (𝓝 w)) (n) :
    ∀ᶠ k in l, pref n (v k) = pref n w := by
  simpa using ((show Continuous (pref (N := N) n) by unfold pref; fun_prop).tendsto w).comp hv

/-- Stabilization of each finite prefix gives uniform convergence on the tube,
hence convergence of any jet, even at a varying argument. -/
lemma IFS.proj_limit {N α} (Φ : IFS N) {l : Filter α} {v : α → Address N} {w} {L : α → ℕ∞}
    (hv : Tendsto v l (𝓝 w)) (hL : Tendsto L l (𝓝 ⊤)) {z : α → ℂ} {x : ℂ} (hx : x ∈ Φ.tube)
    (hz : Tendsto z l (𝓝 x)) (r : ℕ) : Tendsto (fun k => deriv^[r] (Φ.dualProj (L k) (v k)) (z k)) l
      (𝓝 (deriv^[r] (Φ.dualProj ⊤ w) x)) := by
  have lim : TendstoUniformlyOn (fun k => Φ.dualProj (L k) (v k)) (Φ.dualProj ⊤ w) l Φ.tube := by
    rw [Metric.tendstoUniformlyOn_iff]; intro δ hδ
    obtain ⟨m,hm⟩ := ((Φ.shrinks.const_mul (2*Φ.amp)).eventually_lt_const (by simpa using hδ)).exists
    filter_upwards [pref_limit hv m,hL.eventually (Ici_mem_nhds (ENat.coe_lt_top m))] with k e hk z h'
    have h := subset_closure h'
    have H := Φ.mapsTo_comp_closure (block m w).reverse h
    rw [dist_eq_norm,Φ.expand (L k) _ hk h,Φ.expand ⊤ w (m := m) le_top h,show block m (v k) = block m w from congrArg List.ofFn e,add_sub_add_left_eq_sub,← mul_sub,norm_mul,mul_comm]
    apply lt_of_le_of_lt _ hm
    exact mul_le_mul ((norm_sub_le _ _).trans (by linarith [Φ.proj_le (⊤-m) (shift m w) H,Φ.proj_le (L k-m) (shift m (v k)) H])) (by simpa [block] using (Φ.bounds (block m w).reverse h).2) (norm_nonneg _) (by linarith [Φ.amp_nonneg])
  exact (jet_convergence (isOpen_nbhd _) (fun k => Φ.analytic_dual _ _) lim.tendstoLocallyUniformlyOn r).tendsto_comp
    (((Φ.analytic_dual _ _).iterated_deriv r).continuousOn _ hx) hx ((isOpen_nbhd _).nhdsWithin_eq hx ▸ hz)

end AnalyticESC
