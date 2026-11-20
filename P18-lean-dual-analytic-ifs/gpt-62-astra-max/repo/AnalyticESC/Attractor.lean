module
public import AnalyticESC.Separation
public import AnalyticESC.Dual.Recursion

@[expose] public section
namespace AnalyticESC.IFS
open Set Metric Filter Topology
variable {N : ℕ} (Φ : IFS N)

/-- `π(ω) = f_{ω₁ ⋯ ω_k}(π(σ^k ω))`, where `σ` is the left shift. -/
theorem natProj_eq_comp_prefix (ω : Address N) (k : ℕ) :
    Φ.natProj ω = Φ.R (block k ω) (Φ.natProj (shift k ω)) := by
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat k).2 (Φ.tendsto_natProj ω)) ?_
  have hc := ((Φ.regular_R (block k ω)).1 _ (Φ.pi_mem (shift k ω))).continuousAt
  exact (hc.tendsto.comp (Φ.tendsto_natProj _)).congr fun n => by rw [block_add,Φ.R_append _ _ zero_I]; rfl

/-! ### The natural projection and the attractor -/

/-- `π(ω) = f_{ω₀}(π(σω))`, where `σ` is the left shift. -/
theorem natProj_eq_realMap (ω : Address N) :
    Φ.natProj ω = Φ.realMap (ω 0) (Φ.natProj fun j => ω (j + 1)) := by
  simpa [block,pref,R] using Φ.natProj_eq_comp_prefix ω 1

/-- Uniform approximation by prefixes, for every initial point of the interval. -/
lemma approx (ω : Address N) (n : ℕ) {x} (hx : x ∈ I) : |Φ.natProj ω - Φ.R (block n ω) x| ≤ Φ.cmax^n := by
  rw [Φ.natProj_eq_comp_prefix ω n]
  simpa only [block,List.length_ofFn] using Φ.abs_re_comp_sub_le (block n ω) (Φ.pi_mem _) hx

/-- The natural projection is continuous. -/
theorem continuous_natProj : Continuous Φ.natProj := by
  refine TendstoUniformly.continuous
    (F := fun n ω => Φ.R (block n ω) 0) (p := atTop) ?_
    (Frequently.of_forall fun n => ?_)
  · rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    filter_upwards [Φ.shrinks.eventually (gt_mem_nhds hδ)] with n hn ω
    exact (Φ.approx ω n zero_I).trans_lt hn
  · unfold R block pref; fun_prop

/-- The attractor is invariant: `Λ = ⋃_i f_i(Λ)`. -/
theorem attractor_eq_iUnion : Φ.attractor = ⋃ i, Φ.realMap i '' Φ.attractor := by
  ext x
  simp only [mem_iUnion, mem_image]
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨ω 0, _, ⟨_, rfl⟩, (Φ.natProj_eq_realMap ω).symm⟩
  · rintro ⟨i, _, ⟨ω, rfl⟩, rfl⟩
    exact ⟨Stream'.cons i ω, Φ.natProj_eq_realMap _⟩

/-- The remark after Theorem 1.6: the attractor is a singleton exactly when the maps have a
common fixed point in `I`. -/
theorem exists_attractor_eq_singleton_iff (hN : 0 < N) :
    (∃ x, Φ.attractor = {x}) ↔ ∃ x ∈ I, ∀ i, Φ.realMap i x = x := by
  constructor
  · rintro ⟨x, hx⟩
    have hxK  := hx ▸ mem_singleton x
    refine ⟨x, Φ.attractor_subset_I hxK, fun i => ?_⟩
    have h := Function.apply_eq_of_range_eq_singleton hx (fun _ => i)
    simpa only [← h] using (Φ.natProj_eq_realMap (fun _ => i)).symm
  · rintro ⟨p,hp,hfix⟩
    have : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
    refine ⟨p,range_eq_singleton fun ω => ?_⟩
    let E (w : Address N) := |Φ.natProj w - p|
    have hb : BddAbove (range E) := ⟨1,forall_mem_range.mpr fun w => by have := Φ.pi_mem w; dsimp [E]; grind⟩
    have step (w) : ∃ v, E w ≤ Φ.cmax * E v := by
      refine ⟨shift 1 w,?_⟩
      have h := Φ.R_lip [w 0] (Φ.pi_mem (shift 1 w)) hp
      rw [show Φ.R [w 0] p = p from hfix _,List.length_singleton,pow_one] at h
      dsimp only [E]; rw [Φ.natProj_eq_realMap w]; exact h
    simpa [E,sub_eq_zero] using contraction_estimate Φ.cmax_nonneg Φ.cmax_lt_one hb step ω

end AnalyticESC.IFS
