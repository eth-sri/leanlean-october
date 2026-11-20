module

public import AnalyticESC.Basic
public import AnalyticESC.Words

@[expose] public section

/-!
# Separation conditions

The natural projection and the attractor, the equivalence in Definition 1.2 between the failure
of the SESC and weak super-exponential condensation, the implication SESC ⇒ ESC, and the
consequence of having no exact overlaps used in Lemma 4.1.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} (Φ : IFS N)

theorem tendsto_natProj (ω : Address N) :
    Tendsto (fun n => Φ.R (block n ω) 0) atTop (𝓝 (Φ.natProj ω)) := by
  apply tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete _)
  apply cauchySeq_of_le_geometric Φ.cmax 1 Φ.cmax_lt_one
  intro n
  rw [Real.dist_eq,add_comm n 1,block_add,Φ.R_append _ _ zero_I,one_mul]
  simpa only [block,List.length_ofFn] using Φ.abs_re_comp_sub_le (block n ω) zero_I (Φ.re_comp_mem_I _ zero_I)

theorem pi_mem (ω : Address N) : Φ.natProj ω ∈ I := isClosed_Icc.mem_of_tendsto (Φ.tendsto_natProj ω)
  (Eventually.of_forall fun n => Φ.re_comp_mem_I (block n ω) zero_I)

theorem attractor_subset_I : Φ.attractor ⊆ I := by rintro _ ⟨ω,rfl⟩; exact Φ.pi_mem ω

lemma le_real_sup {g : ℂ → ℝ} (hg : ContinuousOn g Φ.tube) {x : ℝ} (hx : x ∈ I) : g x ≤ ⨆ y : I, g y :=
  le_sup isCompact_Icc (hg.comp Complex.continuous_ofReal.continuousOn fun _ => Φ.real_mem) hx

lemma close_after (u i j : Letters N) {x : ℝ} (hx : x ∈ I) : |Φ.R u (Φ.R i x) - Φ.R u (Φ.R j x)| ≤ Φ.supDist i j := by
  apply (Φ.R_lip u (Φ.re_comp_mem_I i hx) (Φ.re_comp_mem_I j hx)).trans
  apply (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ Φ.cmax_nonneg Φ.cmax_lt_one.le)).trans
  exact (Complex.abs_re_le_norm _).trans (Φ.le_real_sup (((Φ.differentiableOn_comp i).continuousOn.sub (Φ.differentiableOn_comp j).continuousOn).norm) hx)

theorem esc_of_sesc (h : Φ.SESC) : Φ.ESC := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, Frequently.of_forall h⟩

end IFS

end AnalyticESC
