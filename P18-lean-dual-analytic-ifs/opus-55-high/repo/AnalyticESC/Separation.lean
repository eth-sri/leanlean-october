module

public import AnalyticESC.Basic

public section

set_option hygiene false
local notation "𝔟" => n + B
local notation "𝔞" => B + 1
local notation "𝖒" => Φ.comp [w n] 0

/-!
# Separation conditions

The natural projection and the attractor, the equivalence in Definition 1.2 between the failure
of the SESC and weak super-exponential condensation, the implication SESC ⇒ ESC, and the
consequence of having no exact overlaps used in Lemma 4.1.
-/

namespace AnalyticESC

variable {x : ℝ}

open Set Filter Topology

namespace IFS

variable (Φ : IFS N ε) (i j : 𝔚 N)

theorem tendsto_natProj w :
    Tendsto (fun n => (Φ.comp (List.ofFn fun k : Fin n => w k) 0).re) atTop (𝓝 (Φ.natProj w)) := by
  have hz0 : (0 : ℂ) ∈ nbhd ε := ofReal_mem_nbhd Φ.ε_pos zero_mem_I
  have hu : ∀ n, dist (Φ.comp (List.ofFn fun k : Fin n => w k) 0).re
      (Φ.comp (List.ofFn fun k : Fin (n + 1) => w k) 0).re ≤ 1 * Φ.cmax ^ n := by
    intro n
    have hsplit : (List.ofFn fun k : Fin (n + 1) => w k) =
        (List.ofFn fun k : Fin n => w k) ++ [w n] := by
      rw [List.ofFn_succ', List.concat_eq_append]
      simp
    rw [hsplit, Φ.comp_append, Function.comp_apply, Real.dist_eq, one_mul]
    set v := List.ofFn fun k => w k
    calc |(Φ.comp v 0).re - (Φ.comp v 𝖒).re|
        = |(Φ.comp v 0 - Φ.comp v 𝖒).re| := by simp_all
      _ ≤ ‖Φ.comp v 0 - Φ.comp v 𝖒‖ := Complex.abs_re_le_norm _
      _ ≤ Φ.cmax ^ v.length * ‖0 - Φ.comp [w n] 0‖ := Φ.norm_comp_sub_le v (by grind) (Φ.mapsTo_comp [w n] (by grind))
      _ ≤ Φ.cmax ^ n * 1 := by
          rw [List.length_ofFn, zero_sub, norm_neg]
          exact mul_le_mul_of_nonneg_left (by simpa using Φ.norm_comp_ofReal_le_one [w n] zero_mem_I) (pow_nonneg Φ.cmax_nonneg n)
      _ = Φ.cmax ^ n := mul_one _
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric Φ.cmax 1
    Φ.cmax_lt_one hu)
  exact tendsto_nhds_limUnder ⟨a, ha⟩

theorem attractor_subset_I : Φ.attractor ⊆ I := by
  rintro _ ⟨w, rfl⟩
  exact isClosed_Icc.mem_of_tendsto (Φ.tendsto_natProj w)
    (Eventually.of_forall fun n => by simpa using Φ.re_comp_mem_I _ zero_mem_I)

theorem bddAbove_supDist :
    BddAbove (range fun x : I => ‖Φ.comp i x - Φ.comp j x‖) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨x, rfl⟩
  calc _ ≤ ‖Φ.comp i x‖ + ‖Φ.comp j x‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (Φ.norm_comp_ofReal_le_one i x.2) (Φ.norm_comp_ofReal_le_one j x.2)
    _ = 2 := by norm_num

theorem norm_le_supDist (hx : x ∈ I) :
    ‖Φ.comp i x - Φ.comp j x‖ ≤ Φ.supDist i j :=
  le_ciSup
    (Φ.bddAbove_supDist i j) ⟨x, hx⟩

/-- Appending a common suffix does not increase the distance. -/
theorem supDist_append_le i j u :
    Φ.supDist (i ++ u) (j ++ u) ≤ Φ.supDist i j := by
  refine ciSup_le fun x => ?_
  rw [Φ.comp_append, Φ.comp_append, Function.comp_apply, Function.comp_apply,
    Φ.comp_ofReal u x.2]
  exact Φ.norm_le_supDist i j (Φ.re_comp_mem_I u x.2)

/-- Without the SESC, close pairs occur at arbitrarily high levels. -/
theorem exists_close_pair_ge (h : ¬ Φ.SESC) (hc : 0 < c) B :
    ∃ n, B ≤ n ∧ ∃ i j : Fin n → Fin N, i ≠ j ∧
      Φ.supDist (List.ofFn i) (List.ofFn j) < c ^ n := by
  by_contra hcon
  push Not at hcon
  apply h
  set c₀ := min c 1
  have hc₀ := lt_min hc one_pos
  refine ⟨c₀ ^ 𝔞, pow_pos hc₀ _, fun n i j hij => ?_⟩
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (Subsingleton.elim i j) hij
    · exact hn
  let u : Fin B → Fin N := fun _ => i ⟨0, hn⟩
  have hne : Fin.append i u ≠ Fin.append j u := by
    intro he
    apply hij
    have := congrArg List.ofFn he
    rw [List.ofFn_fin_append, List.ofFn_fin_append] at this
    exact List.ofFn_injective (List.append_cancel_right this)
  have h1 := hcon 𝔟 (Nat.le_add_left B n) _ _ hne
  rw [List.ofFn_fin_append, List.ofFn_fin_append] at h1
  calc (c₀ ^ 𝔞) ^ n = c₀ ^ (𝔞 * n) := (pow_mul _ _ _).symm
    _ ≤ c₀ ^ 𝔟 := pow_le_pow_of_le_one hc₀.le (min_le_right _ _) (by nlinarith)
    _ ≤ c ^ 𝔟 := pow_le_pow_left₀ hc₀.le (min_le_left _ _) _
    _ ≤ _ := h1
    _ ≤ _ := Φ.supDist_append_le _ _ _

theorem esc_of_sesc (h : Φ.SESC) : Φ.ESC := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, Frequently.of_forall h⟩

end IFS

end AnalyticESC
