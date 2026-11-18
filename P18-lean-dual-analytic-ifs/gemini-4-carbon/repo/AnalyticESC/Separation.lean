module

public import AnalyticESC.Basic

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

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

private theorem zero_mem_I : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩

/-- Compositions map real points of `I` into the closed unit disc. -/
private theorem norm_comp_ofReal_le_one (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.comp w x‖ ≤ 1 := by
  rw [Φ.comp_ofReal w hx, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have := Φ.re_comp_mem_I w hx
  constructor <;> linarith [this.1, this.2]

theorem tendsto_natProj (w : ℕ → Fin N) :
    Tendsto (fun n => (Φ.comp (List.ofFn fun k : Fin n => w k) 0).re) atTop (𝓝 (Φ.natProj w)) := by
  have hz0 : ((0 : ℝ) : ℂ) ∈ nbhd ε := ofReal_mem_nbhd Φ.ε_pos zero_mem_I
  have hu : ∀ n, dist (Φ.comp (List.ofFn fun k : Fin n => w k) 0).re
      (Φ.comp (List.ofFn fun k : Fin (n + 1) => w k) 0).re ≤ 1 * Φ.cmax ^ n := by
    intro n
    have hsplit : (List.ofFn fun k : Fin (n + 1) => w k) =
        (List.ofFn fun k : Fin n => w k) ++ [w n] := by
      rw [List.ofFn_succ', List.concat_eq_append]
      simp
    rw [hsplit, Φ.comp_append, Function.comp_apply, Real.dist_eq, one_mul]
    set v := List.ofFn fun k : Fin n => w k
    have hv : v.length = n := List.length_ofFn
    have hz0' : (0 : ℂ) ∈ nbhd ε := by simpa using hz0
    have hz1 : Φ.comp [w n] 0 ∈ nbhd ε := Φ.mapsTo_comp [w n] hz0'
    have h1 : ‖Φ.comp [w n] 0‖ ≤ 1 := by
      simpa using Φ.norm_comp_ofReal_le_one [w n] zero_mem_I
    calc |(Φ.comp v 0).re - (Φ.comp v (Φ.comp [w n] 0)).re|
        = |(Φ.comp v 0 - Φ.comp v (Φ.comp [w n] 0)).re| := by rw [Complex.sub_re]
      _ ≤ ‖Φ.comp v 0 - Φ.comp v (Φ.comp [w n] 0)‖ := Complex.abs_re_le_norm _
      _ ≤ Φ.cmax ^ v.length * ‖0 - Φ.comp [w n] 0‖ := Φ.norm_comp_sub_le v hz0' hz1
      _ ≤ Φ.cmax ^ n * 1 := by
          rw [hv, zero_sub, norm_neg]
          exact mul_le_mul_of_nonneg_left h1 (pow_nonneg Φ.cmax_nonneg n)
      _ = Φ.cmax ^ n := mul_one _
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric Φ.cmax 1
    Φ.cmax_lt_one hu)
  exact tendsto_nhds_limUnder ⟨a, ha⟩

theorem attractor_subset_I : Φ.attractor ⊆ I := by
  rintro _ ⟨w, rfl⟩
  exact isClosed_Icc.mem_of_tendsto (Φ.tendsto_natProj w)
    (Eventually.of_forall fun n => by simpa using Φ.re_comp_mem_I _ zero_mem_I)

private theorem bddAbove_supDist (i j : List (Fin N)) :
    BddAbove (range fun x : I => ‖Φ.comp i ((x : ℝ) : ℂ) - Φ.comp j ((x : ℝ) : ℂ)‖) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨x, rfl⟩
  calc _ ≤ ‖Φ.comp i ((x : ℝ) : ℂ)‖ + ‖Φ.comp j ((x : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (Φ.norm_comp_ofReal_le_one i x.2) (Φ.norm_comp_ofReal_le_one j x.2)
    _ = 2 := by norm_num

private theorem norm_le_supDist (i j : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.comp i x - Φ.comp j x‖ ≤ Φ.supDist i j :=
  le_ciSup (f := fun x : I => ‖Φ.comp i ((x : ℝ) : ℂ) - Φ.comp j ((x : ℝ) : ℂ)‖)
    (Φ.bddAbove_supDist i j) ⟨x, hx⟩

/-- Appending a common suffix does not increase the distance. -/
private theorem supDist_append_le (i j u : List (Fin N)) :
    Φ.supDist (i ++ u) (j ++ u) ≤ Φ.supDist i j := by
  have : Nonempty I := ⟨⟨0, zero_mem_I⟩⟩
  refine ciSup_le fun x => ?_
  have hx := x.2
  rw [Φ.comp_append, Φ.comp_append, Function.comp_apply, Function.comp_apply,
    Φ.comp_ofReal u hx]
  exact Φ.norm_le_supDist i j (Φ.re_comp_mem_I u hx)

/-- Without the SESC, close pairs occur at arbitrarily high levels. -/
theorem exists_close_pair_ge (h : ¬ Φ.SESC) {c : ℝ} (hc : 0 < c) (B : ℕ) :
    ∃ n, B ≤ n ∧ ∃ i j : Fin n → Fin N, i ≠ j ∧
      Φ.supDist (List.ofFn i) (List.ofFn j) < c ^ n := by
  by_contra hcon
  push Not at hcon
  apply h
  set c₀ := min c 1
  have hc₀ : 0 < c₀ := lt_min hc one_pos
  have hc₀1 : c₀ ≤ 1 := min_le_right _ _
  refine ⟨c₀ ^ (B + 1), pow_pos hc₀ _, fun n i j hij => ?_⟩
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
  have h1 := hcon (n + B) (Nat.le_add_left B n) _ _ hne
  rw [List.ofFn_fin_append, List.ofFn_fin_append] at h1
  calc (c₀ ^ (B + 1)) ^ n = c₀ ^ ((B + 1) * n) := (pow_mul _ _ _).symm
    _ ≤ c₀ ^ (n + B) := pow_le_pow_of_le_one hc₀.le hc₀1 (by nlinarith)
    _ ≤ c ^ (n + B) := pow_le_pow_left₀ hc₀.le (min_le_left _ _) _
    _ ≤ _ := h1
    _ ≤ _ := Φ.supDist_append_le _ _ _

theorem esc_of_sesc (h : Φ.SESC) : Φ.ESC := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, Frequently.of_forall h⟩

end IFS

end AnalyticESC
