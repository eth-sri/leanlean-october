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
  rw [Φ.comp_ofReal w hx, Complex.norm_real, Real.norm_of_nonneg (Φ.re_comp_mem_I w hx).1]
  exact (Φ.re_comp_mem_I w hx).2

theorem tendsto_natProj (w : ℕ → Fin N) :
    Tendsto (fun n => (Φ.comp (List.ofFn fun k : Fin n => w k) 0).re) atTop (𝓝 (Φ.natProj w)) := by
  have hu (n : ℕ) : dist (Φ.comp (List.ofFn fun k : Fin n => w k) 0).re
      (Φ.comp (List.ofFn fun k : Fin (n + 1) => w k) 0).re ≤ 1 * Φ.cmax ^ n := by
    rw [List.ofFn_succ', List.concat_eq_append, Φ.comp_append, Function.comp_apply,
      ← Complex.ofReal_zero, Φ.comp_ofReal [w (Fin.last n)] zero_mem_I, Real.dist_eq, one_mul]
    exact (Φ.abs_re_comp_sub_le _ zero_mem_I (Φ.re_comp_mem_I _ zero_mem_I)).trans_eq (by simp)
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric Φ.cmax 1 Φ.cmax_lt_one hu))

theorem attractor_subset_I : Φ.attractor ⊆ I := by
  rintro _ ⟨w, rfl⟩
  exact isClosed_Icc.mem_of_tendsto (Φ.tendsto_natProj w)
    (Eventually.of_forall fun n => by simpa using Φ.re_comp_mem_I _ zero_mem_I)

/-- Two points of `I` fixed by `f_w`, for a nonempty word `w`, are equal. -/
theorem eq_of_fixed {w : List (Fin N)} (hw : w ≠ []) {x y : ℝ} (hx : x ∈ I)
    (hy : y ∈ I) (hfx : (Φ.comp w x).re = x) (hfy : (Φ.comp w y).re = y) : x = y := by
  have hle := Φ.abs_re_comp_sub_le_mul w hx hy
  rw [hfx, hfy] at hle
  have hc : Φ.cmax ^ w.length < 1 :=
    pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.2 hw).ne'
  by_contra hne
  nlinarith [abs_pos.2 (sub_ne_zero.2 hne)]

theorem natProj_prepend (a : List (Fin N)) (w : ℕ → Fin N) :
    Φ.natProj (fun n => if h : n < a.length then a[n] else w (n - a.length)) =
      (Φ.comp a (Φ.natProj w)).re := by
  set v : ℕ → Fin N := fun n => if h : n < a.length then a[n] else w (n - a.length)
  have hlist (n : ℕ) : (List.ofFn fun k : Fin (n + a.length) => v k) =
      a ++ List.ofFn fun k : Fin n => w k :=
    List.ext_getElem (by simp [Nat.add_comm]) fun l h1 h2 => by
      simp only [List.getElem_ofFn, List.getElem_append, v]
  have hc : ContinuousAt (fun t : ℝ => (Φ.comp a t).re) (Φ.natProj w) :=
    Complex.continuous_re.continuousAt.comp ((Φ.differentiableAt_comp a
      (subset_closure (ofReal_mem_nbhd Φ.ε_pos (Φ.attractor_subset_I ⟨w, rfl⟩)))).continuousAt.comp
      Complex.continuous_ofReal.continuousAt)
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat a.length).2 (Φ.tendsto_natProj v))
    ((hc.tendsto.comp (Φ.tendsto_natProj w)).congr fun n => ?_)
  rw [Function.comp_apply, hlist n, Φ.comp_append, Function.comp_apply, ← Complex.ofReal_zero,
    ← Φ.comp_ofReal _ zero_mem_I]

/-- `π(ω) = f_{ω₁ ⋯ ω_k}(π(σ^k ω))`, where `σ` is the left shift. -/
theorem natProj_eq_comp_prefix (ω : ℕ → Fin N) (k : ℕ) :
    Φ.natProj ω =
      (Φ.comp (List.ofFn fun j : Fin k => ω j) (Φ.natProj fun j => ω (j + k))).re := by
  rw [← Φ.natProj_prepend]
  congr 1; funext n; simp only [List.length_ofFn, List.getElem_ofFn]
  split_ifs with h <;> [rfl; exact congrArg ω (by omega)]

/-- `π(ω) = f_{ω₀}(π(σω))`, where `σ` is the left shift. -/
theorem natProj_eq_realMap (ω : ℕ → Fin N) :
    Φ.natProj ω = Φ.realMap (ω 0) (Φ.natProj fun j => ω (j + 1)) := by
  rw [Φ.natProj_eq_comp_prefix ω 1]
  simp [realMap]

theorem norm_le_supDist (i j : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.comp i x - Φ.comp j x‖ ≤ Φ.supDist i j := by
  refine le_ciSup (f := fun x : I => ‖Φ.comp i ((x : ℝ) : ℂ) - Φ.comp j ((x : ℝ) : ℂ)‖)
    ⟨1 + 1, ?_⟩ ⟨x, hx⟩
  rintro _ ⟨y, rfl⟩
  exact (norm_sub_le _ _).trans
    (add_le_add (Φ.norm_comp_ofReal_le_one i y.2) (Φ.norm_comp_ofReal_le_one j y.2))

/-- Appending a common suffix does not increase the distance. -/
private theorem supDist_append_le (i j u : List (Fin N)) :
    Φ.supDist (i ++ u) (j ++ u) ≤ Φ.supDist i j := by
  have : Nonempty I := ⟨⟨0, zero_mem_I⟩⟩
  refine ciSup_le fun x => ?_
  have hx := x.2
  change ‖Φ.comp (i ++ u) x - Φ.comp (j ++ u) x‖ ≤ Φ.supDist i j
  rw [Φ.comp_append, Φ.comp_append, Function.comp_apply, Function.comp_apply,
    Φ.comp_ofReal u hx]
  exact Φ.norm_le_supDist i j (Φ.re_comp_mem_I u hx)

/-- Without the SESC, close pairs occur at arbitrarily high levels. -/
theorem exists_close_pair_ge (h : ¬ Φ.SESC) {c : ℝ} (hc : 0 < c) (B : ℕ) :
    ∃ n, B ≤ n ∧ ∃ i j : Fin n → Fin N, i ≠ j ∧
      Φ.supDist (List.ofFn i) (List.ofFn j) < c ^ n := by
  by_contra! hcon
  apply h
  set c₀ := min c 1
  have hc₀ : 0 < c₀ := lt_min hc one_pos
  refine ⟨c₀ ^ (B + 1), pow_pos hc₀ _, fun n i j hij => ?_⟩
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => hij (by subst h0; exact Subsingleton.elim i j)
  let u : Fin B → Fin N := fun _ => i ⟨0, hn⟩
  have h1 := hcon (n + B) (Nat.le_add_left B n) (Fin.append i u) (Fin.append j u) fun he => by
    have he' := congrArg List.ofFn he
    rw [List.ofFn_fin_append, List.ofFn_fin_append] at he'
    exact hij (List.ofFn_injective (List.append_cancel_right he'))
  rw [List.ofFn_fin_append, List.ofFn_fin_append] at h1
  exact (pow_mul c₀ (B + 1) n).symm.trans_le
    ((pow_le_pow_of_le_one hc₀.le (min_le_right _ _) (by nlinarith)).trans
      ((pow_le_pow_left₀ hc₀.le (min_le_left _ _) _).trans
        (h1.trans (Φ.supDist_append_le _ _ _))))

theorem esc_of_sesc (h : Φ.SESC) : Φ.ESC :=
  let ⟨c, hc, h⟩ := h; ⟨c, hc, Frequently.of_forall h⟩

end IFS

end AnalyticESC
