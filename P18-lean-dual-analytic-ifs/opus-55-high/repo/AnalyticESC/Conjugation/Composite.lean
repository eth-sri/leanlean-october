module

public import AnalyticESC.Conjugation.Koenigs
public import AnalyticESC.Conjugation.Basic

public section

set_option hygiene false
local notation "𝔞" => hS hz
local notation "𝖒" => w ∘ Fin.rev

local notation "𝖑" => ε / 4

/-!
# Compositions and periodic words

Compositions `f_w` along nonempty words lie in the class for a smaller `ε`; their functions
`Ĥ_{f_w}` of (5.1) are dual natural projections of periodic words; and if the dual natural
projections of the constant words agree, then all dual natural projections agree (the remark
after Theorem 1.12).
-/

namespace AnalyticESC

variable {m : ℕ}

open Set Metric Filter Topology

namespace Word


/-- A periodic word is its period followed by itself. -/
theorem composite_inf_periodic_eq_prepend (hm : 0 < m) (v : Fin m → Fin N) :
    inf (periodic hm v) = (inf (periodic hm v)).prepend (List.ofFn v) := by
  show _ = inf fun n => if h : n < (List.ofFn v).length then _ else _
  congr 1
  funext n
  simp
  split_ifs with hn
  · simp [periodic, Nat.mod_eq_of_lt hn]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + m := ⟨n - m, by omega⟩
    simp [periodic]

end Word

/-- `List.ofFn (w ∘ Fin.rev) = (List.ofFn w)^←`. -/
theorem composite_ofFn_comp_rev (w : Fin m → α) :
    List.ofFn 𝖒 = (List.ofFn w).reverse := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  grind

/-- A bounded solution of `h(z) = R(z) + g'(z) h(g(z))` is unique when `g` maps `S` into itself
with `|g'| ≤ c < 1` on `S`. -/
theorem composite_eqOn_of_functional_eq {g R A B : ℂ → ℂ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hg : MapsTo g S S) (hgd : ∀ z ∈ S, ‖deriv g z‖ ≤ c)
    (hA : ∀ z ∈ S, A z = R z + deriv g z * A (g z))
    (hB : ∀ z ∈ S, B z = R z + deriv g z * B (g z)) (hK : ∀ z ∈ S, ‖A z - B z‖ ≤ K) :
    ∀ z ∈ S, A z = B z := by
  have key : ∀ n, ∀ z ∈ S, ‖A z - B z‖ ≤ c ^ n * K := by
    intro n
    induction n with
    | zero => simpa using hK
    | succ n ih =>
      intro z hz
      rw [hA z hz, hB z hz, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, pow_succ', mul_assoc]
      exact mul_le_mul (hgd z hz) (ih _ (hg hz)) (norm_nonneg _) hc0
  intro z hz
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const K) fun n => key n z hz))

namespace IFS

variable (Φ : IFS N ε)

/-- Compositions along nonempty words lie in the class for some `ε' > 0`. -/
theorem inClass_comp (hw : w ≠ []) :
    InClass 𝖑 (Φ.comp w) := by
  have hε := Φ.ε_pos
  have hc : Φ.cmax ^ w.length < 1 :=
    pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.2 hw).ne'
  have hcl : 𝔹 𝖑 ⊆ 𝔹 ε := closure_mono (nbhd_mono (by linarith))
  refine ⟨(Φ.differentiableOn_comp w).mono (nbhd_mono (by linarith)),
    fun x hx => Φ.im_comp_ofReal w ((nbhd_mono (by linarith)) hx), fun x hx => Φ.re_comp_mem_I w hx, ?_,
    fun z hz => Φ.deriv_comp_ne_zero w (hcl hz),
    fun z hz => (Φ.norm_deriv_comp_le w (hcl hz)).trans_lt hc⟩
  intro z hz
  have h1 : z ∈ cthickening 𝖑 Iℂ :=
    closure_thickening_subset_cthickening _ _ hz
  rw [isCompact_image_I.isClosed.cthickening_eq_biUnion_closedBall (by positivity)] at h1
  obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := mem_iUnion₂.1 h1
  rw [mem_closedBall, dist_eq_norm] at hzx
  have h2 := Φ.norm_comp_sub_le w (ball_subset_nbhd hx (by rw [mem_ball, dist_eq_norm]; linarith)) (ofReal_mem_nbhd hε hx)
  rw [Φ.comp_ofReal w hx] at h2
  refine ball_subset_nbhd (Φ.re_comp_mem_I w hx) ?_
  rw [mem_ball, dist_eq_norm]
  calc _ ≤ Φ.cmax ^ w.length * ‖z - x‖ := h2
    _ ≤ Φ.cmax ^ w.length * 𝖑 :=
        mul_le_mul_of_nonneg_left hzx (pow_nonneg Φ.cmax_nonneg _)
    _ < ε / 4 := by simp_all

/-- `Ĥ_{f_w} = H_{(w^←)^∞}` on `[0,1]`, where `w^←` is the reversed word: both are bounded
solutions of `h = f_w''/f_w' + f_w' · h ∘ f_w`. -/
theorem hatH_comp_eq_dualProj (hm : 0 < m) (w : Fin m → Fin N) :
    Ɐ hatH (Φ.comp (List.ofFn w)) x = Φ.dualProj (.inf (periodic hm 𝖒)) x := by
  have hf := Φ.inClass_comp (w := List.ofFn w) (by aesop)
  have h4 : 0 < ε / 4 := by linarith [Φ.ε_pos]
  have hS : nbhd 𝖑 ⊆ 𝔹 ε := (nbhd_mono (by linarith)).trans subset_closure
  obtain ⟨M, -, hM⟩ := Φ.exists_norm_dualProj_le
  obtain ⟨M', -, hM'⟩ := (koenigsIFS h4 hf).exists_norm_dualProj_le
  intro x hx
  refine composite_eqOn_of_functional_eq (pow_nonneg Φ.cmax_nonneg m)
    (pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one hm.ne') (fun z hz => hf.mapsTo (subset_closure hz))
    (fun z hz => by simpa using Φ.norm_deriv_comp_le (List.ofFn w) 𝔞)
    (fun z hz => hatH_eq_add h4 hf hz) (fun z hz => ?_) (K := M' + M) (fun z hz => ?_) _
    (ofReal_mem_nbhd h4 hx)
  · have h1 := Φ.dualProj_prepend (List.ofFn 𝖒) (.inf (periodic hm 𝖒))
      𝔞
    rw [← Word.composite_inf_periodic_eq_prepend hm 𝖒, composite_ofFn_comp_rev,
      List.reverse_reverse] at h1
    rw [← Φ.dualProj_fin_reverse _ 𝔞]
    exact h1
  · rw [hatH_eq_dualProj h4 hf]
    exact (norm_sub_le _ _).trans (add_le_add (hM' _ _ (subset_closure hz)) (hM _ _ 𝔞))

end IFS

end AnalyticESC
