module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoSpec2
public import Chazelle.Core.SweepEvOrgM

/-!
# The sweep RAM (WP-D), answers: the cost of the query loop

* `qPt_end`: the point of an endpoint query `j < 2 K₂` of side `1` is the endpoint `endOrigin j`;
* `brute_card`: at most `5` queries of side `1` are brute-force queries (`TopCountSpec`, at most
  `3` queries after the endpoint queries);
* `qCost_sum`: the sum of the query costs.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep

@[expose] public section

/-- **The point of an endpoint query** is the endpoint. -/
theorem qPt_end {J : Merge.Junction} {P : Polygon} {N₂ : NF} (hN : IsNF (chainModel J.right) (Qof P) N₂)
    (L₁ : List (ℕ × ℕ × ℕ)) {j : ℕ} (hj : j < 2 * N₂.nChords) :
    qPt J P 1 (sweepEndQ N₂.chords ++ L₁) j = endOrigin J (Qof P) N₂ j := by
  Ξ (endOrigin_eq J hN hj).1
  have hlen : (sweepEndQ N₂.chords).length = 2 * N₂.nChords := by
    Θ sweepEndQ, NF.nChords
  have hget : (sweepEndQ N₂.chords ++ L₁).getD j (0, 0, 0) =
      (let r := N₂.chords.getD (j / 2) ⟨0, 0, 0, 0, 0⟩
       if j % 2 = 0 then (r.lp, r.h + 1, 1) else (r.rp, r.h + 1, 0)) := by
    Ξ List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; exact hj)
    simp only [sweepEndQ, List.getElem?_map, List.getElem?_range (show j < 2 * N₂.chords.length
      from hj), Option.map_some, Option.getD_some]
  unfold qPt
  Ξ hget
  have hsc : sideChain J 1 = J.right := by unfold sideChain; rw [ite_eq_right (⊛)]
  Ξ hsc
  unfold endPos NF.chord CRec.lpos CRec.rpos
  by_cases h : j % 2 = 0 <;> simp [h]

open Classical in
/-- **At most five brute-force queries.** -/
theorem brute_card (hT : TopCountSpec) {P : Polygon} {J : Merge.Junction} {N₂ : NF}
    (hG : GoodEnv P) (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N₂)
    {L : List (ℕ × ℕ × ℕ)} {i : ℕ}
    (hend : i = 1 → ∃ L₁ : List (ℕ × ℕ × ℕ), L = sweepEndQ N₂.chords ++ L₁ ∧ L₁.length ≤ 3) :
    ((Finset.range L.length).filter
      (fun j => i = 1 ∧ BruteQ J N₂ j (qPt J P i L j))).card ≤ 5 := by
  by_cases hi : i = 1
  swap
  · rw [Finset.filter_false_of_mem (fun j _ h => hi h.1)]; simp
  obtain ⟨L₁, rfl, hL₁⟩ := hend hi
  subst hi
  have hlen : (sweepEndQ N₂.chords ++ L₁).length = 2 * N₂.nChords + L₁.length := by
    Θ sweepEndQ, NF.nChords
  set K := 2 * N₂.nChords with hK
  have hsub : (Finset.range (sweepEndQ N₂.chords ++ L₁).length).filter
      (fun j => 1 = 1 ∧ BruteQ J N₂ j (qPt J P 1 (sweepEndQ N₂.chords ++ L₁) j)) ⊆
      Finset.Ico K (K + L₁.length) ∪
        (Finset.range K).filter (fun j => endOrigin J (Qof P) N₂ j = J.right.top) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, hlen] at hj
    obtain ⟨hjL, -, hb⟩ := hj
    Ξ Finset.mem_union, Finset.mem_Ico, Finset.mem_filter, Finset.mem_range
    rcases hb with hb | hb
    · exact Or.inl ⟨hb, hjL⟩
    · by_cases hjK : K ≤ j
      · exact Or.inl ⟨hjK, hjL⟩
      · push Not at hjK
        refine Or.inr ⟨hjK, ?_⟩
        rw [← qPt_end hN L₁ hjK]; exact hb
  have h2 : ((Finset.range K).filter (fun j => endOrigin J (Qof P) N₂ j = J.right.top)).card ≤ 2 := by
    have := hT P J N₂ hG hP hN
    refine le_trans (le_of_eq ?_) this
    show (Multiset.filter _ (Multiset.range K)).card = _
    Ξ Multiset.range, Multiset.filter_coe, Multiset.coe_card
  calc _ ≤ (Finset.Ico K (K + L₁.length) ∪
        (Finset.range K).filter (fun j => endOrigin J (Qof P) N₂ j = J.right.top)).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.Ico K (K + L₁.length)).card +
        ((Finset.range K).filter (fun j => endOrigin J (Qof P) N₂ j = J.right.top)).card :=
      Finset.card_union_le _ _
    _ ≤ 5 := by rw [Nat.card_Ico]; omega

open Classical in
/-- **The sum of the query costs.** -/
theorem qCost_sum (hT : TopCountSpec) {κ : ℕ → ℕ} {F : ℕ → ℕ} {c₀ : Config} {P : Polygon}
    {J : Merge.Junction} {N₁ N₂ : NF} (hG : GoodEnv P) (hP : J.P.Simple)
    (hN : IsNF (chainModel J.right) (Qof P) N₂) {L : List (ℕ × ℕ × ℕ)} {i : ℕ}
    (hend : i = 1 → ∃ L₁ : List (ℕ × ℕ × ℕ), L = sweepEndQ N₂.chords ++ L₁ ∧ L₁.length ≤ 3) :
    ∑ j ∈ Finset.range L.length, qCost κ F c₀ J P N₁ N₂ L i j ≤
      L.length * (κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1)) +
        5 * (κ (c₀.nreg (sw 6)) * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1)) := by
  unfold qCost
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have := brute_card hT hG hP hN hend (i := i)
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ this) _

end

end SweepIo

end Chazelle.Core
