module

public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace OAI

namespace Problem337

/-- The indices of a monotone sequence lying in a closed interval form one
possibly empty interval of indices. -/
theorem monotone_filter_range_eq_Ico {α : Type*} [LinearOrder α]
    (d : ℕ → α) (hd : Monotone d) (N : ℕ) (L R : α) :
    ∃ a b : ℕ, a ≤ b ∧ b ≤ N ∧
      (Finset.range N).filter (fun j => L ≤ d j ∧ d j ≤ R) = Finset.Ico a b := by
  classical
  let s := (Finset.range N).filter (fun j => L ≤ d j ∧ d j ≤ R)
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs
    have ha : a ∈ s := Finset.min'_mem _ hs
    have hb : b ∈ s := Finset.max'_mem _ hs
    have hab : a ≤ b := Finset.min'_le _ _ hb
    have hbN := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    refine ⟨a, b + 1, by omega, by omega, ?_⟩
    change s = Finset.Ico a (b + 1)
    ext j
    constructor
    · intro hj
      exact Finset.mem_Ico.mpr ⟨Finset.min'_le _ _ hj, Nat.lt_succ_iff.mpr (Finset.le_max' _ _ hj)⟩
    · intro hj
      rcases Finset.mem_Ico.mp hj with ⟨haj, hjb⟩
      have hjb' := Nat.lt_succ_iff.mp hjb
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hjb' hbN), ?_⟩
      exact ⟨(Finset.mem_filter.mp ha).2.1.trans (hd haj),
        (hd hjb').trans (Finset.mem_filter.mp hb).2.2⟩
  · refine ⟨0, 0, le_rfl, Nat.zero_le _, ?_⟩
    grind

/-- Cancellation on every interval transfers to one interval cut out by a
monotone increment sequence, without paying an extra term count. -/
theorem norm_sum_monotone_block_le {α : Type*} [LinearOrder α]
    (d : ℕ → α) (hd : Monotone d) (N : ℕ) (L R : α)
    (z : ℕ → ℂ) (C : ℝ)
    (hcancel : ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, L ≤ d j ∧ d j ≤ R) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ (Finset.range N).filter (fun j => L ≤ d j ∧ d j ≤ R), z j‖ ≤ C := by
  classical
  obtain ⟨a, b, hab, hbN, heq⟩ := monotone_filter_range_eq_Ico d hd N L R
  grind

/-- Good derivative indices in the integer cell labelled by `k`. -/
noncomputable def phaseGoodBlock (d : ℕ → ℝ) (N : ℕ) (β : ℝ) (k : ℤ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun j => (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β)

lemma phaseGoodBlock_pairwise_disjoint (d : ℕ → ℝ) (N : ℕ)
    (β : ℝ) (hβ : 0 < β) : Pairwise (fun k l : ℤ =>
      Disjoint (phaseGoodBlock d N β k) (phaseGoodBlock d N β l)) := by
  classical
  intro k l hkl
  apply Finset.disjoint_left.mpr
  intro j hjk hjl
  have hk := (Finset.mem_filter.mp hjk).2
  have hl := (Finset.mem_filter.mp hjl).2
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hgap : (k : ℝ) + 1 ≤ (l : ℝ) := by
      exact_mod_cast (by omega)
    linarith
  · have hgap : (l : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (by omega)
    linarith

/-- Partition a sum into good monotone derivative blocks and exceptional
indices. Each good integer cell pays just one cancellation bound. -/
theorem norm_sum_le_bad_card_add_good_blocks
    (d : ℕ → ℝ) (hd : Monotone d) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (K : Finset ℤ) (z : ℕ → ℂ) (C : ℝ)
    (hz : ∀ j < N, ‖z j‖ ≤ 1)
    (hcancel : ∀ k ∈ K, ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, z j‖ ≤
      ((Finset.range N \ K.biUnion (phaseGoodBlock d N β)).card : ℝ) +
        (K.card : ℝ) * C := by
  classical
  let G := K.biUnion (phaseGoodBlock d N β)
  have hsub : G ⊆ Finset.range N := by
    intro j hj
    obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp hjk).1
  have hdisj : (K : Set ℤ).PairwiseDisjoint (phaseGoodBlock d N β) := by
    intro k hk l hl hkl
    exact phaseGoodBlock_pairwise_disjoint d N β hβ hkl
  have hgood : ‖∑ j ∈ G, z j‖ ≤ (K.card : ℝ) * C := by
    change ‖∑ j ∈ K.biUnion (phaseGoodBlock d N β), z j‖ ≤ _
    rw [Finset.sum_biUnion hdisj]
    calc
      _ ≤ ∑ k ∈ K, ‖∑ j ∈ phaseGoodBlock d N β k, z j‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ K, C := by
        apply Finset.sum_le_sum
        intro k hk
        exact norm_sum_monotone_block_le d hd N ((k : ℝ) + β) ((k : ℝ) + 1 - β)
          z C (by grind)
      _ = _ := by simp
  have hbad : ‖∑ j ∈ Finset.range N \ G, z j‖ ≤ ((Finset.range N \ G).card : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N \ G, ‖z j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range N \ G, (1 : ℝ) := by
        apply Finset.sum_le_sum
        grind
      _ = _ := by simp
  rw [← Finset.sum_sdiff hsub]
  exact (norm_add_le _ _).trans (by linarith)

/-- The number of integer cells intersecting a real interval has the usual
length-plus-two bound. -/
theorem floor_interval_card_le (L U : ℝ) (hLU : L ≤ U) :
    ((Finset.Icc ⌊L⌋ ⌊U⌋).card : ℝ) ≤ U - L + 2 := by
  have hfloor := Int.floor_le_floor hLU
  have hcardZ := Int.card_Icc_of_le ⌊L⌋ ⌊U⌋ (by omega)
  have hcard : ((Finset.Icc ⌊L⌋ ⌊U⌋).card : ℝ) = (⌊U⌋ : ℝ) + 1 - (⌊L⌋ : ℝ) := by
    exact_mod_cast hcardZ
  rw [hcard]
  have hU := Int.floor_le U
  have hL := Int.lt_floor_add_one L
  linarith

/-- Outside the good integer cells, an increment is close to an integer. -/
theorem phase_bad_near_integer (d : ℕ → ℝ) (N : ℕ) (β L U : ℝ)
    (hrange : ∀ j < N, L ≤ d j ∧ d j ≤ U) (j : ℕ)
    (hj : j ∈ Finset.range N \ (Finset.Icc ⌊L⌋ ⌊U⌋).biUnion (phaseGoodBlock d N β)) :
    ∃ k : ℤ, |d j - (k : ℝ)| < β := by
  classical
  have hjN := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
  have hnotmem := (Finset.mem_sdiff.mp hj).2
  let k : ℤ := ⌊d j⌋
  have hk : k ∈ Finset.Icc ⌊L⌋ ⌊U⌋ :=
    Finset.mem_Icc.mpr ⟨Int.floor_le_floor (by grind),
      Int.floor_le_floor (by grind)⟩
  have hnot : ¬((k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) := by
    intro hgood
    apply hnotmem
    exact Finset.mem_biUnion.mpr ⟨k, hk,
      Finset.mem_filter.mpr (by grind)⟩
  have hklo : (k : ℝ) ≤ d j := Int.floor_le _
  have hkhi : d j < (k : ℝ) + 1 := Int.lt_floor_add_one _
  by_cases hleft : d j - (k : ℝ) < β
  · grind
  · have hleft' : β ≤ d j - (k : ℝ) := le_of_not_gt hleft
    have hright : (k : ℝ) + 1 - β < d j := by
      apply lt_of_not_ge
      intro hupper
      exact by grind
    refine ⟨k + 1, ?_⟩
    grind

noncomputable def nearIntegerIndices (d : ℕ → ℝ) (N : ℕ) (β : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun j => ∃ k : ℤ, |d j - (k : ℝ)| < β)

/-- A second-derivative partition estimate, separating the packing estimate
for bad points from the cancellation estimate on good intervals. -/
theorem norm_sum_le_near_integer_bound
    (d : ℕ → ℝ) (hd : Monotone d) (N : ℕ) (β L U : ℝ) (hβ : 0 < β)
    (hLU : L ≤ U) (hrange : ∀ j < N, L ≤ d j ∧ d j ≤ U)
    (z : ℕ → ℂ) (B C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ j < N, ‖z j‖ ≤ 1)
    (hbad : ((nearIntegerIndices d N β).card : ℝ) ≤ B)
    (hcancel : ∀ k ∈ Finset.Icc ⌊L⌋ ⌊U⌋, ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, z j‖ ≤ B + (U - L + 2) * C := by
  classical
  have hsub : Finset.range N \ (Finset.Icc ⌊L⌋ ⌊U⌋).biUnion (phaseGoodBlock d N β) ⊆
      (Finset.range N).filter (fun j => ∃ k : ℤ, |d j - (k : ℝ)| < β) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨by grind,
      phase_bad_near_integer d N β L U hrange j hj⟩
  have hcard : ((Finset.range N \ (Finset.Icc ⌊L⌋ ⌊U⌋).biUnion (phaseGoodBlock d N β)).card : ℝ) ≤
      ((nearIntegerIndices d N β).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hbad' := hcard.trans hbad
  have hmain := norm_sum_le_bad_card_add_good_blocks d hd N β hβ
    (Finset.Icc ⌊L⌋ ⌊U⌋) z C hz hcancel
  exact hmain.trans (add_le_add hbad' (mul_le_mul_of_nonneg_right (floor_interval_card_le L U hLU) hC))

/-- Local monotonicity on the sampled range suffices for the partition bound;
extend by a constant after the last sampled increment. -/
theorem norm_sum_le_near_integer_bound_local
    (d : ℕ → ℝ) (N : ℕ) (hd : MonotoneOn d (Set.Iio N))
    (β L U : ℝ) (hβ : 0 < β) (hLU : L ≤ U)
    (hrange : ∀ j < N, L ≤ d j ∧ d j ≤ U)
    (z : ℕ → ℂ) (B C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ j < N, ‖z j‖ ≤ 1)
    (hbad : ((nearIntegerIndices d N β).card : ℝ) ≤ B)
    (hcancel : ∀ k ∈ Finset.Icc ⌊L⌋ ⌊U⌋, ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, z j‖ ≤ B + (U - L + 2) * C := by
  classical
  let e : ℕ → ℝ := fun j => d (min j (N - 1))
  have heq (j : ℕ) (hj : j < N) : e j = d j := by
    dsimp [e]
    rw [min_eq_left (by omega)]
  have hem : Monotone e := by
    intro i j hij
    by_cases hN : N = 0
    · grind
    · apply hd
      · grind
      · grind
      omega
  have hindices : nearIntegerIndices e N β = nearIntegerIndices d N β := by
    ext j
    by_cases hj : j < N
    · simp only [nearIntegerIndices, Finset.mem_filter, heq j hj]
    · simp only [nearIntegerIndices, Finset.mem_filter, Finset.mem_range, hj, false_and]
  apply norm_sum_le_near_integer_bound e hem N β L U hβ hLU
    (fun j hj => by grind) z B C hC hz
  · grind
  grind

end Problem337

end OAI
