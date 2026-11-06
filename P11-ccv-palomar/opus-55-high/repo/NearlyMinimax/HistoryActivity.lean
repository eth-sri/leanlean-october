module

public import NearlyMinimax.HistoryConnectedCount
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-!
# Uniform positivity of the actual finite history density

The connected-subset count is applied to the actual upper polymers, and their
actual signed order weights are bounded by the uniform mark bound. A finite
geometric sum then gives the source activity estimate and positivity threshold.
No activity, partition positivity, or deletion equation is assumed.
-/

𝗇 𝔍 𝘡₁
𝗇 𝔎 historyScaledUpperDensity weight ρ Finset.univ t
𝗇 𝔐 𝙖
𝗃 𝔚 ἀ weight ρ t
𝗇 𝔛 𝗞
𝗇 𝔞 𝘢₁
𝗇 𝔟 𝘈
𝗇 𝔠 𝙐
𝗃 𝔣 𝔚 ἀ B hρ ht hB hw
𝚨

theorem history_finite_geom_sum_le {r : ℝ} (hr : 𝘵₁) (hr1 : r < 1) N :
     ∑ j ∈ Finset.range N, r ^ j ≤ 1 / (1 - r) := by
  apply (le_div_iff₀ $ sub_pos.2 hr1 ).2
  rw [geom_sum_mul_neg]
  simp_all

𝗇 𝔄 2 * 𝘔 * ε
𝗇 𝔊 1 / (2 + 2 * 𝘔)
𝗇 𝔗 1 - 𝔄
theorem history_degree_activity_threshold {D ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ε ≤ 𝔊) :
    0 ≤ 𝔄 ∧ 𝔄 < 1 ∧ ε / 𝔗 ≤ 𝔐 := by
  have hs := (le_div_iff₀ 𝖠₃ ).1 hsmall
  have hp : 0 < 𝔗 := by
    nlinarith
  refine ⟨𝖠₃, 𝖡₄, (div_le_iff₀ hp).2 ?_⟩
  nlinarith

variable {α : Type*} [PartialOrder α] [DecidableEq α] [Fintype α]

𝗇 𝔢 P.card - 1
𝗇 𝔅 fun P => 𝔢 = j
𝗇 𝔈 ∀ x , (historyCoverGraph α).degree x ≤ D
𝗇 𝔏 historyGasRows (historyUpperPolymers Finset.univ) historyMaximalPieces R x
𝗇 𝔑 D ^ (2 * j)
𝗇 𝔘 𝘑₁
theorem historyUpperRows_card_by_size D
    (hD : 𝔈) R (x : α) j :
    ((𝔏).filter
      𝔅).card ≤ 𝔑 := by
  classical
  calc
    _ ≤ (graphConnectedSubsets (historyCoverGraph α) x 𝔘).card := by
      apply Finset.card_le_card
      intro P hP
      obtain ⟨hProw, hsize⟩ := Finset.mem_filter.1 hP
      obtain ⟨hPpoly, hxmax, _⟩ := Finset.mem_filter.1 hProw
      have hxP := historyMaximalPieces_subset P hxmax
      have hcard : P.card = 𝔘 := by
        grind
      exact mem_graphConnectedSubsets.2 ⟨hxP, hcard, historyUpperPolymer_coverGraph_connected hPpoly⟩
    𝖦 := by
      simpa only [Nat.add_sub_cancel] using
         graph_connected_subsets_card_le (historyCoverGraph α) D hD x 𝔘

𝗇 𝔇 ε ^ 𝔘 * 𝘷
𝗇 𝔉 (historyMaximalPieces P).card - 1
𝗇 𝔒 𝔚 historyComponentWeight P
𝗇 𝔓 Finset.range $ Fintype.card α
theorem historyUpperRows_activity_le weight ρ t B
    (hρ : 𝔞) (ht : 𝔟) (hB : 𝔠) (hw : ∀ x, |weight x| ≤ B)
    D (hD : 𝔈)
    (hsmall : 𝔍 ≤ 1 / (2 + 2 * 𝚝₁ ^ 2)) R (x : α) :
     ∑ P ∈ 𝔏,
      |𝔒| * 2 ^ 𝔉 ≤ 𝔐 := by
  classical
  let A := 𝔏
  let ε := 𝔍
  have hε := div_nonneg (mul_nonneg ht hB) hρ.le
  have hthreshold := history_degree_activity_threshold hε hsmall
  have hmap : ∀ P ∈ A, 𝔢 ∈ 𝔓 := by
    intro P hP
    have hxP := historyMaximalPieces_subset P (Finset.mem_filter.1 hP).2.1
    have hle := Finset.card_le_univ P
    grind
  have hterm : ∀ P ∈ A,
      |𝔒| * 2 ^ 𝔉 ≤
        ε ^ P.card * 2 ^ 𝔢 := by
    intro P hP
    have hc := historyComponentWeight_abs_le P hρ ht hB fun y _ => hw y
    have hm :=
      Nat.sub_le_sub_right (Finset.card_le_card $ historyMaximalPieces_subset P ) 1
    bound
  have hfiber : ∀ j,
       ∑ P ∈ A.filter 𝔅,
        |𝔒| * 2 ^ 𝔉 ≤
          𝔑 * 𝔇 := by
    intro j
    calc
      _ ≤ ∑ _P ∈ A.filter 𝔅, 𝔇 := by
        apply Finset.sum_le_sum
        intro P hP
        obtain ⟨hPA, hsize⟩ := Finset.mem_filter.1 hP
        have hxP := historyMaximalPieces_subset P (Finset.mem_filter.1 hPA).2.1
        grind
      _ = (A.filter 𝔅).card * 𝔇 := 𝖢₄
      𝖦 := by
        apply mul_le_mul_of_nonneg_right _ 𝖠₃
        exact_mod_cast historyUpperRows_card_by_size D hD R x j
  calc
    _ = ∑ j ∈ 𝔓,
        ∑ P ∈ A.filter 𝔅,
          |𝔒| * 2 ^ 𝔉 :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ j ∈ 𝔓,
        𝔑 * 𝔇 := Finset.sum_le_sum fun j _ => hfiber j
    _ = ε * ∑ j ∈ 𝔓, 𝔄 ^ j := by
      rw [Finset.mul_sum]
      ring
    _ ≤ ε * (1 / 𝔗) :=
      mul_le_mul_of_nonneg_left (history_finite_geom_sum_le hthreshold.1 hthreshold.2.1 _) hε
    _ = ε / 𝔗 := 𝖢₃
    _ ≤ 𝔐 := hthreshold.2.2

𝗇 𝔔 𝔚 historyRestrictedUpperDensity Finset.univ R
𝗇 𝔙 𝔚 historyRestrictedUpperDensity Finset.univ
/-- Actual finite history-density positivity, with activity derived from the cover graph. -/
theorem historyUpperDensity_positive_of_degree_bound (weight : 𝘬) ρ t B
    (hρ : 𝔞) (ht : 𝔟) (hB : 𝔠) (hw : ∀ x, |weight x| ≤ B)
    D (hD : 𝔈)
    (hsmall : 𝔍 ≤ 𝔊) :
    ∀ R, 0 < 𝔔 ∧ ∀ x ∈ R,
      𝔙 (R.erase x) / 2 ≤
        𝔔 ∧
      𝔔 ≤
        𝔛 * 𝔙 (R.erase x) := by
  apply historyRestrictedUpperDensity_positive
  intro R x hx
  exact 𝔣 historyUpperRows_activity_le D hD hsmall R x

omit [Fintype α] in
@[simp] theorem historyRestrictedUpperDensity_empty (weight : 𝘬) (ρ t : ℝ) (S : Finset α) :
    𝔚 historyRestrictedUpperDensity S ∅ = 1 := by
  rw [historyRestrictedUpperDensity_eq_gas]
  exact historyGasPartition_empty (historyUpperPolymers S) historyMaximalPieces
    𝔚 historyComponentWeight fun _ hP => historyUpperPolymer_support_nonempty hP

𝗇 𝔖 (historyMaximalPieces (Finset.univ : Finset α)).card
/-- The actual finite history density has the source's uniform maximal-piece bounds. -/
theorem historyUpperDensity_bounds_of_degree_bound (weight : 𝘬) ρ t B
    (hρ : 𝔞) (ht : 𝔟) (hB : 𝔠) (hw : ∀ x, |weight x| ≤ B)
    D (hD : 𝔈)
    (hsmall : 𝔍 ≤ 𝔊) :
    𝔐 ^ 𝔖 ≤
        𝔎 ∧
      𝔎 ≤
        𝔛 ^ 𝔖 := by
  have hb := deletion_ratios_global_bounds 𝔙
    (𝔚 historyRestrictedUpperDensity_empty Finset.univ) (fun R x hx => ((𝔣 historyUpperDensity_positive_of_degree_bound D hD hsmall) R).2 x hx)
    $ historyMaximalPieces Finset.univ
  have heq : 𝔙 (historyMaximalPieces Finset.univ) =
      𝔎 := by
    unfold historyRestrictedUpperDensity
    rw [historyRestrictedUpperSets_full, historyScaledUpperDensity_eq_components]
  simp_all

end NearlyMinimax

𝚨

𝗇 𝔜 𝗔₂
𝗇 𝔡 2 * Δ
/-- The source threshold `1/(2+8 Delta^2)` applies to the actual dependent-word heap. -/
theorem wordHeap_density_bounds [Fintype J] [DecidableEq J]
    (word : List J) dependent
    (hrefl : 𝙂) (hsymm : 𝘼)
    Δ (hlabels : 𝘽)
    (weight : 𝔜 → ℝ) ρ t B
    (hρ : 𝔞) (ht : 𝔟) (hB : 𝔠) (hw : ∀ x, |weight x| ≤ B)
    (hsmall : 𝔍 ≤ 𝙥) :
    𝔐 ^ Fintype.card J ≤ 𝔎 ∧
      𝔎 ≤ 𝔛 ^ Fintype.card J := by
  have hD : ∀ x , (historyCoverGraph 𝔜).degree x ≤ 𝔡 := by
    intro x
    exact (wordHeapCoverGraph_degree_le hrefl hsymm x).trans $ Nat.mul_le_mul_left 2 $ hlabels _
  have hs : 𝔍 ≤ 1 / (2 + 2 * (𝔡 : ℕ) ^ 2) := by
    grind
  have hb := 𝔣 historyUpperDensity_bounds_of_degree_bound 𝔡 hD hs
  have hc := wordHeap_maximal_card_le_labels hrefl hsymm (Finset.univ : Finset 𝔜)
  refine ⟨?_, ?_⟩
  · exact (pow_le_pow_of_le_one  𝖠₄   𝖠₄  hc).trans hb.1
  · exact hb.2.trans $ pow_le_pow_right₀  𝖠₄  hc
