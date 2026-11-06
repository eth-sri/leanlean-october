module
public import Mathlib
@[expose] public section
noncomputable section
section
open scoped BigOperators
namespace NearlyMinimax
section
section
variable {α : Type*} [PartialOrder α] [DecidableEq α]
def historyMaximalPieces (S : Finset α) : Finset α := by
  classical
  exact S.filter (fun x => ∀ y ∈ S, x ≤ y → y = x)
theorem mem_historyMaximalPieces {S : Finset α} {x : α} :
    x ∈ historyMaximalPieces S ↔ x ∈ S ∧ ∀ y ∈ S, x ≤ y → y = x := by
  simp only [historyMaximalPieces, Finset.mem_filter]
theorem historyMaximalPieces_subset (S : Finset α) : historyMaximalPieces S ⊆ S := by
  intro x hx
  exact (mem_historyMaximalPieces.1 hx).1
def historyDeletionCoefficient (weight : α → ℝ) : ℕ → Finset α → ℝ
  | 0, _ => 1
  | k + 1, S => ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionCoefficient weight k (S.erase x)
@[simp] theorem historyDeletionCoefficient_zero (weight : α → ℝ) (S : Finset α) :
    historyDeletionCoefficient weight 0 S = 1 := rfl
@[simp] theorem historyDeletionCoefficient_succ (weight k) (S : Finset α) :
    historyDeletionCoefficient weight (k + 1) S =
      ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionCoefficient weight k (S.erase x) := rfl
def historyDeletionPolynomial (weight : α → ℝ) (S : Finset α) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (S.card + 1), t ^ k / k.factorial * historyDeletionCoefficient weight k S
end
section
variable {α : Type*} [PartialOrder α] [DecidableEq α]
def IncomparableHistoryParts (P Q : Finset α) : Prop :=
  ∀ p ∈ P, ∀ q ∈ Q, ¬ p ≤ q ∧ ¬ q ≤ p
theorem IncomparableHistoryParts.disjoint {P Q : Finset α} (h : IncomparableHistoryParts P Q) :
    Disjoint P Q := by
  apply Finset.disjoint_left.2
  intro x hxP hxQ
  exact (h x hxP x hxQ).1 le_rfl
def historyOrderCount (S : Finset α) : ℝ := historyDeletionCoefficient (fun _ => 1) S.card S
def historyOrderVolume (S : Finset α) : ℝ := historyOrderCount S / S.card.factorial
@[simp] theorem historyOrderCount_empty : historyOrderCount (∅ : Finset α) = 1 := by
  simp [historyOrderCount]
@[simp] theorem historyOrderVolume_empty : historyOrderVolume (∅ : Finset α) = 1 := by
  simp [historyOrderVolume]
theorem historyOrderCount_recursion (S : Finset α) (hS : S.Nonempty) :
    historyOrderCount S = ∑ x ∈ historyMaximalPieces S, historyOrderCount (S.erase x) := by
  have := Finset.card_pos.2 hS
  have hc : S.card = S.card - 1 + 1 := by omega
  unfold historyOrderCount
  rw [hc, historyDeletionCoefficient_succ]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.card_erase_of_mem (historyMaximalPieces_subset S hx), one_mul]
theorem historyOrderCount_le_factorial (S : Finset α) : historyOrderCount S ≤ S.card.factorial := by
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases he : S = ∅
  · subst S; simp
  · have hS := Finset.nonempty_iff_ne_empty.2 he
    have := Finset.card_pos.2 hS
    rw [historyOrderCount_recursion S hS]
    calc
      _ ≤ ∑ x ∈ historyMaximalPieces S, ((S.card - 1).factorial : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        have hxS := historyMaximalPieces_subset S hx
        simpa only [Finset.card_erase_of_mem hxS] using ih (S.erase x) (Finset.erase_ssubset hxS)
      _ = (historyMaximalPieces S).card * ((S.card - 1).factorial : ℝ) := by simp
      _ ≤ S.card * ((S.card - 1).factorial : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_le_card (historyMaximalPieces_subset S)
      _ = S.card.factorial := by
        have hc : S.card = S.card - 1 + 1 := by omega
        conv_rhs => rw [hc, Nat.factorial_succ]
        push_cast
        congr 1
        exact_mod_cast hc
theorem historyOrderVolume_nonneg (S : Finset α) : 0 ≤ historyOrderVolume S :=
  have hh : ∀ k (T : Finset α), 0 ≤ historyDeletionCoefficient (fun _ => 1) k T := by
    intro k
    induction k with
    | zero => intro T; simp
    | succ k ih =>
      intro T
      rw [historyDeletionCoefficient_succ]
      apply Finset.sum_nonneg
      intro x hx
      simpa only [one_mul] using ih (T.erase x)
  div_nonneg (hh S.card S) (by positivity)
theorem historyOrderVolume_recursion (S : Finset α) :
    S.card * historyOrderVolume S = ∑ x ∈ historyMaximalPieces S, historyOrderVolume (S.erase x) := by
  by_cases he : S = ∅
  · subst S
    simp [historyMaximalPieces]
  · have hS := Finset.nonempty_iff_ne_empty.2 he
    have := Finset.card_pos.2 hS
    have hc : S.card = S.card - 1 + 1 := by omega
    unfold historyOrderVolume
    rw [historyOrderCount_recursion S hS]
    conv_lhs => arg 2; arg 2; rw [hc, Nat.factorial_succ]
    push_cast
    calc
      _ = (∑ x ∈ historyMaximalPieces S, historyOrderCount (S.erase x)) /
          ((S.card - 1).factorial : ℝ) := by
        have hr : ↑S.card = ((S.card - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast hc
        rw [hr]
        field_simp [show (((S.card - 1 : ℕ) : ℝ) + 1) ≠ 0 by positivity]
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.card_erase_of_mem (historyMaximalPieces_subset S hx)]
def historyComponentWeight (weight : α → ℝ) (ρ t : ℝ) (P : Finset α) : ℝ :=
  (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, weight x
end
variable {α : Type*} [PartialOrder α] [DecidableEq α]
def IsHistoryUpper (S U : Finset α) : Prop :=
  U ⊆ S ∧ ∀ x ∈ U, ∀ y ∈ S, x ≤ y → y ∈ U
def historyUpperSets (S : Finset α) : Finset (Finset α) := by
  classical
  exact S.powerset.filter (IsHistoryUpper S)
theorem mem_historyUpperSets {S U : Finset α} :
    U ∈ historyUpperSets S ↔ IsHistoryUpper S U := by
  simp only [historyUpperSets, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
@[simp] theorem empty_mem_historyUpperSets (S : Finset α) : ∅ ∈ historyUpperSets S :=
  mem_historyUpperSets.2 (by simp [IsHistoryUpper])
theorem historyUpper_maximal_subset {S U : Finset α} (hU : IsHistoryUpper S U) :
    historyMaximalPieces U ⊆ historyMaximalPieces S := by
  intro x hx
  obtain ⟨hxU, hmax⟩ := mem_historyMaximalPieces.1 hx
  apply mem_historyMaximalPieces.2
  exact ⟨hU.1 hxU, fun y hy hxy => hmax y (hU.2 x hxU y hy hxy) hxy⟩
theorem historyUpper_erase {S U : Finset α} (hU : IsHistoryUpper S U) 
    (_hx : x ∈ historyMaximalPieces U) : IsHistoryUpper (S.erase x) (U.erase x) := by
  refine ⟨Finset.erase_subset_erase _ hU.1, ?_⟩
  intro a ha b hb hab
  exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hb).1,
    hU.2 a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab⟩
theorem historyUpper_insert {S U : Finset α} 
    (hx : x ∈ historyMaximalPieces S) (hU : IsHistoryUpper (S.erase x) U) :
    IsHistoryUpper S (insert x U) := by
  obtain ⟨hxS, hmax⟩ := mem_historyMaximalPieces.1 hx
  refine ⟨Finset.insert_subset hxS (hU.1.trans (Finset.erase_subset _ _)), ?_⟩
  intro a ha b hb hab
  rcases Finset.mem_insert.1 ha with rfl | haU
  · rw [hmax b hb hab]
    exact Finset.mem_insert_self _ _
  · by_cases hbx : b = x
    · subst b; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hU.2 a haU b (Finset.mem_erase.2 ⟨hbx, hb⟩) hab)
theorem historyUpper_not_mem_deleted {S U : Finset α} 
    (hU : IsHistoryUpper (S.erase x) U) : x ∉ U := by
  intro hxU
  exact Finset.notMem_erase x S (hU.1 hxU)
theorem historyUpper_disjoint_incomparable {S P Q : Finset α}
    (hP : IsHistoryUpper S P) (hQ : IsHistoryUpper S Q) (hdis : Disjoint P Q) :
    IncomparableHistoryParts P Q := by
  intro p hp q hq
  refine ⟨?_, ?_⟩
  · intro hpq
    exact Finset.disjoint_left.1 hdis (hP.2 p hp q (hQ.1 hq) hpq) hq
  · intro hqp
    exact Finset.disjoint_left.1 hdis hp (hQ.2 q hq p (hP.1 hp) hqp)
theorem historyUpper_nonempty_maximal {S U : Finset α} (_hU : IsHistoryUpper S U)
    (hne : U.Nonempty) : (historyMaximalPieces U).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := U.exists_maximal hne
  refine ⟨x, mem_historyMaximalPieces.2 ⟨hx, ?_⟩⟩
  intro y hy hxy
  exact le_antisymm (hmax hy hxy) hxy
theorem historyUpper_disjoint_iff {S P Q : Finset α}
    (hP : IsHistoryUpper S P) (hQ : IsHistoryUpper S Q) :
    Disjoint P Q ↔ Disjoint (historyMaximalPieces P) (historyMaximalPieces Q) := by
  have h_historyUpper_maximal_eq_inter {U : Finset α} (hU : IsHistoryUpper S U) : historyMaximalPieces U = U ∩ historyMaximalPieces S := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_inter.2 ⟨historyMaximalPieces_subset U hx, historyUpper_maximal_subset hU hx⟩
    · intro hx
      obtain ⟨hxU, hxS⟩ := Finset.mem_inter.1 hx
      exact mem_historyMaximalPieces.2 ⟨hxU, fun y hy hxy =>
        (mem_historyMaximalPieces.1 hxS).2 y (hU.1 hy) hxy⟩
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty,
    ← Finset.not_nonempty_iff_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  have h_historyUpper_inter_iff_maximal_inter : (P ∩ Q).Nonempty ↔ (historyMaximalPieces P ∩ historyMaximalPieces Q).Nonempty := by
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨hxP, hxQ⟩ := Finset.mem_inter.1 hx
      obtain ⟨y, hxy, hyS, hmax⟩ := S.exists_le_maximal (hP.1 hxP)
      have hyP := hP.2 x hxP y hyS hxy
      have hyQ := hQ.2 x hxQ y hyS hxy
      have hymax  :=
        mem_historyMaximalPieces.2 ⟨hyS, fun z hz hyz => le_antisymm (hmax hz hyz) hyz⟩
      refine ⟨y, Finset.mem_inter.2 ⟨?_, ?_⟩⟩
      · rw [h_historyUpper_maximal_eq_inter hP]; exact Finset.mem_inter.2 ⟨hyP, hymax⟩
      · rw [h_historyUpper_maximal_eq_inter hQ]; exact Finset.mem_inter.2 ⟨hyQ, hymax⟩
    · rintro ⟨x, hx⟩
      obtain ⟨hxP, hxQ⟩ := Finset.mem_inter.1 hx
      exact ⟨x, Finset.mem_inter.2 ⟨historyMaximalPieces_subset P hxP,
        historyMaximalPieces_subset Q hxQ⟩⟩
  exact not_congr h_historyUpper_inter_iff_maximal_inter
theorem historyUpper_maximal_sum (S : Finset α) (F : Finset α → α → ℝ) :
    (∑ U ∈ historyUpperSets S, ∑ x ∈ historyMaximalPieces U, F U x) =
      ∑ x ∈ historyMaximalPieces S, ∑ U ∈ historyUpperSets (S.erase x), F (insert x U) x := by
  suffices hh :
      (∑ i ∈ (historyUpperSets S).sigma historyMaximalPieces, F i.1 i.2) =
        ∑ i ∈ (historyMaximalPieces S).sigma (fun x => historyUpperSets (S.erase x)),
          F (insert i.1 i.2) i.1 by
    simpa only [Finset.sum_sigma] using hh
  apply Finset.sum_bij (fun i _ => ⟨i.2, i.1.erase i.2⟩)
  · intro i hi
    obtain ⟨hiU, hix⟩ := Finset.mem_sigma.1 hi
    have hU := mem_historyUpperSets.1 hiU
    exact Finset.mem_sigma.2 ⟨historyUpper_maximal_subset hU hix,
      mem_historyUpperSets.2 (historyUpper_erase hU hix)⟩
  · intro i hi j hj heq
    obtain ⟨hiU, hix⟩ := Finset.mem_sigma.1 hi
    obtain ⟨hjU, hjx⟩ := Finset.mem_sigma.1 hj
    have hx : i.2 = j.2 := congrArg Sigma.fst heq
    have hrest : i.1.erase i.2 = j.1.erase j.2 :=
      congrArg (fun z : Sigma (fun _ : α => Finset α) => z.2) heq
    have : i.1 = j.1 := by
      rw [← Finset.insert_erase (historyMaximalPieces_subset i.1 hix),
        ← Finset.insert_erase (historyMaximalPieces_subset j.1 hjx), hrest, hx]
    cases i
    cases j
    subst_vars
    rfl
  · intro i hi
    obtain ⟨hix, hiU⟩ := Finset.mem_sigma.1 hi
    have hU := mem_historyUpperSets.1 hiU
    refine ⟨⟨insert i.1 i.2, i.1⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, ?_⟩
    · exact mem_historyUpperSets.2 (historyUpper_insert hix hU)
    · apply mem_historyMaximalPieces.2
      refine ⟨Finset.mem_insert_self _ _, ?_⟩
      intro y hy hxy
      exact (mem_historyMaximalPieces.1 hix).2 y ((historyUpper_insert hix hU).1 hy) hxy
    · simp only [Finset.erase_insert (historyUpper_not_mem_deleted hU)]
  · intro i hi
    rw [Finset.insert_erase (historyMaximalPieces_subset i.1 (Finset.mem_sigma.1 hi).2)]
def historyUpperDensity (weight : α → ℝ) (S : Finset α) (t : ℝ) : ℝ :=
  ∑ U ∈ historyUpperSets S, t ^ U.card * historyOrderVolume U * ∏ x ∈ U, weight x
@[simp] theorem historyUpperDensity_at_zero (weight : α → ℝ) (S : Finset α) :
    historyUpperDensity weight S 0 = 1 := by
  unfold historyUpperDensity
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro U hU hne
    simp only [zero_pow (Finset.card_ne_zero.2 (Finset.nonempty_iff_ne_empty.2 hne)), zero_mul]
  · simp
theorem historyUpperDensity_hasDerivAt (weight ) (S : Finset α) (t : ℝ) :
    HasDerivAt (historyUpperDensity weight S)
      (∑ x ∈ historyMaximalPieces S, weight x * historyUpperDensity weight (S.erase x) t) t := by
  have h_historyUpperDensity_derivative_formula : HasDerivAt (historyUpperDensity weight S)
      (∑ U ∈ historyUpperSets S,
        (↑U.card * t ^ (U.card - 1)) * historyOrderVolume U * ∏ x ∈ U, weight x) t := by
    apply HasDerivAt.fun_sum
    intro U hU
    simpa only [id_eq, mul_one] using! ((hasDerivAt_id t).pow U.card).mul_const
      (historyOrderVolume U) |>.mul_const (∏ x ∈ U, weight x)
  have h_historyUpperDensity_term_derivative (U : Finset α) (t : ℝ) : ((U.card : ℝ) * t ^ (U.card - 1)) * historyOrderVolume U * (∏ x ∈ U, weight x) =
      ∑ x ∈ historyMaximalPieces U,
        weight x * (t ^ (U.erase x).card * historyOrderVolume (U.erase x) *
          ∏ y ∈ U.erase x, weight y) := by
    calc
      _ = t ^ (U.card - 1) * ((U.card : ℝ) * historyOrderVolume U) *
          (∏ x ∈ U, weight x) := by ring
      _ = t ^ (U.card - 1) * (∑ x ∈ historyMaximalPieces U, historyOrderVolume (U.erase x)) *
          (∏ x ∈ U, weight x) := by rw [historyOrderVolume_recursion]
      _ = _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        have hxU := historyMaximalPieces_subset U hx
        rw [Finset.card_erase_of_mem hxU, ← Finset.mul_prod_erase U weight hxU]
        ring
  have hh := h_historyUpperDensity_derivative_formula
  simp_rw [h_historyUpperDensity_term_derivative] at hh
  rw [historyUpper_maximal_sum] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x hx
  unfold historyUpperDensity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.erase_insert (historyUpper_not_mem_deleted (mem_historyUpperSets.1 hU))]
theorem historyUpperDensity_eq_deletionPolynomial (weight ) (S : Finset α) (t ) :
    historyUpperDensity weight S t = historyDeletionPolynomial weight S t := by
  induction S using Finset.strongInductionOn generalizing t
  rename_i S ih
  have hd : ∀ u, HasDerivAt (fun v => historyUpperDensity weight S v -
      historyDeletionPolynomial weight S v) 0 u := by
    intro u
    have h_historyDeletionPolynomial_derivative_formula : HasDerivAt (historyDeletionPolynomial weight S)
        (∑ k ∈ Finset.range (S.card + 1),
          k * u ^ (k - 1) / k.factorial * historyDeletionCoefficient weight k S) u := by
      apply HasDerivAt.fun_sum
      intro k hk
      simpa only [id_eq, mul_one] using! (((hasDerivAt_id u).pow k).div_const k.factorial).mul_const
        (historyDeletionCoefficient weight k S)
    have hh := h_historyDeletionPolynomial_derivative_formula
    have h_historyDeletionPolynomial_derivative_shift : (∑ k ∈ Finset.range (S.card + 1),
        k * u ^ (k - 1) / k.factorial * historyDeletionCoefficient weight k S) =
      ∑ k ∈ Finset.range S.card, u ^ k / k.factorial * historyDeletionCoefficient weight (k + 1) S := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, zero_div, add_zero, Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    have h_historyDeletionPolynomial_derivative_deletion : (∑ k ∈ Finset.range S.card, u ^ k / k.factorial * historyDeletionCoefficient weight (k + 1) S) =
        ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionPolynomial weight (S.erase x) u := by
      simp_rw [historyDeletionCoefficient_succ, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      have hxS := historyMaximalPieces_subset S hx
      have hc : (S.erase x).card + 1 = S.card := by
        have := Finset.card_erase_of_mem hxS
        have := Finset.card_pos.2 ⟨x, hxS⟩
        omega
      unfold historyDeletionPolynomial
      rw [hc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have hh := (historyUpperDensity_hasDerivAt weight S u).sub
      (by rw [h_historyDeletionPolynomial_derivative_shift, h_historyDeletionPolynomial_derivative_deletion] at hh; exact hh)
    have hsum : (∑ x ∈ historyMaximalPieces S, weight x * historyUpperDensity weight (S.erase x) u) =
        ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionPolynomial weight (S.erase x) u := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [ih (S.erase x) (Finset.erase_ssubset (historyMaximalPieces_subset S hx)) u]
    rw [hsum, sub_self] at hh
    exact hh
  have hh := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t 0
  have h_historyDeletionPolynomial_at_zero : historyDeletionPolynomial weight S 0 = 1 := by
    unfold historyDeletionPolynomial
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      simp [zero_pow hk0]
    · simp
  simp only [historyUpperDensity_at_zero, h_historyDeletionPolynomial_at_zero, sub_self] at hh
  exact sub_eq_zero.1 hh
def historyScaledUpperDensity (weight : α → ℝ) (ρ : ℝ) (S : Finset α) (t : ℝ) : ℝ :=
  historyUpperDensity (fun x => weight x / ρ) S t
theorem historyScaledUpperDensity_eq_components (weight ρ) (S : Finset α) (t : ℝ) :
    historyScaledUpperDensity weight ρ S t =
      ∑ U ∈ historyUpperSets S, historyComponentWeight weight ρ t U := by
  unfold historyScaledUpperDensity historyUpperDensity historyComponentWeight
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.prod_div_distrib, Finset.prod_const, div_pow]
  ring
theorem historyScaledUpperDensity_hasDerivAt (weight ρ) (S : Finset α) (t ) :
    HasDerivAt (historyScaledUpperDensity weight ρ S)
      (ρ⁻¹ * ∑ x ∈ historyMaximalPieces S, weight x * historyScaledUpperDensity weight ρ (S.erase x) t) t := by
  unfold historyScaledUpperDensity
  convert (historyUpperDensity_hasDerivAt (fun x => weight x / ρ) S t) using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring
end
structure WordHeapPiece {J : Type*} (word : List J) (dependent : J → J → Prop) where
  position : Fin word.length
@[ext] theorem WordHeapPiece.ext  {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (h : x.position = y.position) : x = y := by
  cases x
  cases y
  cases h
  rfl
instance wordHeapPiece_decidableEq {J : Type*} (word : List J) (dependent : J → J → Prop) :
    DecidableEq (WordHeapPiece word dependent) := Classical.decEq _
instance wordHeapPiece_fintype {J : Type*} (word : List J) (dependent : J → J → Prop) :
    Fintype (WordHeapPiece word dependent) :=
  Fintype.ofEquiv (Fin word.length) {
    toFun := fun i => ⟨i⟩
    invFun := WordHeapPiece.position
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
def wordHeapLabel  {word : List J} {dependent : J → J → Prop}
    (x : WordHeapPiece word dependent) : J := word.get x.position
def wordHeapStep  {word : List J} {dependent : J → J → Prop}
    (x y : WordHeapPiece word dependent) : Prop :=
  x.position < y.position ∧ dependent (wordHeapLabel x) (wordHeapLabel y)
theorem wordHeap_reachable_position_le  {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (h : Relation.ReflTransGen wordHeapStep x y) :
    x.position ≤ y.position := by
  induction h with
  | refl => exact le_rfl
  | tail hreach hstep ih => exact ih.trans hstep.1.le
instance wordHeap_partialOrder {J : Type*} (word : List J) (dependent : J → J → Prop) :
    PartialOrder (WordHeapPiece word dependent) where
  le := Relation.ReflTransGen wordHeapStep
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm x y hxy hyx := by
    apply WordHeapPiece.ext
    exact le_antisymm (wordHeap_reachable_position_le hxy) (wordHeap_reachable_position_le hyx)
theorem wordHeapStep_le  {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (h : wordHeapStep x y) : x ≤ y :=
  Relation.ReflTransGen.single h
theorem wordHeap_dependent_comparable {J : Type*} {word : List J} {dependent : J → J → Prop}
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) {x y : WordHeapPiece word dependent}
    (hdep : dependent (wordHeapLabel x) (wordHeapLabel y)) : x ≤ y ∨ y ≤ x := by
  rcases lt_trichotomy x.position y.position with hxy | heq | hyx
  · exact Or.inl (wordHeapStep_le ⟨hxy, hdep⟩)
  · have  := WordHeapPiece.ext heq
    subst y
    exact Or.inl le_rfl
  · exact Or.inr (wordHeapStep_le ⟨hyx, hsymm hdep⟩)
theorem wordHeap_cover_dependent {J : Type*} {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (hcov : x ⋖ y) :
    dependent (wordHeapLabel x) (wordHeapLabel y) := by
  cases (hcov.le) with
  | refl => exact (hcov.ne rfl).elim
  | @tail z y hxz hzy =>
    rcases (hcov.eq_or_eq hxz (wordHeapStep_le hzy)) with rfl | hzyEq
    · exact hzy.2
    · have hh : z.position < z.position := by simpa only [hzyEq] using hzy.1
      exact (lt_irrefl _ hh).elim
theorem wordHeap_equal_labels_comparable  {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {x y : WordHeapPiece word dependent} (hlab : wordHeapLabel x = wordHeapLabel y) :
    x ≤ y ∨ y ≤ x := by
  apply wordHeap_dependent_comparable hsymm
  rw [hlab]
  exact hrefl _
theorem wordHeap_upper_cover_label_injective {J : Type*} {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {x y z : WordHeapPiece word dependent} (hxy : x ⋖ y) (hxz : x ⋖ z)
    (hlab : wordHeapLabel y = wordHeapLabel z) : y = z := by
  rcases wordHeap_equal_labels_comparable hrefl hsymm hlab with hyz | hzy
  · rcases hxz.eq_or_eq hxy.le hyz with hyx | hyz
    · exact (hxy.ne hyx.symm).elim
    · exact hyz
  · rcases hxy.eq_or_eq hxz.le hzy with hzx | hzy
    · exact (hxz.ne hzx.symm).elim
    · exact hzy.symm
theorem wordHeap_lower_cover_label_injective {J : Type*} {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {x y z : WordHeapPiece word dependent} (hyx : y ⋖ x) (hzx : z ⋖ x)
    (hlab : wordHeapLabel y = wordHeapLabel z) : y = z := by
  rcases wordHeap_equal_labels_comparable hrefl hsymm hlab with hyz | hzy
  · rcases hyx.eq_or_eq hyz hzx.le with hzy | hzxEq
    · exact hzy.symm
    · exact (hzx.ne hzxEq).elim
  · rcases hzx.eq_or_eq hzy hyx.le with hyz | hyxEq
    · exact hyz
    · exact (hyx.ne hyxEq).elim
theorem wordHeap_maximal_label_injective  {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (S : Finset (WordHeapPiece word dependent)) :
    Set.InjOn wordHeapLabel (historyMaximalPieces S : Set (WordHeapPiece word dependent)) := by
  intro x hx y hy hlab
  obtain ⟨hxS, hxmax⟩ := mem_historyMaximalPieces.1 hx
  obtain ⟨hyS, hymax⟩ := mem_historyMaximalPieces.1 hy
  rcases wordHeap_equal_labels_comparable hrefl hsymm hlab with hxy | hyx
  · exact (hxmax y hyS hxy).symm
  · exact hymax x hxS hyx
theorem wordHeap_maximal_card_le_labels  [Fintype J] [DecidableEq J]
    {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (S : Finset (WordHeapPiece word dependent)) :
    (historyMaximalPieces S).card ≤ Fintype.card J := by
  rw [← Finset.card_image_iff.2 (wordHeap_maximal_label_injective hrefl hsymm S)]
  exact Finset.card_le_card (Finset.subset_univ _)
def wordHeapUpperCovers  {word : List J} {dependent : J → J → Prop}
    (x : WordHeapPiece word dependent) : Finset (WordHeapPiece word dependent) := by
  classical
  exact Finset.univ.filter (fun y => x ⋖ y)
def wordHeapLowerCovers  {word : List J} {dependent : J → J → Prop}
    (x : WordHeapPiece word dependent) : Finset (WordHeapPiece word dependent) := by
  classical
  exact Finset.univ.filter (fun y => y ⋖ x)
def dependentLabelFinset  [Fintype J] (dependent : J → J → Prop) (j : J) : Finset J := by
  classical
  exact Finset.univ.filter (fun i => dependent j i)
def wordHeapCoverGraph {J : Type*} (word : List J) (dependent : J → J → Prop) :
    SimpleGraph (WordHeapPiece word dependent) where
  Adj x y := x ⋖ y ∨ y ⋖ x
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun x h => by
    rcases h with h | h <;> exact h.ne rfl⟩
instance wordHeapCoverGraph_neighbor_fintype {J : Type*} (word : List J) (dependent : J → J → Prop)
    (x : WordHeapPiece word dependent) : Fintype ((wordHeapCoverGraph word dependent).neighborSet x) :=
  Fintype.ofFinite _
theorem wordHeapCoverGraph_degree_le  [Fintype J] {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (x : WordHeapPiece word dependent) :
    (wordHeapCoverGraph word dependent).degree x ≤
      2 * (dependentLabelFinset dependent (wordHeapLabel x)).card := by
  change ((wordHeapCoverGraph word dependent).neighborFinset x).card ≤ _
  have h_wordHeapCoverGraph_neighbors : (wordHeapCoverGraph word dependent).neighborFinset x = wordHeapUpperCovers x ∪ wordHeapLowerCovers x := by
    ext y
    rw [SimpleGraph.mem_neighborFinset]
    simp only [wordHeapUpperCovers, wordHeapLowerCovers, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl
  rw [h_wordHeapCoverGraph_neighbors]
  have h_wordHeap_upper_covers_card : (wordHeapUpperCovers x).card ≤ (dependentLabelFinset dependent (wordHeapLabel x)).card := by
    classical
    apply Finset.card_le_card_of_injOn wordHeapLabel
    · intro y hy
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, wordHeap_cover_dependent ((Finset.mem_filter.1 hy).2)⟩
    · intro y hy z hz hlab
      exact wordHeap_upper_cover_label_injective hrefl hsymm
        (Finset.mem_filter.1 hy).2 (Finset.mem_filter.1 hz).2 hlab
  have := h_wordHeap_upper_covers_card
  have h_wordHeap_lower_covers_card : (wordHeapLowerCovers x).card ≤ (dependentLabelFinset dependent (wordHeapLabel x)).card := by
    classical
    apply Finset.card_le_card_of_injOn wordHeapLabel
    · intro y hy
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hsymm (wordHeap_cover_dependent ((Finset.mem_filter.1 hy).2))⟩
    · intro y hy z hz hlab
      exact wordHeap_lower_cover_label_injective hrefl hsymm
        (Finset.mem_filter.1 hy).2 (Finset.mem_filter.1 hz).2 hlab
  have := h_wordHeap_lower_covers_card
  have := Finset.card_union_le (wordHeapUpperCovers x) (wordHeapLowerCovers x)
  omega
section
section
theorem positive_deletion_recurrence  [DecidableEq α]
    (F : Finset α → ℝ) (rows : Finset α → α → Finset β)
    (removed : β → Finset α) (weight : β → ℝ)
    (hempty : F ∅ = 1)
    (hremove : ∀ S x, x ∈ S → ∀ P ∈ rows S x, x ∈ removed P ∧ removed P ⊆ S)
    (hrec : ∀ S x, x ∈ S →
      F S = F (S.erase x) + ∑ P ∈ rows S x, weight P * F (S \ removed P))
    (hactivity : ∀ S x, x ∈ S →
      (∑ P ∈ rows S x, |weight P| * (2 : ℝ) ^ ((removed P).card - 1)) ≤ 1 / 2) :
    ∀ S, 0 < F S ∧ ∀ x ∈ S,
      F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x) := by
  intro S
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases he : S = ∅
  · subst S
    simp [hempty]
  · have hratio : ∀ x ∈ S,
        0 < F (S.erase x) ∧
        F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x) := by
      intro x hx
      have hprevious := ih (S.erase x) (Finset.erase_ssubset hx)
      have hterms : ∀ P ∈ rows S x,
          0 ≤ F (S \ removed P) ∧
          F (S \ removed P) ≤ ↑2 ^ ((removed P).card - 1) * F (S.erase x) := by
        intro P hP
        obtain ⟨hxP, hPS⟩ := hremove S x hx P hP
        have hsub : S \ removed P ⊆ S.erase x := by
          intro y hy
          obtain ⟨hyS, hyn⟩ := Finset.mem_sdiff.mp hy
          exact Finset.mem_erase.mpr ⟨by intro h; subst y; exact hyn hxP, hyS⟩
        have hproper  :=
          hsub.trans_ssubset (Finset.erase_ssubset hx)
        have hc : (S.erase x).card - (S \ removed P).card = (removed P).card - 1 := by
          have := Finset.card_le_card hPS
          have := Finset.card_pos.mpr ⟨x, hxP⟩
          rw [Finset.card_erase_of_mem hx, Finset.card_sdiff_of_subset hPS]
          omega
        refine ⟨(ih (S \ removed P) hproper).1.le, ?_⟩
        rw [← hc]
        have h_deletion_comparison (T : Finset α) (U : Finset α) (hUT : U ⊆ T) (hstep : ∀ V ⊆ T, ∀ x ∈ V, F (V.erase x) ≤ 2 * F V) : F U ≤ ↑2 ^ (T.card - U.card) * F T := by
          induction T using Finset.strongInductionOn generalizing U
          rename_i T ih
          by_cases heq : U = T
          · subst U
            simp
          · have hnot  := fun hTU => heq (Finset.Subset.antisymm hUT hTU)
            obtain ⟨x, hxT, hxU⟩ := Finset.not_subset.mp hnot
            have hue : U ⊆ T.erase x := by
              intro y hy
              exact Finset.mem_erase.mpr ⟨by intro h; subst y; exact hxU hy, hUT hy⟩
            have hsmall := ih (T.erase x) (Finset.erase_ssubset hxT) U hue
              (fun V hV => hstep V (hV.trans (Finset.erase_subset _ _)))
            have hcard : T.card - U.card = (T.erase x).card - U.card + 1 := by
              have := Finset.card_le_card hue
              have := Finset.card_erase_of_mem hxT
              have := Finset.card_pos.mpr ⟨x, hxT⟩
              omega
            calc
              F U ≤ ↑2 ^ ((T.erase x).card - U.card) * F (T.erase x) := hsmall
              _ ≤ ↑2 ^ ((T.erase x).card - U.card) * (2 * F T) := mul_le_mul_of_nonneg_left (hstep T Finset.Subset.rfl x hxT) (by positivity)
              _ = ↑2 ^ (T.card - U.card) * F T := by rw [hcard, pow_succ]; ring
        apply h_deletion_comparison (S.erase x) (S \ removed P) hsub
        intro V hV y hy
        have hp  := hV.trans_ssubset (Finset.erase_ssubset hx)
        have := (ih V hp).2 y hy |>.1
        linarith
      have : |F S - F (S.erase x)| ≤ F (S.erase x) / 2 := by
        rw [hrec S x hx, add_sub_cancel_left]
        calc
          |∑ P ∈ rows S x, weight P * F (S \ removed P)| ≤
              ∑ P ∈ rows S x, |weight P * F (S \ removed P)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ P ∈ rows S x, |weight P| * F (S \ removed P) := by
            apply Finset.sum_congr rfl
            intro P hP
            rw [abs_mul, abs_of_nonneg (hterms P hP).1]
          _ ≤ ∑ P ∈ rows S x,
              |weight P| * (↑2 ^ ((removed P).card - 1) * F (S.erase x)) := by
            apply Finset.sum_le_sum
            intro P hP
            exact mul_le_mul_of_nonneg_left (hterms P hP).2 (abs_nonneg _)
          _ = (∑ P ∈ rows S x, |weight P| * ↑2 ^ ((removed P).card - 1)) *
              F (S.erase x) := by simp_rw [← mul_assoc]; rw [Finset.sum_mul]
          _ ≤ 1 / 2 * F (S.erase x) :=
            mul_le_mul_of_nonneg_right (hactivity S x hx) hprevious.1.le
          _ = F (S.erase x) / 2 := by ring
      refine ⟨hprevious.1, ?_, ?_⟩
      · linarith [neg_le_abs (F S - F (S.erase x))]
      · linarith [le_abs_self (F S - F (S.erase x))]
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have h := hratio x hx
    refine ⟨by linarith [h.1], fun y hy => (hratio y hy).2⟩
theorem deletion_ratios_global_bounds {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) (hempty : F ∅ = 1)
    (hstep : ∀ S x, x ∈ S →
      F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x)) :
    ∀ S, (1 / 2 : ℝ) ^ S.card ≤ F S ∧ F S ≤ (3 / 2 : ℝ) ^ S.card := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp [hempty]
  | @insert x S hx ih =>
    have h := hstep (insert x S) x (by simp)
    simp only [Finset.erase_insert hx] at h
    rw [Finset.card_insert_of_notMem hx, pow_succ, pow_succ]
    constructor <;> nlinarith [ih.1, ih.2]
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
def CompatibleHistoryFamily (support : β → Finset α) (F : Finset β) : Prop :=
  ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (support p) (support q)
def historyGasFamilies (P : Finset β) (support : β → Finset α) (S : Finset α) : Finset (Finset β) := by
  classical
  exact P.powerset.filter (fun F => CompatibleHistoryFamily support F ∧ ∀ p ∈ F, support p ⊆ S)
def historyGasPartition (P : Finset β) (support : β → Finset α) (weight : β → ℝ) (S : Finset α) : ℝ :=
  ∑ F ∈ historyGasFamilies P support S, ∏ p ∈ F, weight p
def historyGasRows (P : Finset β) (support : β → Finset α) (S : Finset α) (x : α) : Finset β :=
  P.filter (fun p => x ∈ support p ∧ support p ⊆ S)
theorem mem_historyGasFamilies  {support : β → Finset α}   :
    F ∈ historyGasFamilies P support S ↔
      F ⊆ P ∧ CompatibleHistoryFamily support F ∧ ∀ p ∈ F, support p ⊆ S := by
  simp only [historyGasFamilies, Finset.mem_filter, Finset.mem_powerset]
theorem historyGasPartition_empty (P : Finset β) (support : β → Finset α) (weight : β → ℝ)
    (hne : ∀ p ∈ P, (support p).Nonempty) : historyGasPartition P support weight ∅ = 1 := by
  unfold historyGasPartition
  have hfamilies : historyGasFamilies P support ∅ = {∅} := by
    ext F
    rw [Finset.mem_singleton, mem_historyGasFamilies]
    constructor
    · rintro ⟨hFP, _, hs⟩
      apply Finset.eq_empty_iff_forall_notMem.2
      intro p hp
      obtain ⟨x, hx⟩ := hne p (hFP hp)
      simpa using hs p hp hx
    · intro hF
      subst F
      simp [CompatibleHistoryFamily]
  rw [hfamilies]
  simp
theorem historyGasFamily_unique_at  {support : β → Finset α} 
     (hF : F ∈ historyGasFamilies P support S) {p q : β} {x : α}
    (hp : p ∈ F) (hq : q ∈ F) (hxp : x ∈ support p) (hxq : x ∈ support q) : p = q := by
  by_contra hpq
  exact Finset.disjoint_left.1 ((mem_historyGasFamilies.1 hF).2.1 p hp q hq hpq) hxp hxq
theorem historyGasFamily_insert_component  {support : β → Finset α} 
      (hF : F ∈ historyGasFamilies P support (S \ support p))
    (hp : p ∈ P) (hps : support p ⊆ S) : insert p F ∈ historyGasFamilies P support S := by
  obtain ⟨hFP, hcompat, hsupport⟩ := mem_historyGasFamilies.1 hF
  rw [mem_historyGasFamilies]
  refine ⟨Finset.insert_subset hp hFP, ?_, ?_⟩
  · intro q hq r hr hqr
    by_cases hqp : q = p
    · subst q
      apply Finset.disjoint_left.2
      intro x hx hx'
      exact (Finset.mem_sdiff.1 (hsupport r (Finset.mem_of_mem_insert_of_ne hr (Ne.symm hqr)) hx')).2 hx
    · have hqF := Finset.mem_of_mem_insert_of_ne hq hqp
      by_cases hrp : r = p
      · subst r
        apply Finset.disjoint_left.2
        intro x hx hx'
        exact (Finset.mem_sdiff.1 (hsupport q hqF hx)).2 hx'
      · exact hcompat q hqF r (Finset.mem_of_mem_insert_of_ne hr hrp) hqr
  · intro q hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact hps
    · exact (hsupport q hq).trans Finset.sdiff_subset
theorem historyGasComponent_not_mem  {support : β → Finset α} 
       (hF : F ∈ historyGasFamilies P support (S \ support p))
    (hxp : x ∈ support p) : p ∉ F := by
  intro hp
  exact (Finset.mem_sdiff.1 ((mem_historyGasFamilies.1 hF).2.2 p hp hxp)).2 hxp
def historyGasActiveFamilies (P : Finset β) (support : β → Finset α) (S : Finset α) (x : α) :
    Finset (Finset β) := by
  classical
  exact (historyGasFamilies P support S).filter (fun F => ∃ p ∈ F, x ∈ support p)
theorem historyGas_active_sum (P : Finset β) (support : β → Finset α) (weight : β → ℝ)
    (S : Finset α) (x : α) :
    (∑ F ∈ historyGasActiveFamilies P support S x, ∏ p ∈ F, weight p) =
      ∑ p ∈ historyGasRows P support S x, weight p * historyGasPartition P support weight (S \ support p) := by
  have hsum : (∑ i ∈ (historyGasRows P support S x).sigma (fun p => historyGasFamilies P support (S \ support p)), weight i.1 * ∏ p ∈ i.2, weight p) =
      ∑ F ∈ historyGasActiveFamilies P support S x, ∏ p ∈ F, weight p := by
    apply Finset.sum_bij (fun i _ => insert i.1 i.2)
    · intro i hi
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨hiP, hix, hiS⟩ := Finset.mem_filter.1 hip
      apply Finset.mem_filter.2
      refine ⟨historyGasFamily_insert_component hiF hiP hiS, i.1, ?_, hix⟩
      exact Finset.mem_insert_self _ _
    · intro i hi j hj heq
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨hjp, hjF⟩ := Finset.mem_sigma.1 hj
      obtain ⟨hiP, hix, hiS⟩ := Finset.mem_filter.1 hip
      obtain ⟨hjP, hjx, hjS⟩ := Finset.mem_filter.1 hjp
      have hfamily := historyGasFamily_insert_component hiF hiP hiS
      have hji : j.1 ∈ insert i.1 i.2 := by rw [heq]; exact Finset.mem_insert_self _ _
      have hpq := historyGasFamily_unique_at hfamily (Finset.mem_insert_self _ _) hji hix hjx
      cases i with | mk p F =>
        cases j with | mk q G =>
          dsimp at hpq heq hix hiF hjF
          subst q
          have hnF := historyGasComponent_not_mem hiF hix
          have hnG := historyGasComponent_not_mem hjF hix
          have hFG := congrArg (fun T => T.erase p) heq
          simp only [Finset.erase_insert hnF, Finset.erase_insert hnG] at hFG
          subst G
          rfl
    · intro F hF
      obtain ⟨hfamily, p, hp, hxp⟩ := Finset.mem_filter.1 hF
      obtain ⟨hFP, _, hs⟩ := mem_historyGasFamilies.1 hfamily
      refine ⟨⟨p, F.erase p⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_filter.2 ⟨hFP hp, hxp, hs p hp⟩
      have h_historyGasFamily_erase_component : F.erase p ∈ historyGasFamilies P support (S \ support p) := by
        obtain ⟨hFP, hcompat, hsupport⟩ := mem_historyGasFamilies.1 hfamily
        rw [mem_historyGasFamilies]
        refine ⟨(Finset.erase_subset _ _).trans hFP, ?_, ?_⟩
        · intro q hq r hr hqr
          exact hcompat q (Finset.mem_of_mem_erase hq) r (Finset.mem_of_mem_erase hr) hqr
        · intro q hq x hx
          obtain ⟨hqp, hqF⟩ := Finset.mem_erase.1 hq
          exact Finset.mem_sdiff.2 ⟨hsupport q hqF hx,
            fun hxp => Finset.disjoint_left.1 (hcompat q hqF p hp hqp) hx hxp⟩
      · exact h_historyGasFamily_erase_component
      · exact Finset.insert_erase hp
    · intro i hi
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨_, hix, _⟩ := Finset.mem_filter.1 hip
      rw [Finset.prod_insert (historyGasComponent_not_mem hiF hix)]
  rw [← hsum, Finset.sum_sigma]
  unfold historyGasPartition
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
theorem historyGasPartition_positive (P ) (support : β → Finset α) (weight : β → ℝ)
    (hne : ∀ p ∈ P, (support p).Nonempty)
    (hactivity : ∀ S x, x ∈ S →
      (∑ p ∈ historyGasRows P support S x, |weight p| * (2 : ℝ) ^ ((support p).card - 1)) ≤ 1 / 2) :
    ∀ S, 0 < historyGasPartition P support weight S ∧ ∀ x ∈ S,
      historyGasPartition P support weight (S.erase x) / 2 ≤ historyGasPartition P support weight S ∧
      historyGasPartition P support weight S ≤ 3 / 2 * historyGasPartition P support weight (S.erase x) := by
  apply positive_deletion_recurrence (historyGasPartition P support weight)
    (historyGasRows P support) support weight (historyGasPartition_empty P support weight hne)
  · intro S x hx p hp
    exact (Finset.mem_filter.1 hp).2
  · intro S x hx
    have h_historyGasFamilies_erase : historyGasFamilies P support (S.erase x) =
        (historyGasFamilies P support S).filter (fun F => ¬ ∃ p ∈ F, x ∈ support p) := by
      ext F
      rw [mem_historyGasFamilies, Finset.mem_filter, mem_historyGasFamilies]
      constructor
      · rintro ⟨hFP, hc, hs⟩
        refine ⟨⟨hFP, hc, fun p hp => (hs p hp).trans (Finset.erase_subset _ _)⟩, ?_⟩
        rintro ⟨p, hp, hxp⟩
        exact (Finset.mem_erase.1 (hs p hp hxp)).1 rfl
      · rintro ⟨⟨hFP, hc, hs⟩, hnone⟩
        refine ⟨hFP, hc, ?_⟩
        intro p hp y hy
        refine Finset.mem_erase.2 ⟨?_, hs p hp hy⟩
        intro hyx
        subst y
        exact hnone ⟨p, hp, hy⟩
    rw [← historyGas_active_sum, historyGasPartition, historyGasPartition, h_historyGasFamilies_erase, add_comm]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  · exact hactivity
end
section
variable {α : Type*} [PartialOrder α] [DecidableEq α]
def historyComparableEdge (U : Finset α) (a b : α) : Prop :=
  a ∈ U ∧ b ∈ U ∧ (a ≤ b ∨ b ≤ a)
def HistoryConnected (U : Finset α) (a b : α) : Prop :=
  Relation.EqvGen (historyComparableEdge U) a b
def historyComponent (U : Finset α) (a : α) : Finset α := by
  classical
  exact U.filter (HistoryConnected U a)
theorem mem_historyComponent  {a b : α} :
    b ∈ historyComponent U a ↔ b ∈ U ∧ HistoryConnected U a b := by
  classical
  exact Finset.mem_filter
theorem historyComponent_subset (U : Finset α) (a : α) : historyComponent U a ⊆ U :=
  fun _ h => (mem_historyComponent.1 h).1
theorem self_mem_historyComponent {U : Finset α} {a : α} (ha : a ∈ U) :
    a ∈ historyComponent U a := mem_historyComponent.2 ⟨ha, .refl _⟩
theorem historyComponent_eq_of_connected {U : Finset α} {a b : α}
    (h : HistoryConnected U a b) : historyComponent U a = historyComponent U b := by
  ext x
  rw [mem_historyComponent, mem_historyComponent]
  constructor
  · rintro ⟨hx, hax⟩
    exact ⟨hx, .trans _ _ _ (.symm _ _ h) hax⟩
  · rintro ⟨hx, hbx⟩
    exact ⟨hx, .trans _ _ _ h hbx⟩
theorem historyComponent_eq_of_inter {U : Finset α} {a b : α}
    (h : (historyComponent U a ∩ historyComponent U b).Nonempty) :
    historyComponent U a = historyComponent U b := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨hxa, hxb⟩ := Finset.mem_inter.1 hx
  apply historyComponent_eq_of_connected
  exact .trans _ _ _ (mem_historyComponent.1 hxa).2 (.symm _ _ (mem_historyComponent.1 hxb).2)
def IsConnectedHistorySubset (U : Finset α) : Prop :=
  U.Nonempty ∧ ∀ a ∈ U, ∀ b ∈ U, HistoryConnected U a b
theorem historyComponent_connected {U : Finset α} {r : α} (hr : r ∈ U) :
    IsConnectedHistorySubset (historyComponent U r) := by
  refine ⟨⟨r, self_mem_historyComponent hr⟩, ?_⟩
  intro a ha b hb
  have hra := (mem_historyComponent.1 ha).2
  have h_historyComponent_connected_lift {a : α} {b : α} {U} (h : HistoryConnected U a b) : HistoryConnected U r a → HistoryConnected (historyComponent U r) a b := by
    induction h with
    | rel a b hab =>
      intro hra
      apply Relation.EqvGen.rel
      exact ⟨mem_historyComponent.2 ⟨hab.1, hra⟩,
        mem_historyComponent.2 ⟨hab.2.1, .trans _ _ _ hra (.rel _ _ hab)⟩, hab.2.2⟩
    | refl a => intro _; exact .refl _
    | symm a b hab ih =>
      intro hrb
      exact .symm _ _ (ih (.trans _ _ _ hrb (.symm _ _ hab)))
    | trans a b c hab hbc ihab ihbc =>
      intro hra
      exact .trans _ _ _ (ihab hra) (ihbc (.trans _ _ _ hra hab))
  exact (h_historyComponent_connected_lift (.trans _ _ _ (.symm _ _ hra) ((mem_historyComponent.1 hb).2))) hra
theorem historyComponent_upper {S U : Finset α} (hU : IsHistoryUpper S U) (r : α) :
    IsHistoryUpper S (historyComponent U r) := by
  refine ⟨(historyComponent_subset U r).trans hU.1, ?_⟩
  intro a ha b hb hab
  obtain ⟨haU, hra⟩ := mem_historyComponent.1 ha
  have hbU := hU.2 a haU b hb hab
  exact mem_historyComponent.2 ⟨hbU, .trans _ _ _ hra (.rel _ _ ⟨haU, hbU, Or.inl hab⟩)⟩
def historyComponents (U : Finset α) : Finset (Finset α) := U.image (historyComponent U)
theorem mem_historyComponents {U P : Finset α} :
    P ∈ historyComponents U ↔ ∃ r ∈ U, historyComponent U r = P := Finset.mem_image
theorem historyComponents_subset {U P : Finset α} (hP : P ∈ historyComponents U) : P ⊆ U := by
  obtain ⟨r, _, rfl⟩ := mem_historyComponents.1 hP
  exact historyComponent_subset U r
theorem historyComponents_upper {S U P : Finset α} (hU : IsHistoryUpper S U)
    (hP : P ∈ historyComponents U) : IsHistoryUpper S P := by
  obtain ⟨r, _, rfl⟩ := mem_historyComponents.1 hP
  exact historyComponent_upper hU r
theorem historyComponents_pairwise_disjoint (U : Finset α) :
    ∀ P ∈ historyComponents U, ∀ Q ∈ historyComponents U, P ≠ Q → Disjoint P Q := by
  intro P hP Q hQ hpq
  obtain ⟨p, _, rfl⟩ := mem_historyComponents.1 hP
  obtain ⟨q, _, rfl⟩ := mem_historyComponents.1 hQ
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  exact fun hi => hpq (historyComponent_eq_of_inter hi)
theorem historyComponents_biUnion (U : Finset α) : (historyComponents U).biUnion id = U := by
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨P, hP, hx⟩
    exact historyComponents_subset hP hx
  · intro hx
    exact ⟨historyComponent U x, mem_historyComponents.2 ⟨x, hx, rfl⟩, self_mem_historyComponent hx⟩
theorem historyUpper_biUnion  {F : Finset (Finset α)}
    (hF : ∀ P ∈ F, IsHistoryUpper S P) : IsHistoryUpper S (F.biUnion id) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx
    exact (hF P hP).1 hxP
  · intro x hx y hy hxy
    obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_biUnion.2 ⟨P, hP, (hF P hP).2 x hxP y hy hxy⟩
theorem historyComponentWeight_biUnion (weight ρ t)
    {S : Finset α} (F : Finset (Finset α)) (hF : ∀ P ∈ F, IsHistoryUpper S P)
    (hdis : ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → Disjoint P Q) :
    historyComponentWeight weight ρ t (F.biUnion id) = ∏ P ∈ F, historyComponentWeight weight ρ t P := by
  induction F using Finset.induction_on with
  | empty => simp [historyComponentWeight]
  | @insert P F hPF ih =>
    have hFin  := fun Q hQ => hF Q (Finset.mem_insert_of_mem hQ)
    have hPdis : Disjoint P (F.biUnion id) := by
      apply Finset.disjoint_left.2
      intro x hxP hxF
      obtain ⟨Q, hQ, hxQ⟩ := Finset.mem_biUnion.1 hxF
      have hPQ : P ≠ Q := fun heq => hPF (heq ▸ hQ)
      exact Finset.disjoint_left.1 (hdis P (Finset.mem_insert_self _ _) Q
        (Finset.mem_insert_of_mem hQ) hPQ) hxP hxQ
    have hinc := historyUpper_disjoint_incomparable (hF P (Finset.mem_insert_self _ _))
      (historyUpper_biUnion hFin) hPdis
    have h_historyComponentWeight_union {P : Finset α} {Q : Finset α} (hinc : IncomparableHistoryParts P Q) : historyComponentWeight weight ρ t (P ∪ Q) =
        historyComponentWeight weight ρ t P * historyComponentWeight weight ρ t Q := by
      have hdis := hinc.disjoint
      unfold historyComponentWeight
      have hmain : ∀ n : ℕ, ∀ P Q : Finset α, (P ∪ Q).card = n → IncomparableHistoryParts P Q →
          historyOrderVolume (P ∪ Q) = historyOrderVolume P * historyOrderVolume Q := by
        intro n
        induction n using Nat.strong_induction_on
        rename_i n ih
        intro P Q hn hinc
        by_cases he : P ∪ Q = ∅
        · have hP : P = ∅ := (Finset.union_eq_empty.1 he).1
          have hQ : Q = ∅ := (Finset.union_eq_empty.1 he).2
          simp [hP, hQ]
        · have hdis := hinc.disjoint
          have hmaxdis : Disjoint (historyMaximalPieces P) (historyMaximalPieces Q) :=
            hdis.mono (historyMaximalPieces_subset P) (historyMaximalPieces_subset Q)
          have hleft : (∑ x ∈ historyMaximalPieces P, historyOrderVolume ((P ∪ Q).erase x)) =
              ↑P.card * historyOrderVolume P * historyOrderVolume Q := by
            calc
              _ = ∑ x ∈ historyMaximalPieces P, historyOrderVolume (P.erase x) * historyOrderVolume Q := by
                apply Finset.sum_congr rfl
                intro x hx
                have hxP := historyMaximalPieces_subset P hx
                have hxQ : x ∉ Q := fun hxQ => Finset.disjoint_left.1 hdis hxP hxQ
                have hU : (P ∪ Q).erase x = P.erase x ∪ Q := by
                  rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hxQ]
                have hinc' : IncomparableHistoryParts (P.erase x) Q :=
                  fun p hp q hq => hinc p (Finset.mem_of_mem_erase hp) q hq
                rw [hU]
                exact ih _ (by rw [← hU, ← hn]; exact Finset.card_lt_card (Finset.erase_ssubset (Finset.mem_union_left _ hxP))) (P.erase x) Q rfl hinc'
              _ = (∑ x ∈ historyMaximalPieces P, historyOrderVolume (P.erase x)) * historyOrderVolume Q :=
                (Finset.sum_mul _ _ _).symm
              _ = _ := by rw [← historyOrderVolume_recursion]
          have hright : (∑ x ∈ historyMaximalPieces Q, historyOrderVolume ((P ∪ Q).erase x)) =
              ↑Q.card * historyOrderVolume P * historyOrderVolume Q := by
            calc
              _ = ∑ x ∈ historyMaximalPieces Q, historyOrderVolume P * historyOrderVolume (Q.erase x) := by
                apply Finset.sum_congr rfl
                intro x hx
                have hxQ := historyMaximalPieces_subset Q hx
                have hxP : x ∉ P := fun hxP => Finset.disjoint_left.1 hdis hxP hxQ
                have hU : (P ∪ Q).erase x = P ∪ Q.erase x := by
                  rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hxP]
                have hinc' : IncomparableHistoryParts P (Q.erase x) :=
                  fun p hp q hq => hinc p hp q (Finset.mem_of_mem_erase hq)
                rw [hU]
                exact ih _ (by rw [← hU, ← hn]; exact Finset.card_lt_card (Finset.erase_ssubset (Finset.mem_union_right _ hxQ))) P (Q.erase x) rfl hinc'
              _ = historyOrderVolume P * (∑ x ∈ historyMaximalPieces Q, historyOrderVolume (Q.erase x)) :=
                (Finset.mul_sum _ _ _).symm
              _ = _ := by rw [← historyOrderVolume_recursion]; ring
          have hrec := historyOrderVolume_recursion (P ∪ Q)
          have h_historyMaximalPieces_union : historyMaximalPieces (P ∪ Q) = historyMaximalPieces P ∪ historyMaximalPieces Q := by
            ext x
            rw [mem_historyMaximalPieces, Finset.mem_union]
            constructor
            · rintro ⟨hx, hm⟩
              rcases hx with hxP | hxQ
              · exact Finset.mem_union.2 (Or.inl (mem_historyMaximalPieces.2 ⟨hxP, fun y hy hxy => hm y (Finset.mem_union_left _ hy) hxy⟩))
              · exact Finset.mem_union.2 (Or.inr (mem_historyMaximalPieces.2 ⟨hxQ, fun y hy hxy => hm y (Finset.mem_union_right _ hy) hxy⟩))
            · intro hx
              rcases Finset.mem_union.1 hx with hxP | hxQ
              · obtain ⟨hxP, hm⟩ := mem_historyMaximalPieces.1 hxP
                refine ⟨Or.inl hxP, ?_⟩
                intro y hy hxy
                rcases Finset.mem_union.1 hy with hyP | hyQ
                · exact hm y hyP hxy
                · exact ((hinc x hxP y hyQ).1 hxy).elim
              · obtain ⟨hxQ, hm⟩ := mem_historyMaximalPieces.1 hxQ
                refine ⟨Or.inr hxQ, ?_⟩
                intro y hy hxy
                rcases Finset.mem_union.1 hy with hyP | hyQ
                · exact ((hinc y hyP x hxQ).2 hxy).elim
                · exact hm y hyQ hxy
          rw [h_historyMaximalPieces_union, Finset.sum_union hmaxdis, hleft, hright] at hrec
          have hcard : (P ∪ Q).card = P.card + Q.card := Finset.card_union_of_disjoint hdis
          have hpos : 0 < ((P ∪ Q).card : ℝ) := by
            exact_mod_cast Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 he)
          apply mul_left_cancel₀ hpos.ne'
          rw [hrec, hcard]
          push_cast
          ring
      have h_historyOrderVolume_union := hmain (P ∪ Q).card P Q rfl hinc
      rw [Finset.card_union_of_disjoint hdis, pow_add, h_historyOrderVolume_union, Finset.prod_union hdis]
      ring
    rw [Finset.biUnion_insert, id_eq, h_historyComponentWeight_union hinc,
      Finset.prod_insert hPF, ih hFin (fun Q hQ R hR hQR => hdis Q (Finset.mem_insert_of_mem hQ) R (Finset.mem_insert_of_mem hR) hQR)]
theorem historyComponentWeight_eq_component_prod (weight ρ t)
    {S U : Finset α} (hU : IsHistoryUpper S U) :
    historyComponentWeight weight ρ t U =
      ∏ P ∈ historyComponents U, historyComponentWeight weight ρ t P := by
  calc
    _ = historyComponentWeight weight ρ t ((historyComponents U).biUnion id) := by
      rw [historyComponents_biUnion]
    _ = _ := historyComponentWeight_biUnion weight ρ t (historyComponents U)
      (fun _ hP => historyComponents_upper hU hP) (historyComponents_pairwise_disjoint U)
def historyUpperPolymers (S : Finset α) : Finset (Finset α) := by
  classical
  exact (historyUpperSets S).filter IsConnectedHistorySubset
theorem mem_historyUpperPolymers {S P : Finset α} :
    P ∈ historyUpperPolymers S ↔ IsHistoryUpper S P ∧ IsConnectedHistorySubset P := by
  simp only [historyUpperPolymers, Finset.mem_filter, mem_historyUpperSets]
theorem historyUpperPolymer_support_nonempty {S P : Finset α} (hP : P ∈ historyUpperPolymers S) :
    (historyMaximalPieces P).Nonempty :=
  historyUpper_nonempty_maximal (mem_historyUpperPolymers.1 hP).1 (mem_historyUpperPolymers.1 hP).2.1
theorem historyConnected_mono {P U : Finset α} (hsub : P ⊆ U) {a b : α}
    (h : HistoryConnected P a b) : HistoryConnected U a b :=
  Relation.EqvGen.mono (r := historyComparableEdge P) (p := historyComparableEdge U)
    (fun _ _ hab => ⟨hsub hab.1, hsub hab.2.1, hab.2.2⟩) a b h
theorem historyConnected_preserves_incomparable_part 
    (hinc : IncomparableHistoryParts P Q) {a b : α} (h : HistoryConnected (P ∪ Q) a b) :
    a ∈ P ↔ b ∈ P := by
  induction h with
  | rel a b hab =>
    constructor
    · intro haP
      rcases Finset.mem_union.1 hab.2.1 with hbP | hbQ
      · exact hbP
      · exact hab.2.2.elim
          (fun hab => ((hinc a haP b hbQ).1 hab).elim)
          (fun hba => ((hinc a haP b hbQ).2 hba).elim)
    · intro hbP
      rcases Finset.mem_union.1 hab.1 with haP | haQ
      · exact haP
      · exact hab.2.2.elim
          (fun hab => ((hinc b hbP a haQ).2 hab).elim)
          (fun hba => ((hinc b hbP a haQ).1 hba).elim)
  | refl a => exact Iff.rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
theorem historyComponent_incomparable_union 
    (hinc : IncomparableHistoryParts P Q) (hP : IsConnectedHistorySubset P) {p : α} (hp : p ∈ P) :
    historyComponent (P ∪ Q) p = P := by
  ext x
  constructor
  · intro hx
    exact (historyConnected_preserves_incomparable_part hinc (mem_historyComponent.1 hx).2).1 hp
  · intro hx
    exact mem_historyComponent.2 ⟨Finset.mem_union_left _ hx,
      historyConnected_mono Finset.subset_union_left (hP.2 p hp x hx)⟩
theorem historyGasFamily_component_at  {F : Finset (Finset α)}
    (hF : F ∈ historyGasFamilies (historyUpperPolymers S) historyMaximalPieces R)
     (hP : P ∈ F) {p : α} (hp : p ∈ P) :
    historyComponent (F.biUnion id) p = P := by
  have hupper : ∀ Q ∈ F, IsHistoryUpper S Q :=
    fun _ hQ => (mem_historyUpperPolymers.1 ((mem_historyGasFamilies.1 hF).1 hQ)).1
  have h_historyGasFamily_piece_disjoint : ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → Disjoint P Q := by
    obtain ⟨hFP, hc, _⟩ := mem_historyGasFamilies.1 hF
    intro P hP Q hQ hpq
    exact (historyUpper_disjoint_iff (mem_historyUpperPolymers.1 (hFP hP)).1
      (mem_historyUpperPolymers.1 (hFP hQ)).1).2 (hc P hP Q hQ hpq)
  have hinc := historyUpper_disjoint_incomparable (hupper P hP)
    (historyUpper_biUnion (fun Q hQ => hupper Q (Finset.mem_of_mem_erase hQ))) (by apply Finset.disjoint_left.2; intro x hxP hxF; obtain ⟨Q, hQ, hxQ⟩ := Finset.mem_biUnion.1 hxF; obtain ⟨hQP, hQF⟩ := Finset.mem_erase.1 hQ; exact Finset.disjoint_left.1 (h_historyGasFamily_piece_disjoint P hP Q hQF hQP.symm) hxP hxQ)
  have hUnion : F.biUnion id = P ∪ (F.erase P).biUnion id := by
    conv_lhs => rw [← Finset.insert_erase hP]
    rw [Finset.biUnion_insert, id_eq]
  rw [hUnion]
  exact historyComponent_incomparable_union hinc
    (mem_historyUpperPolymers.1 ((mem_historyGasFamilies.1 hF).1 hP)).2 hp
def historyRestrictedUpperSets (S R : Finset α) : Finset (Finset α) := by
  classical
  exact (historyUpperSets S).filter (fun U => historyMaximalPieces U ⊆ R)
theorem mem_historyRestrictedUpperSets {S R U : Finset α} :
    U ∈ historyRestrictedUpperSets S R ↔ IsHistoryUpper S U ∧ historyMaximalPieces U ⊆ R := by
  simp only [historyRestrictedUpperSets, Finset.mem_filter, mem_historyUpperSets]
def historyRestrictedUpperDensity (weight : α → ℝ) (ρ t : ℝ) (S R : Finset α) : ℝ :=
  ∑ U ∈ historyRestrictedUpperSets S R, historyComponentWeight weight ρ t U
theorem historyRestrictedUpperDensity_eq_gas (weight ρ t) (S R : Finset α) :
    historyRestrictedUpperDensity weight ρ t S R =
      historyGasPartition (historyUpperPolymers S) historyMaximalPieces
        (historyComponentWeight weight ρ t) R := by
  apply Finset.sum_bij (fun U _ => historyComponents U)
  · intro U hU
    obtain ⟨hupper, hmax⟩ := mem_historyRestrictedUpperSets.1 hU
    have h_historyComponents_mem_gas : historyComponents U ∈ historyGasFamilies (historyUpperPolymers S) historyMaximalPieces (historyMaximalPieces U) := by
      rw [mem_historyGasFamilies]
      refine ⟨?_, ?_, ?_⟩
      · intro P hP
        obtain ⟨r, hr, rfl⟩ := mem_historyComponents.1 hP
        have h_historyComponents_connected := historyComponent_connected hr
        exact mem_historyUpperPolymers.2 ⟨historyComponents_upper hupper hP, h_historyComponents_connected⟩
      · intro P hP Q hQ hpq
        exact (historyUpper_disjoint_iff (historyComponents_upper hupper hP)
          (historyComponents_upper hupper hQ)).1 (historyComponents_pairwise_disjoint U P hP Q hQ hpq)
      · intro P hP
        obtain ⟨r, _, rfl⟩ := mem_historyComponents.1 hP
        exact historyUpper_maximal_subset (historyComponent_upper ⟨Finset.Subset.refl _,
          fun _ _ _ hy _ => hy⟩ r)
    obtain ⟨hcP, hcompat, hcSupport⟩ := mem_historyGasFamilies.1 h_historyComponents_mem_gas
    exact mem_historyGasFamilies.2 ⟨hcP, hcompat, fun P hP => (hcSupport P hP).trans hmax⟩
  · intro U hU V hV hUV
    simpa only [historyComponents_biUnion] using (congrArg (fun F => F.biUnion id) hUV)
  · intro F hF
    have h_historyGasFamily_components_biUnion : historyComponents (F.biUnion id) = F := by
      ext P
      constructor
      · intro hP
        obtain ⟨p, hp, rfl⟩ := mem_historyComponents.1 hP
        obtain ⟨Q, hQ, hpQ⟩ := Finset.mem_biUnion.1 hp
        rw [historyGasFamily_component_at hF hQ hpQ]
        exact hQ
      · intro hP
        have hPP := (mem_historyUpperPolymers.1 ((mem_historyGasFamilies.1 hF).1 hP)).2.1
        obtain ⟨p, hp⟩ := hPP
        exact mem_historyComponents.2 ⟨p, Finset.mem_biUnion.2 ⟨P, hP, hp⟩,
          historyGasFamily_component_at hF hP hp⟩
    have h_historyGasFamily_biUnion_restricted : F.biUnion id ∈ historyRestrictedUpperSets S R := by
      apply mem_historyRestrictedUpperSets.2
      have h_historyGasFamily_biUnion_upper  := historyUpper_biUnion (fun _ hP => (mem_historyUpperPolymers.1 ((mem_historyGasFamilies.1 hF).1 hP)).1)
      refine ⟨h_historyGasFamily_biUnion_upper, ?_⟩
      intro x hx
      obtain ⟨hxU, hm⟩ := mem_historyMaximalPieces.1 hx
      obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hxU
      have hxmaxP  := mem_historyMaximalPieces.2 ⟨hxP, fun y hy hxy =>
        hm y (Finset.mem_biUnion.2 ⟨P, hP, hy⟩) hxy⟩
      exact (mem_historyGasFamilies.1 hF).2.2 P hP hxmaxP
    exact ⟨F.biUnion id, h_historyGasFamily_biUnion_restricted, h_historyGasFamily_components_biUnion⟩
  · intro U hU
    exact historyComponentWeight_eq_component_prod weight ρ t (mem_historyRestrictedUpperSets.1 hU).1
theorem historyRestrictedUpperSets_full (S : Finset α) :
    historyRestrictedUpperSets S (historyMaximalPieces S) = historyUpperSets S := by
  ext U
  rw [mem_historyRestrictedUpperSets, mem_historyUpperSets]
  exact ⟨fun h => h.1, fun h => ⟨h, historyUpper_maximal_subset h⟩⟩
end
variable {α : Type*} [PartialOrder α] [DecidableEq α]
def historyCoverEdge (U : Finset α) (a b : α) : Prop :=
  a ∈ U ∧ b ∈ U ∧ (a ⋖ b ∨ b ⋖ a)
def HistoryCoverConnected (U : Finset α) (a b : α) : Prop :=
  Relation.EqvGen (historyCoverEdge U) a b
theorem historyCoverConnected_of_le [Fintype α] 
    (hU : IsHistoryUpper Finset.univ U) {a b : α} (ha : a ∈ U) (hab : a ≤ b) :
    HistoryCoverConnected U a b := by
  classical
  let : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  induction (le_iff_reflTransGen_covBy.1 hab) with
  | refl => exact .refl _
  | @tail c b hac hcb ih =>
    have hac'  := le_iff_reflTransGen_covBy.2 hac
    have hc  := hU.2 a ha c (Finset.mem_univ _) hac'
    have hb  := hU.2 a ha b (Finset.mem_univ _) (hac'.trans hcb.le)
    exact .trans _ _ _ (ih hac') (.rel _ _ ⟨hc, hb, Or.inl hcb⟩)
theorem historyConnected_iff_coverConnected [Fintype α] 
    (hU : IsHistoryUpper Finset.univ U) {a b : α} :
    HistoryConnected U a b ↔ HistoryCoverConnected U a b := by
  constructor
  · intro h
    induction h with
    | rel a b hab =>
      rcases hab.2.2 with hab' | hba'
      · exact historyCoverConnected_of_le hU hab.1 hab'
      · exact .symm _ _ (historyCoverConnected_of_le hU hab.2.1 hba')
    | refl a => exact .refl _
    | symm a b hab ih => exact .symm _ _ ih
    | trans a b c hab hbc ihab ihbc => exact .trans _ _ _ ihab ihbc
  have h_historyCoverConnected_comparable (h : HistoryCoverConnected U a b) : HistoryConnected U a b := by
    exact Relation.EqvGen.mono (r := historyCoverEdge U) (p := historyComparableEdge U)
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)⟩) a b h
  · exact h_historyCoverConnected_comparable
def historyInducedCoverGraph (U : Finset α) : SimpleGraph U where
  Adj a b := (a : α) ⋖ b ∨ (b : α) ⋖ a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (fun h => h.ne rfl) (fun h => h.ne rfl)⟩
def historyCoverGraph (α ) [PartialOrder α] : SimpleGraph α where
  Adj a b := a ⋖ b ∨ b ⋖ a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (fun h => h.ne rfl) (fun h => h.ne rfl)⟩
instance historyCoverGraph_locallyFinite [Fintype α] : (historyCoverGraph α).LocallyFinite :=
  fun _ => Fintype.ofFinite _
theorem historyConnected_iff_coverGraph_reachable [Fintype α] 
    (hU : IsHistoryUpper Finset.univ U) {a b : α} (ha ) (hb : b ∈ U) :
    HistoryConnected U a b ↔ (historyInducedCoverGraph U).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  rw [historyConnected_iff_coverConnected hU]
  have h_historyInducedCoverGraph_reachable_connected {U : Finset α} {a : U} {b : U} (h : (historyInducedCoverGraph U).Reachable a b) : HistoryCoverConnected U a b := by
    obtain ⟨p⟩ := h
    induction p with
    | nil => exact .refl _
    | @cons a c b hac p ih => exact .trans _ _ _ (.rel _ _ ⟨a.prop, c.prop, hac⟩) ih
  have h_historyCoverConnected_reachable (h : HistoryCoverConnected U a b) : (historyInducedCoverGraph U).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
    induction h with
    | rel a b hab => exact (show (historyInducedCoverGraph U).Adj ⟨a, hab.1⟩ ⟨b, hab.2.1⟩ from hab.2.2).reachable
    | refl a => exact SimpleGraph.Reachable.refl _
    | symm a b hab ih => exact (ih hb ha).symm
    | trans a b c hab hbc ihab ihbc =>
      by_cases hbU : b ∈ U
      · exact (ihab ha hbU).trans (ihbc hbU hb)
      · have hs : ∀ {x y}, HistoryCoverConnected U x y → x = y ∨ x ∈ U ∧ y ∈ U := by
          intro x y h
          induction h with
          | rel x y h => exact Or.inr ⟨h.1, h.2.1⟩
          | refl x => exact Or.inl rfl
          | symm x y h ih => exact ih.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
          | trans x y z hxy hyz ihxy ihyz =>
            rcases ihxy with rfl | ⟨hx, hy⟩
            · exact ihyz
            · rcases ihyz with rfl | ⟨_, hz⟩
              · exact Or.inr ⟨hx, hy⟩
              · exact Or.inr ⟨hx, hz⟩
        rcases hs hab with hab' | hab'
        · exact (hbU (hab' ▸ ha)).elim
        · exact (hbU hab'.2).elim
  exact ⟨h_historyCoverConnected_reachable, h_historyInducedCoverGraph_reachable_connected⟩
end
universe u
theorem finite_connected_closed_spanning_walk {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (r : V) :
    ∃ p : G.Walk r r, p.length = 2 * (Fintype.card V - 1) ∧ ∀ v, v ∈ p.support := by
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  have h_finite_tree_closed_spanning_walk : ∃ p : T.Walk r r, p.length = 2 * (Fintype.card V - 1) ∧ ∀ v, v ∈ p.support := by
    classical
    have hmain : ∀ n : ℕ, ∀ (V : Type u) [Fintype V], Fintype.card V = n →
        ∀ (T : SimpleGraph V), T.IsTree → ∀ r : V,
          ∃ p : T.Walk r r, p.length = 2 * (Fintype.card V - 1) ∧ ∀ v, v ∈ p.support := by
      intro n
      induction n using Nat.strong_induction_on
      rename_i n ih
      intro V instV hcard T hT r
      by_cases hs : Subsingleton V
      · let : Subsingleton V := hs
        let : Unique V := { default := r, uniq := fun v => Subsingleton.elim v r }
        refine ⟨.nil, by simp, ?_⟩
        intro v
        simp [Subsingleton.elim v r]
      · let : Nontrivial V := not_subsingleton_iff_nontrivial.1 hs
        obtain ⟨a, b, hab, ha, hb⟩ := hT.exists_ne_and_degree_eq_one
        have hleaf : ∃ v : V, v ≠ r ∧ T.degree v = 1 := by
          by_cases har : a = r
          · exact ⟨b, fun hbr => hab (har.trans hbr.symm), hb⟩
          · exact ⟨a, har, ha⟩
        obtain ⟨v, hvr, hdeg⟩ := hleaf
        let S : Set V := {v}ᶜ
        let T' := T.induce S
        let r' : S := ⟨r, by simpa [S] using hvr.symm⟩
        have hT' : T'.IsTree := {
          connected := hT.connected.induce_compl_singleton_of_degree_eq_one hdeg
          isAcyclic := hT.isAcyclic.induce S }
        have : Fintype.card S = Fintype.card V - 1 := by
          simp only [S, Fintype.card_compl_set, Fintype.card_unique]
        obtain ⟨p', hp'len, hp'all⟩ := ih (Fintype.card S) (by rw [← hcard]; exact Fintype.card_subtype_lt (x := v) (by simp [S])) S rfl T' hT' r'
        let f : T' →g T := { toFun := Subtype.val, map_rel' := fun h => h }
        let p : T.Walk r r := p'.map f
        have hplen : p.length = 2 * (Fintype.card S - 1) := by
          simpa only [p, SimpleGraph.Walk.length_map] using hp'len
        have hpall : ∀ x : V, x ≠ v → x ∈ p.support := by
          intro x hxv
          rw [show p = p'.map f from rfl, SimpleGraph.Walk.support_map]
          exact List.mem_map.2 ⟨⟨x, by simpa [S] using hxv⟩, hp'all _, rfl⟩
        obtain ⟨w, hvw, _⟩ := T.degree_eq_one_iff_existsUnique_adj.1 hdeg
        have hwv  := hvw.ne.symm
        have hwp := hpall w hwv
        let left := p.takeUntil w hwp
        let right := p.dropUntil w hwp
        let excursion : T.Walk w w := .cons hvw.symm (.cons hvw .nil)
        let q := (left.append excursion).append right
        have : left.length + right.length = p.length := by
          have hh := congrArg SimpleGraph.Walk.length (p.take_spec hwp)
          simpa only [SimpleGraph.Walk.length_append] using hh
        have hqLen : q.length = 2 * (Fintype.card V - 1) := by
          simp only [q, excursion, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
            SimpleGraph.Walk.length_nil]
          have : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff_nontrivial.2 inferInstance
          omega
        refine ⟨q, hqLen, ?_⟩
        intro x
        by_cases hxv : x = v
        · subst x
          simp only [q, SimpleGraph.Walk.mem_support_append_iff, excursion,
            SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons]
          exact Or.inl (Or.inr (Or.inr (Or.inl trivial)))
        · have hx := hpall x hxv
          have hxsplit : x ∈ left.support ∨ x ∈ right.support := by
            rw [← p.take_spec hwp, SimpleGraph.Walk.mem_support_append_iff] at hx
            exact hx
          simp only [q, SimpleGraph.Walk.mem_support_append_iff]
          exact hxsplit.elim (fun hx => Or.inl (Or.inl hx)) Or.inr
    exact hmain (Fintype.card V) V rfl T hT r
  obtain ⟨p, hplen, hpall⟩ := h_finite_tree_closed_spanning_walk
  exact ⟨p.mapLe hTG, by simpa only [SimpleGraph.Walk.length_mapLe] using hplen,
    fun v => by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hpall v⟩
theorem graph_walk_count_le  [DecidableEq V] (G : SimpleGraph V)
    [G.LocallyFinite] (D ) (hD : ∀ v, G.degree v ≤ D) (n u v) :
    (G.finsetWalkLength n u v).card ≤ D ^ n := by
  induction n generalizing u with
  | zero =>
    simp only [SimpleGraph.finsetWalkLength]
    split_ifs with h
    · subst u; simp
    · simp
  | succ n ih =>
    rw [SimpleGraph.finsetWalkLength]
    calc
      _ ≤ ∑ w : G.neighborSet u,
          ((G.finsetWalkLength n w v).map ⟨fun p => SimpleGraph.Walk.cons w.prop p, fun a b hab => by cases hab; rfl⟩).card :=
        Finset.card_biUnion_le
      _ = ∑ w : G.neighborSet u, (G.finsetWalkLength n w v).card := by simp
      _ ≤ ∑ _w : G.neighborSet u, D ^ n := Finset.sum_le_sum (fun _ _ => ih _)
      _ = G.degree u * D ^ n := by simp
      _ ≤ D * D ^ n := Nat.mul_le_mul_right _ (hD u)
      _ = D ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
def graphConnectedSubsets  [Fintype V] (G : SimpleGraph V) (x : V) (k : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter (fun P => x ∈ P ∧ P.card = k ∧ (G.induce (P : Set V)).Connected)
theorem mem_graphConnectedSubsets  [Fintype V] {G : SimpleGraph V}   {P : Finset V} :
    P ∈ graphConnectedSubsets G x k ↔ x ∈ P ∧ P.card = k ∧ (G.induce (P : Set V)).Connected := by
  simp [graphConnectedSubsets]
theorem graph_connected_subsets_card_le  [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (x : V) (k : ℕ) :
    (graphConnectedSubsets G x k).card ≤ D ^ (2 * (k - 1)) := by
  have h_graphConnectedSubset_closed_walk {P : Finset V} (hP : P ∈ graphConnectedSubsets G x k) : ∃ p : G.Walk x x, p.length = 2 * (k - 1) ∧ p.support.toFinset = P := by
    obtain ⟨hx, hcard, hconn⟩ := mem_graphConnectedSubsets.1 hP
    let x' : P := ⟨x, hx⟩
    obtain ⟨p, hplen, hpall⟩ := finite_connected_closed_spanning_walk (G.induce (P : Set V)) hconn x'
    refine ⟨p.map ({ toFun := Subtype.val, map_rel' := fun h => h }), ?_, ?_⟩
    · have hc : Fintype.card (P : Set V) = P.card :=
        Fintype.card_ofFinset P (fun _ => Iff.rfl)
      simpa only [SimpleGraph.Walk.length_map, hc, hcard] using hplen
    · ext y
      rw [List.mem_toFinset, SimpleGraph.Walk.support_map, List.mem_map]
      constructor
      · rintro ⟨z, hz, hzy⟩
        exact hzy ▸ z.prop
      · intro hy
        exact ⟨⟨y, hy⟩, hpall _, rfl⟩
  let f : Finset V → G.Walk x x := fun P =>
    if hP : P ∈ graphConnectedSubsets G x k then Classical.choose (h_graphConnectedSubset_closed_walk hP) else .nil
  have hf : ∀ P ∈ graphConnectedSubsets G x k,
      (f P).length = 2 * (k - 1) ∧ (f P).support.toFinset = P := by
    intro P hP
    dsimp only [f]
    rw [dite_eq_left hP]
    exact Classical.choose_spec (h_graphConnectedSubset_closed_walk hP)
  calc
    _ ≤ (G.finsetWalkLength (2 * (k - 1)) x x).card := by
      apply Finset.card_le_card_of_injOn f
      · intro P hP
        exact SimpleGraph.mem_finsetWalkLength_iff.2 (hf P hP).1
      · intro P hP Q hQ hPQ
        calc
          P = (f P).support.toFinset := (hf P hP).2.symm
          _ = (f Q).support.toFinset := by rw [hPQ]
          _ = Q := (hf Q hQ).2
    _ ≤ _ := graph_walk_count_le G D hD _ _ _
end NearlyMinimax
end
section
namespace NearlyMinimax
theorem history_finite_geom_sum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    (∑ j ∈ Finset.range N, r ^ j) ≤ 1 / (1 - r) := by
  apply (le_div_iff₀ (sub_pos.2 hr1)).2
  rw [geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg hr N)
variable {α : Type*} [PartialOrder α] [DecidableEq α] [Fintype α]
theorem historyUpperDensity_bounds_of_degree_bound (weight : α → ℝ) (ρ t B : ℝ)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B) (hw : ∀ x, |weight x| ≤ B)
    (D : ℕ) (hD : ∀ x : α, (historyCoverGraph α).degree x ≤ D)
    (hsmall : t * B / ρ ≤ 1 / (2 + 2 * (D : ℝ) ^ 2)) :
    (1 / 2 : ℝ) ^ (historyMaximalPieces (Finset.univ : Finset α)).card ≤
        historyScaledUpperDensity weight ρ Finset.univ t ∧
      historyScaledUpperDensity weight ρ Finset.univ t ≤
        (3 / 2 : ℝ) ^ (historyMaximalPieces (Finset.univ : Finset α)).card := by
  have h_historyUpperDensity_positive_of_degree_bound : ∀ R, 0 < historyRestrictedUpperDensity weight ρ t Finset.univ R ∧ ∀ x ∈ R,
      historyRestrictedUpperDensity weight ρ t Finset.univ (R.erase x) / 2 ≤
        historyRestrictedUpperDensity weight ρ t Finset.univ R ∧
      historyRestrictedUpperDensity weight ρ t Finset.univ R ≤
        3 / 2 * historyRestrictedUpperDensity weight ρ t Finset.univ (R.erase x) := by
    have h_historyRestrictedUpperDensity_positive (S : Finset α) (hactivity : ∀ R x, x ∈ R →
      (∑ P ∈ historyGasRows (historyUpperPolymers S) historyMaximalPieces R x,
        |historyComponentWeight weight ρ t P| * ↑2 ^ ((historyMaximalPieces P).card - 1)) ≤ 1 / 2) : ∀ R, 0 < historyRestrictedUpperDensity weight ρ t S R ∧ ∀ x ∈ R,
      historyRestrictedUpperDensity weight ρ t S (R.erase x) / 2 ≤ historyRestrictedUpperDensity weight ρ t S R ∧
      historyRestrictedUpperDensity weight ρ t S R ≤ 3 / 2 * historyRestrictedUpperDensity weight ρ t S (R.erase x) := by
      simp_rw [historyRestrictedUpperDensity_eq_gas]
      exact historyGasPartition_positive (historyUpperPolymers S) historyMaximalPieces
        (historyComponentWeight weight ρ t) (fun _ hP => historyUpperPolymer_support_nonempty hP) hactivity
    apply h_historyRestrictedUpperDensity_positive
    intro R x hx
    let A := historyGasRows (historyUpperPolymers Finset.univ) historyMaximalPieces R x
    let ε := t * B / ρ
    have hε  := div_nonneg (mul_nonneg ht hB) hρ.le
    have h_history_degree_activity_threshold : 0 ≤ 2 * D ^ 2 * ε ∧ 2 * D ^ 2 * ε < 1 ∧ ε / (1 - 2 * D ^ 2 * ε) ≤ 1 / 2 := by
      have := (le_div_iff₀ (by positivity)).1 hsmall
      have hp : 0 < 1 - 2 * D ^ 2 * ε := by
        by_cases he : ε = 0
        · simp [he]
        · have  := lt_of_le_of_ne hε (Ne.symm he)
          nlinarith
      refine ⟨by positivity, by linarith, (div_le_iff₀ hp).2 ?_⟩
      nlinarith
    have hthreshold := h_history_degree_activity_threshold
    have hterm : ∀ P ∈ A,
        |historyComponentWeight weight ρ t P| * ↑2 ^ ((historyMaximalPieces P).card - 1) ≤
          ε ^ P.card * ↑2 ^ (P.card - 1) := by
      intro P hP
      have h_historyComponentWeight_abs_le : |historyComponentWeight weight ρ t P| ≤ (t * B / ρ) ^ P.card := by
        have hw : ∀ x ∈ P, |weight x| ≤ B := fun y _ => hw y
        have hp  := div_nonneg ht hρ.le
        have hprod : (∏ x ∈ P, |weight x|) ≤ B ^ P.card := by
          calc
            _ ≤ ∏ _x ∈ P, B := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hw
            _ = _ := by simp
        unfold historyComponentWeight
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hp _),
          abs_of_nonneg (historyOrderVolume_nonneg P), Finset.abs_prod]
        have h_historyOrderVolume_le_one  := (div_le_one (by positivity : 0 < (P.card.factorial : ℝ))).2 (historyOrderCount_le_factorial P)
        calc
          _ ≤ (t / ρ) ^ P.card * 1 * (B ^ P.card) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h_historyOrderVolume_le_one (pow_nonneg hp _))
              hprod (by positivity) (by positivity)
          _ = _ := by rw [mul_one, ← mul_pow]; congr 1; ring
      have hc := h_historyComponentWeight_abs_le
      have hm  :=
        Nat.sub_le_sub_right (Finset.card_le_card (historyMaximalPieces_subset P)) 1
      exact mul_le_mul hc (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm)
        (by positivity) (pow_nonneg hε _)
    have hfiber : ∀ j,
        (∑ P ∈ A.filter (fun P => P.card - 1 = j),
          |historyComponentWeight weight ρ t P| * ↑2 ^ ((historyMaximalPieces P).card - 1)) ≤
            ↑D ^ (2 * j) * (ε ^ (j + 1) * ↑2 ^ j) := by
      intro j
      calc
        _ ≤ ∑ _P ∈ A.filter (fun P => P.card - 1 = j), ε ^ (j + 1) * ↑2 ^ j := by
          apply Finset.sum_le_sum
          intro P hP
          obtain ⟨hPA, hsize⟩ := Finset.mem_filter.1 hP
          have hxP := historyMaximalPieces_subset P (Finset.mem_filter.1 hPA).2.1
          have hcard : P.card = j + 1 := by
            have hpos := Finset.card_pos.2 ⟨x, hxP⟩
            omega
          simpa only [hcard, Nat.add_sub_cancel] using hterm P hPA
        _ = ((A.filter (fun P => P.card - 1 = j)).card : ℝ) * (ε ^ (j + 1) * ↑2 ^ j) := by simp
        _ ≤ _ := by
          have h_historyUpperRows_card_by_size : ((historyGasRows (historyUpperPolymers Finset.univ) historyMaximalPieces R x).filter
        (fun P => P.card - 1 = j)).card ≤ D ^ (2 * j) := by
            calc
              _ ≤ (graphConnectedSubsets (historyCoverGraph α) x (j + 1)).card := by
                apply Finset.card_le_card
                intro P hP
                obtain ⟨hProw, hsize⟩ := Finset.mem_filter.1 hP
                obtain ⟨hPpoly, hxmax, _⟩ := Finset.mem_filter.1 hProw
                have hxP := historyMaximalPieces_subset P hxmax
                have hpos := Finset.card_pos.2 ⟨x, hxP⟩
                obtain ⟨hupper, hconn⟩ := mem_historyUpperPolymers.1 hPpoly
                obtain ⟨x, hx⟩ := hconn.1
                let : Nonempty (P : Set α) := ⟨⟨x, hx⟩⟩
                exact mem_graphConnectedSubsets.2 ⟨hxP, by omega, (by constructor; intro a b; exact (historyConnected_iff_coverGraph_reachable hupper a.prop b.prop).1 (hconn.2 a a.prop b b.prop))⟩
              _ ≤ _ := by
                simpa only [Nat.add_sub_cancel] using
                  (graph_connected_subsets_card_le (historyCoverGraph α) D hD x (j + 1))
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast h_historyUpperRows_card_by_size
    calc
      _ = ∑ j ∈ Finset.range (Fintype.card α),
          ∑ P ∈ A.filter (fun P => P.card - 1 = j),
            |historyComponentWeight weight ρ t P| * ↑2 ^ ((historyMaximalPieces P).card - 1) :=
        (Finset.sum_fiberwise_of_maps_to (by intro P hP; have hxP := historyMaximalPieces_subset P (Finset.mem_filter.1 hP).2.1; have hpos := Finset.card_pos.2 ⟨x, hxP⟩; have := Finset.card_le_univ P; exact Finset.mem_range.2 (by omega)) _).symm
      _ ≤ ∑ j ∈ Finset.range (Fintype.card α),
          ↑D ^ (2 * j) * (ε ^ (j + 1) * ↑2 ^ j) := Finset.sum_le_sum (fun j _ => hfiber j)
      _ = ε * ∑ j ∈ Finset.range (Fintype.card α), (2 * ↑D ^ 2 * ε) ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_mul, pow_succ, mul_pow, mul_pow]
        ring
      _ ≤ ε * (1 / (1 - 2 * ↑D ^ 2 * ε)) :=
        mul_le_mul_of_nonneg_left (history_finite_geom_sum_le hthreshold.1 hthreshold.2.1 _) hε
      _ = ε / (1 - 2 * ↑D ^ 2 * ε) := by ring
      _ ≤ 1 / 2 := hthreshold.2.2
  have hpos := h_historyUpperDensity_positive_of_degree_bound
  have h_historyRestrictedUpperDensity_empty : historyRestrictedUpperDensity weight ρ t Finset.univ ∅ = 1 := by
    rw [historyRestrictedUpperDensity_eq_gas]
    exact historyGasPartition_empty (historyUpperPolymers Finset.univ) historyMaximalPieces
      (historyComponentWeight weight ρ t) (fun _ hP => historyUpperPolymer_support_nonempty hP)
  have hb := deletion_ratios_global_bounds (historyRestrictedUpperDensity weight ρ t Finset.univ)
    h_historyRestrictedUpperDensity_empty (fun R x hx => (hpos R).2 x hx)
    (historyMaximalPieces (Finset.univ : Finset α))
  have heq : historyRestrictedUpperDensity weight ρ t Finset.univ (historyMaximalPieces Finset.univ) =
      historyScaledUpperDensity weight ρ Finset.univ t := by
    unfold historyRestrictedUpperDensity
    rw [historyRestrictedUpperSets_full, historyScaledUpperDensity_eq_components]
  rwa [heq] at hb
end NearlyMinimax
namespace NearlyMinimax
end NearlyMinimax
end
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
section
section
section
inductive IndependentHistoryExchange {α : Type*} (independent : α → α → Prop) : List α → List α → Prop
  | swap (before after : List α) (x y : α) (hxy : independent x y) :
      IndependentHistoryExchange independent (before ++ x :: y :: after) (before ++ y :: x :: after)
def historyShapeSetoid  (independent : α → α → Prop) : Setoid (List α) where
  r := Relation.EqvGen (IndependentHistoryExchange independent)
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩
def HistoryShape {α : Type*} (independent : α → α → Prop) := Quotient (historyShapeSetoid independent)
def historyWordState  (update : α → X → X) (initial : X) (word : List α) : X :=
  word.foldl (fun state piece => update piece state) initial
instance historyShape_countable {α : Type*} [Countable α] (independent : α → α → Prop) :
    Countable (HistoryShape independent) := by
  unfold HistoryShape
  infer_instance
def affinePatchUpdate  (patch : Set X) (A B state : X → ℝ) : X → ℝ := by
  classical
  exact fun x => if x ∈ patch then A x * state x + B x else state x
def responseCoordinateUpdate  [DecidableEq α]
    (j : α) (response : E → E) (state : α → E) : α → E := Function.update state j (response (state j))
def rawPatchUpdate {α X E : Type*} [DecidableEq α] (j : α) (patch : Set X)
    (A B : X → ℝ) (response : E → E) (state : (X → ℝ) × (α → E)) : (X → ℝ) × (α → E) :=
  (affinePatchUpdate patch A B state.1, responseCoordinateUpdate j response state.2)
variable {J : Type*}
theorem historyShapeRelation_cons {independent : J → J → Prop} (a ) 
    (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) :
    Relation.EqvGen (IndependentHistoryExchange independent) (a :: u) (a :: v) := by
  induction h with
  | rel _ _ h =>
    cases h with
    | swap before after x y hxy =>
      exact .rel _ _ (IndependentHistoryExchange.swap (a :: before) after x y hxy)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
variable [DecidableEq J]
def historyPairProjection (i j : J) (word : List J) : List J :=
  word.filter (fun x => decide (x = i ∨ x = j))
theorem history_dependent_pair_members {dependent : J → J → Prop}
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {i j x y : J} (hij : dependent i j) (hx : x = i ∨ x = j) (hy : y = i ∨ y = j) :
    dependent x y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact hrefl _
  · exact hij
  · exact hsymm hij
  · exact hrefl _
theorem historyPairProjection_shape_invariant {dependent : J → J → Prop}
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
     (hij : dependent i j) 
    (h : Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v) :
    historyPairProjection i j u = historyPairProjection i j v := by
  have h_historyPairProjection_exchange {u} {v} (h : IndependentHistoryExchange (fun a b => ¬ dependent a b) u v) : historyPairProjection i j u = historyPairProjection i j v := by
    cases h with
    | swap before after x y hxy =>
      by_cases hx : x = i ∨ x = j
      · have hy : ¬ (y = i ∨ y = j) := fun hy => hxy (history_dependent_pair_members hrefl hsymm hij hx hy)
        simp [historyPairProjection, List.filter_append, hx, hy]
      · by_cases hy : y = i ∨ y = j <;> simp [historyPairProjection, List.filter_append, hx, hy]
  induction h with
  | rel _ _ h => exact h_historyPairProjection_exchange h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
theorem history_first_decomposition  {word : List J} (ha : a ∈ word) :
    ∃ before after, word = before ++ a :: after ∧ a ∉ before := by
  induction word with
  | nil => simp at ha
  | cons b word ih =>
    by_cases hba : b = a
    · subst b; exact ⟨[], word, rfl, by simp⟩
    · have ha'  := (List.mem_cons.1 ha).resolve_left (Ne.symm hba)
      obtain ⟨before, after, hword, hbefore⟩ := ih ha'
      exact ⟨b :: before, after, by simp [hword], by simp [hbefore, Ne.symm hba]⟩
theorem historyPairProjection_prefix_head  {before after : List J}
    (ha : a ∉ before) (hb : b ∈ before) :
    (historyPairProjection a b (before ++ a :: after)).head? = some b := by
  induction before with
  | nil => simp at hb
  | cons c before ih =>
    have hca : c ≠ a := fun h => ha (List.mem_cons.2 (Or.inl h.symm))
    have habefore  := fun h => ha (List.mem_cons.2 (Or.inr h))
    by_cases hcb : c = b
    · subst c; simp [historyPairProjection]
    · have hbbefore  := (List.mem_cons.1 hb).resolve_left (Ne.symm hcb)
      simpa [historyPairProjection, hca, hcb] using ih habefore hbbefore
theorem historyShapeRelation_move_first {independent : J → J → Prop} (a before after)
    (hbefore : ∀ b ∈ before, independent b a) :
    Relation.EqvGen (IndependentHistoryExchange independent) (before ++ a :: after) (a :: (before ++ after)) := by
  induction before with
  | nil => exact .refl _
  | cons b before ih =>
    exact .trans _ _ _ (historyShapeRelation_cons b (ih (fun c hc => hbefore c (List.mem_cons_of_mem _ hc))))
      (.rel _ _ (IndependentHistoryExchange.swap [] (before ++ after) b a (hbefore b (List.mem_cons_self))))
theorem historyShapeRelation_of_pair_projections {dependent : J → J → Prop}
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
     (hproj : ∀ i j, dependent i j → historyPairProjection i j u = historyPairProjection i j v) :
    Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact .refl _
    | cons b v =>
      have hh := congrArg List.head? (hproj b b (hrefl b))
      simp [historyPairProjection] at hh
  | cons a u ih =>
    have hm : a ∈ historyPairProjection a a (a :: u) := by simp [historyPairProjection]
    obtain ⟨before, after, hv, ha⟩ := history_first_decomposition (by rw [hproj a a (hrefl a)] at hm; exact (List.mem_filter.1 hm).1)
    have hind : ∀ b ∈ before, ¬ dependent b a := by
      intro b hb hba
      have hh := congrArg List.head? (hproj a b (hsymm hba))
      rw [hv, historyPairProjection_prefix_head ha hb] at hh
      have hab : a = b := by simpa [historyPairProjection] using hh
      exact ha (hab ▸ hb)
    have hmove := historyShapeRelation_move_first (independent := fun b c => ¬ dependent b c) a before after hind
    have hrest : ∀ i j, dependent i j → historyPairProjection i j u = historyPairProjection i j (before ++ after) := by
      intro i j hij
      have hm : historyPairProjection i j v = historyPairProjection i j (a :: (before ++ after)) := by
        rw [hv]
        exact historyPairProjection_shape_invariant hrefl hsymm hij hmove
      have hh := (hproj i j hij).trans hm
      by_cases hai : a = i ∨ a = j
      · simpa [historyPairProjection, hai] using hh
      · simpa [historyPairProjection, hai] using hh
    rw [hv]
    exact .trans _ _ _ (historyShapeRelation_cons a (ih hrest)) (.symm _ _ hmove)
def historyShapePairCode (dependent : J → J → Prop)
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) :
    HistoryShape (fun a b => ¬ dependent a b) → ({p : J × J // dependent p.1 p.2} → List J) :=
  Quotient.lift (fun word p => historyPairProjection p.val.1 p.val.2 word)
    (fun _ _ h => funext (fun p => historyPairProjection_shape_invariant hrefl hsymm p.prop h))
end
section
variable {J : Type*} [DecidableEq J]
theorem historyWord_count_shape_invariant (independent j) {u v : List J}
    (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) : u.count j = v.count j := by
  induction h with
  | rel _ _ h =>
    cases h with
    | swap before after x y hxy => simp [List.count_append, List.count_cons, Nat.add_comm, Nat.add_left_comm]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
def historyShapeMultiplicity (dependent : J → J → Prop) (j : J) :
    HistoryShape (fun a b => ¬ dependent a b) → ℕ :=
  Quotient.lift (List.count j) (fun _ _ h => historyWord_count_shape_invariant _ j h)
theorem historyShapeMultiplicity_out (dependent ) (j : J)
    (g : HistoryShape (fun a b => ¬ dependent a b)) :
    (Quotient.out g).count j = historyShapeMultiplicity dependent j g := congrArg (historyShapeMultiplicity dependent j) (Quotient.out_eq g)
abbrev HistoryMultiplicityShape (dependent : J → J → Prop) (n : J → ℕ) :=
  {g : HistoryShape (fun a b => ¬ dependent a b) // ∀ j, historyShapeMultiplicity dependent j g = n j}
theorem historyPairProjection_symm (i j : J) (word : List J) :
    historyPairProjection i j word = historyPairProjection j i word := by
  unfold historyPairProjection
  congr 1
  funext x
  simp only [or_comm]
theorem historyPairProjection_self (j ) (word : List J) :
    historyPairProjection j j word = List.replicate (word.count j) j := by
  induction word with
  | nil => simp [historyPairProjection]
  | cons a word ih =>
    by_cases haj : a = j
    · subst a
      simpa [historyPairProjection, List.replicate_succ] using congrArg (List.cons j) ih
    · simpa [historyPairProjection, haj] using ih
def historyPairBits (i j : J) (word : List J) : List Bool :=
  (historyPairProjection i j word).map (fun x => decide (x = j))
theorem historyPairBits_length  (hij : i ≠ j) (word : List J) :
    (historyPairBits i j word).length = word.count i + word.count j := by
  have h_historyPairProjection_length (word : List J) : (historyPairProjection i j word).length = word.count i + word.count j := by
    induction word with
    | nil => simp [historyPairProjection]
    | cons a word ih =>
      by_cases hai : a = i
      · subst a
        simp [historyPairProjection] at ih
        simp [historyPairProjection, hij]
        omega
      · by_cases haj : a = j
        · subst a
          simp [historyPairProjection] at ih
          simp [historyPairProjection, Ne.symm hij]
          omega
        · simpa [historyPairProjection, List.count_cons, hai, haj] using ih
  rw [historyPairBits, List.length_map, h_historyPairProjection_length]
theorem historyPairProjection_eq_of_bits_eq {i j : J} (hij : i ≠ j) {u v : List J}
    (h : historyPairBits i j u = historyPairBits i j v) : historyPairProjection i j u = historyPairProjection i j v := by
  have h_historyPairBits_reconstruct (word : List J) : (historyPairBits i j word).map (fun b => if b then j else i) = historyPairProjection i j word := by
    unfold historyPairBits
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (historyPairProjection i j word)]
    apply List.map_congr_left
    intro x hx
    rcases (of_decide_eq_true (List.mem_filter.1 hx).2) with rfl | rfl
    · simp [hij]
    · simp
  rw [← h_historyPairBits_reconstruct u, ← h_historyPairBits_reconstruct v, h]
abbrev HistoryOrderedDependentPair (dependent : J → J → Prop) [LinearOrder J] :=
  {p : J × J // p.1 < p.2 ∧ dependent p.1 p.2}
instance historyOrderedDependentPair_fintype [Fintype J] [LinearOrder J] (dependent : J → J → Prop) :
    Fintype (HistoryOrderedDependentPair dependent) := Fintype.ofFinite _
def historyMultiplicityPairCode (dependent : J → J → Prop) [LinearOrder J] (n : J → ℕ)
    (g : HistoryMultiplicityShape dependent n) :
    ∀ p : HistoryOrderedDependentPair dependent, List.Vector Bool (n p.val.1 + n p.val.2) := fun p =>
  ⟨historyPairBits p.val.1 p.val.2 (Quotient.out g.val), by
    rw [historyPairBits_length p.prop.1.ne, historyShapeMultiplicity_out, historyShapeMultiplicity_out,
      g.prop p.val.1, g.prop p.val.2]⟩
theorem historyMultiplicityPairCode_injective (dependent : J → J → Prop) [LinearOrder J]
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (n : J → ℕ) :
    Function.Injective (historyMultiplicityPairCode dependent n) := by
  intro g h hcode
  have hproj : ∀ i j, dependent i j → historyPairProjection i j (Quotient.out g.val) = historyPairProjection i j (Quotient.out h.val) := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have he := congrArg Subtype.val (congrFun hcode ⟨⟨i, j⟩, hlt, hij⟩)
      exact historyPairProjection_eq_of_bits_eq hlt.ne he
    · subst j
      rw [historyPairProjection_self, historyPairProjection_self, historyShapeMultiplicity_out,
        historyShapeMultiplicity_out, g.prop i, h.prop i]
    · have he := congrArg Subtype.val (congrFun hcode ⟨⟨j, i⟩, hgt, hsymm hij⟩)
      rw [historyPairProjection_symm i j, historyPairProjection_symm i j]
      exact historyPairProjection_eq_of_bits_eq hgt.ne he
  apply Subtype.ext
  exact (Quotient.out_eq g.val).symm.trans ((Quotient.sound (historyShapeRelation_of_pair_projections hrefl hsymm hproj)).trans (Quotient.out_eq h.val))
theorem historyMultiplicityShape_finite [Fintype J] [LinearOrder J] (dependent : J → J → Prop)
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (n : J → ℕ) :
    Finite (HistoryMultiplicityShape dependent n) :=
  Finite.of_injective _ (historyMultiplicityPairCode_injective dependent hrefl hsymm n)
end
variable {J : Type*} [Fintype J] [LinearOrder J]
def historyIncidentPairs (dependent : J → J → Prop) (j : J) : Finset (HistoryOrderedDependentPair dependent) := by
  classical
  exact Finset.univ.filter (fun p => p.val.1 = j ∨ p.val.2 = j)
def historyPairOtherLabel (dependent : J → J → Prop) (j : J)
    (p : HistoryOrderedDependentPair dependent) : J := if p.val.1 = j then p.val.2 else p.val.1
end
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyWord_sum_count (word : List J) : (∑ j : J, word.count j) = word.length := by
  induction word with
  | nil => simp
  | cons a word ih =>
    have hc : ∀ j, (a :: word).count j = word.count j + if j = a then 1 else 0 := by
      intro j
      by_cases hja : j = a
      · subst j; simp
      · simp [hja, Ne.symm hja]
    simp_rw [hc]
    rw [Finset.sum_add_distrib, ih]
    simp
def historyShapeLength (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : ℕ := ∑ j : J, historyShapeMultiplicity dependent j g
theorem historyShapeLength_mk (dependent : J → J → Prop) (word : List J) :
    historyShapeLength dependent (Quotient.mk _ word) = word.length := historyWord_sum_count word
def historyReferenceRho (Δ : ℕ) : ℝ := (1 / 2 ) ^ (Δ + 1)
theorem historyReferenceRho_pos (Δ ) : 0 < historyReferenceRho Δ := by
  unfold historyReferenceRho
  positivity
def historyShapeReferenceWeight (dependent : J → J → Prop) (Δ : ℕ)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : ℝ :=
  historyReferenceRho Δ ^ historyShapeLength dependent g
theorem historyReferenceWeight_finite_sum_le (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (A : Finset (HistoryShape (fun a b => ¬ dependent a b))) :
    (∑ g ∈ A, historyShapeReferenceWeight dependent Δ g) ≤ (4 / 3 : ℝ) ^ Fintype.card J := by
  have h_historyIncidentPair_reconstruct (j : J) (p : HistoryOrderedDependentPair dependent) (hp : p ∈ historyIncidentPairs dependent j) : p.val = if j < historyPairOtherLabel dependent j p then
      (j, historyPairOtherLabel dependent j p) else (historyPairOtherLabel dependent j p, j) := by
    rcases p with ⟨⟨a, b⟩, hab, hdep⟩
    obtain ⟨_, hp⟩ := Finset.mem_filter.1 hp
    rcases hp with rfl | rfl
    · simp [historyPairOtherLabel, hab]
    · simp [historyPairOtherLabel, hab.ne, not_lt_of_gt hab]
  let code := fun g => (fun j => historyShapeMultiplicity dependent j g)
  let C := A.image code
  let N := (∑ n ∈ C, ∑ j : J, n j) + 1
  have hbox : C ⊆ Fintype.piFinset (fun _ : J => Finset.range N) := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro j
    have h1 : n j ≤ ∑ i : J, n i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : (∑ j : J, n j) ≤ ∑ m ∈ C, ∑ j : J, m j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hn
    exact Finset.mem_range.2 (by dsimp [N]; omega)
  calc
    _ = ∑ n ∈ C, ∑ g ∈ A.filter (fun g => code g = n), historyShapeReferenceWeight dependent Δ g :=
      (Finset.sum_fiberwise_of_maps_to (fun g hg => Finset.mem_image_of_mem code hg) _).symm
    _ ≤ ∑ n ∈ C, (1 / 4 ) ^ (∑ j : J, n j) := by
      apply Finset.sum_le_sum
      intro n hn
      have heq : (∑ g ∈ A.filter (fun g => (fun j => historyShapeMultiplicity dependent j g) = n),
          historyShapeReferenceWeight dependent Δ g) =
          ((A.filter (fun g => (fun j => historyShapeMultiplicity dependent j g) = n)).card : ℝ) *
            historyReferenceRho Δ ^ (∑ j : J, n j) := by
        calc
          _ = ∑ _g ∈ A.filter (fun g => (fun j => historyShapeMultiplicity dependent j g) = n),
              historyReferenceRho Δ ^ (∑ j : J, n j) := by
            apply Finset.sum_congr rfl
            intro g hg
            have he := (Finset.mem_filter.1 hg).2
            unfold historyShapeReferenceWeight historyShapeLength
            rw [he]
          _ = _ := by simp
      rw [heq]
      calc
        _ ≤ 2 ^ ((Δ - 1) * ∑ j : J, n j) * historyReferenceRho Δ ^ (∑ j : J, n j) := by
          have h_historyFiniteMultiplicityFiber_card_le : (A.filter (fun g => (fun j => historyShapeMultiplicity dependent j g) = n)).card ≤
          2 ^ ((Δ - 1) * ∑ j : J, n j) := by
            let F := A.filter (fun g => (fun j => historyShapeMultiplicity dependent j g) = n)
            let f : F → HistoryMultiplicityShape dependent n := fun g =>
              ⟨g.val, fun j => congrFun (Finset.mem_filter.1 g.prop).2 j⟩
            let : Finite (HistoryMultiplicityShape dependent n) := historyMultiplicityShape_finite dependent hrefl hsymm n
            have hh := Nat.card_le_card_of_injective f (by intro g h heq; exact Subtype.ext (congrArg (fun z => z.val) heq))
            have hF : Nat.card F = F.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
            rw [hF] at hh
            have h_historyMultiplicityShape_card_le_degree : Nat.card (HistoryMultiplicityShape dependent n) ≤ 2 ^ ((Δ - 1) * ∑ j : J, n j) := by
              have h_historyPairExponent_le : (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) ≤ (Δ - 1) * ∑ j : J, n j := by
                have h_historyPairExponent_incidence : (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) =
                    ∑ j : J, (historyIncidentPairs dependent j).card * n j := by
                  have hp : ∀ p : HistoryOrderedDependentPair dependent,
                      n p.val.1 + n p.val.2 = ∑ j : J, if p.val.1 = j ∨ p.val.2 = j then n j else 0 := by
                    intro p
                    have ht : ∀ j, (if p.val.1 = j ∨ p.val.2 = j then n j else 0) =
                        (if p.val.1 = j then n j else 0) + (if p.val.2 = j then n j else 0) := by
                      intro j
                      by_cases h1 : p.val.1 = j
                      · have h2 : p.val.2 ≠ j := fun h => p.prop.1.ne (h1.trans h.symm)
                        simp [h1, h2]
                      · by_cases h2 : p.val.2 = j <;> simp [h1, h2]
                    simp_rw [ht]
                    rw [Finset.sum_add_distrib]
                    simp [eq_comm]
                  calc
                    _ = ∑ p : HistoryOrderedDependentPair dependent, ∑ j : J, if p.val.1 = j ∨ p.val.2 = j then n j else 0 :=
                      Finset.sum_congr rfl (fun p _ => hp p)
                    _ = ∑ j : J, ∑ p : HistoryOrderedDependentPair dependent, if p.val.1 = j ∨ p.val.2 = j then n j else 0 :=
                      Finset.sum_comm
                    _ = _ := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      rw [← Finset.sum_filter]
                      simp [historyIncidentPairs]
                rw [h_historyPairExponent_incidence, Finset.mul_sum]
                apply Finset.sum_le_sum
                intro j hj
                have h_historyIncidentPairs_card_le : (historyIncidentPairs dependent j).card ≤ (dependentLabelFinset dependent j).card - 1 := by
                  classical
                  have hj : j ∈ dependentLabelFinset dependent j := Finset.mem_filter.2 ⟨Finset.mem_univ _, hrefl _⟩
                  rw [← Finset.card_erase_of_mem hj]
                  apply Finset.card_le_card_of_injOn (historyPairOtherLabel dependent j)
                  · intro p hp
                    obtain ⟨_, hp⟩ := Finset.mem_filter.1 hp
                    rcases hp with hp | hp
                    · have he : historyPairOtherLabel dependent j p = p.val.2 := by simp [historyPairOtherLabel, hp]
                      rw [he]
                      apply Finset.mem_erase.2
                      refine ⟨?_, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
                      · rw [← hp]; exact p.prop.1.ne.symm
                      · rw [← hp]; exact p.prop.2
                    · have hne : p.val.1 ≠ j := by rw [← hp]; exact p.prop.1.ne
                      have he : historyPairOtherLabel dependent j p = p.val.1 := by simp [historyPairOtherLabel, hne]
                      rw [he]
                      exact Finset.mem_erase.2 ⟨hne, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [← hp]; exact hsymm p.prop.2⟩⟩
                  · intro p hp q hq hpq
                    apply Subtype.ext
                    rw [h_historyIncidentPair_reconstruct j p hp,
                      h_historyIncidentPair_reconstruct j q hq, hpq]
                exact Nat.mul_le_mul_right (n j) (h_historyIncidentPairs_card_le.trans
                  (Nat.sub_le_sub_right (hlabels j) 1))
              let : Finite (HistoryMultiplicityShape dependent n) := historyMultiplicityShape_finite dependent hrefl hsymm n
              have hh := Nat.card_le_card_of_injective (historyMultiplicityPairCode dependent n)
                (historyMultiplicityPairCode_injective dependent hrefl hsymm n)
              have hc : Nat.card (∀ p : HistoryOrderedDependentPair dependent, List.Vector Bool (n p.val.1 + n p.val.2)) =
                  ∏ p : HistoryOrderedDependentPair dependent, 2 ^ (n p.val.1 + n p.val.2) := by
                rw [Nat.card_eq_fintype_card]
                simp only [Fintype.card_pi, card_vector, Fintype.card_bool]
              calc
                _ ≤ ∏ p : HistoryOrderedDependentPair dependent, 2 ^ (n p.val.1 + n p.val.2) :=
                  (by rwa [hc] at hh)
                _ = 2 ^ (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) :=
                  Finset.prod_pow_eq_pow_sum _ _ _
                _ ≤ _ := pow_le_pow_right₀ (by decide : 1 ≤ 2)
                  h_historyPairExponent_le
            exact hh.trans h_historyMultiplicityShape_card_le_degree
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (historyReferenceRho_pos Δ).le _)
          exact_mod_cast h_historyFiniteMultiplicityFiber_card_le
        _ = (1 / 4 ) ^ (∑ j : J, n j) := by
          have h_historyReferenceRho_times_degree_power : historyReferenceRho Δ * 2 ^ (Δ - 1) = 1 / 4 := by
            have hc : Δ + 1 = Δ - 1 + 2 := by omega
            unfold historyReferenceRho
            rw [hc, pow_add]
            calc
              _ = ((1 / 2 : ℝ) * 2) ^ (Δ - 1) * (1 / 2 : ℝ) ^ 2 := by rw [mul_pow]; ring
              _ = _ := by norm_num
          rw [pow_mul, ← mul_pow, mul_comm ((2 : ℝ) ^ (Δ - 1)), h_historyReferenceRho_times_degree_power]
    _ ≤ ∑ n ∈ Fintype.piFinset (fun _ => Finset.range N), (1 / 4 ) ^ (∑ j : J, n j) :=
      Finset.sum_le_sum_of_subset_of_nonneg hbox (fun _ _ _ => by positivity)
    _ = ∏ _j : J, ∑ r ∈ Finset.range N, (1 / 4 ) ^ r := by
      simp_rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.sum_prod_piFinset (Finset.range N) (fun _ r => (1 / 4 ) ^ r)
    _ ≤ ∏ _j : J, (4 / 3 ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro j hj
      have hh := history_finite_geom_sum_le (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1) N
      norm_num at hh ⊢
      exact hh
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]
end
section
variable {J : Type*} [Fintype J] [LinearOrder J]
abbrev HistoryMarked (dependent : J → J → Prop) (E : Type*) :=
  Σ g : HistoryShape (fun a b => ¬ dependent a b), Fin (historyShapeLength dependent g) → E
theorem historyMarked_measurable_mk (dependent : J → J → Prop) {E : Type*}
    [MeasurableSpace E] (g : HistoryShape (fun a b => ¬ dependent a b)) :
    Measurable (fun marks : Fin (historyShapeLength dependent g) → E => (⟨g, marks⟩ : HistoryMarked dependent E)) := by
  apply Measurable.of_le_map
  exact iInf_le _ g
theorem historyMarked_measurable_iff (dependent : J → J → Prop) {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] (f : HistoryMarked dependent E → X) :
    Measurable f ↔ ∀ g, Measurable (fun marks => f ⟨g, marks⟩) := by
  constructor
  · intro hf g
    exact hf.comp (historyMarked_measurable_mk dependent g)
  · intro hf s hs
    change MeasurableSet[⨅ g, MeasurableSpace.map (Sigma.mk g)
      (inferInstance : MeasurableSpace (Fin (historyShapeLength dependent g) → E))] (f ⁻¹' s)
    rw [MeasurableSpace.measurableSet_iInf]
    exact fun g => hf g hs
theorem historySigma_borelSpace  [Countable I] {X : I → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)] :
    BorelSpace (Sigma X) := by
  constructor
  apply le_antisymm
  · intro s hs
    let : MeasurableSpace (Sigma X) := borel (Sigma X)
    let : BorelSpace (Sigma X) := ⟨rfl⟩
    have hu : s = ⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s) := by
      ext x
      constructor
      · intro hx; exact Set.mem_iUnion.2 ⟨x.1, x.2, hx, rfl⟩
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨i, y, hy, rfl⟩
        exact hy
    rw [hu]
    exact MeasurableSet.iUnion fun i =>
      (Topology.IsClosedEmbedding.sigmaMk (i := i)).measurableEmbedding.measurableSet_image' ((MeasurableSpace.measurableSet_iInf.1 hs) i)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    intro i
    exact (hs.preimage continuous_sigmaMk).measurableSet
theorem historyShapeLength_out (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyShapeLength dependent g = g.out.length := by
  have hh := congrArg (historyShapeLength dependent) (Quotient.out_eq g)
  rw [historyShapeLength_mk] at hh
  exact hh.symm
def historyShapeCanonicalLabels (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : Fin (historyShapeLength dependent g) → J :=
  fun i => g.out.get (Fin.cast (historyShapeLength_out dependent g) i)
def historyMarkedRawState (dependent : J → J → Prop) {E X : Type*}
    (update : J → E → X → X) (initial : X) (h : HistoryMarked dependent E) : X :=
  (List.ofFn (fun i : Fin (historyShapeLength dependent h.1) => i)).foldl
    (fun state i => update (historyShapeCanonicalLabels dependent h.1 i) (h.2 i) state) initial
theorem historyMarkedRawState_measurable (dependent : J → J → Prop) {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] (update : J → E → X → X)
    (hu : ∀ j, Measurable (fun ex : E × X => update j ex.1 ex.2)) (initial : X) :
    Measurable (historyMarkedRawState dependent update initial) := by
  rw [historyMarked_measurable_iff]
  intro g
  have h_historyMarked_indexFold_measurable (n : ℕ) (labels : Fin n → J) (indices : List (Fin n)) (f : (Fin n → E) → X) (hf : Measurable f) : Measurable (fun marks => indices.foldl (fun state i => update (labels i) (marks i) state) (f marks)) := by
    induction indices generalizing f with
    | nil => exact hf
    | cons i indices ih =>
      exact ih (fun marks => update (labels i) (marks i) (f marks))
        ((hu (labels i)).comp ((measurable_pi_apply i).prodMk hf))
  exact h_historyMarked_indexFold_measurable (historyShapeLength dependent g) (historyShapeCanonicalLabels dependent g) (List.ofFn (fun i : Fin (historyShapeLength dependent g) => i)) (fun _ => initial) measurable_const
def historyMarkedReferenceRaw (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
    Measure.map (Sigma.mk g) (Measure.pi fun _ => π)
theorem historyMarkedReferenceRaw_univ (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    historyMarkedReferenceRaw dependent Δ π Set.univ =
      ∑' g, ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) := by
  unfold historyMarkedReferenceRaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  congr 1
  funext g
  rw [Measure.smul_apply, Measure.map_apply (historyMarked_measurable_mk dependent g) MeasurableSet.univ]
  simp
theorem historyMarkedReferenceRaw_univ_one_le (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    1 ≤ historyMarkedReferenceRaw dependent Δ π Set.univ := by
  rw [historyMarkedReferenceRaw_univ]
  let empty : HistoryShape (fun a b => ¬ dependent a b) := Quotient.mk _ []
  have he : ENNReal.ofReal (historyShapeReferenceWeight dependent Δ empty) = 1 := by
    simp [empty, historyShapeReferenceWeight, historyShapeLength_mk]
  rw [← he]
  exact ENNReal.le_tsum (f := fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g)) empty
theorem historyMarkedReferenceRaw_finite (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) := by
  constructor
  rw [historyMarkedReferenceRaw_univ]
  have h_historyShapeReferenceWeight_summable  := summable_of_sum_le (fun _ => pow_nonneg (historyReferenceRho_pos Δ).le _)
    (historyReferenceWeight_finite_sum_le dependent hrefl hsymm Δ hΔ hlabels)
  exact h_historyShapeReferenceWeight_summable.tsum_ofReal_lt_top
def historyMarkedReference (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedReferenceRaw dependent Δ π
theorem historyMarkedReference_probability (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (historyMarkedReference dependent Δ π) := by
  let : IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) :=
    historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  unfold historyMarkedReference
  constructor
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by have hh := historyMarkedReferenceRaw_univ_one_le dependent Δ π; exact ne_of_gt (lt_of_lt_of_le zero_lt_one hh)) (measure_ne_top _ _)
end
variable {J : Type*} [Fintype J] [LinearOrder J]
def historyMarkedPieceWeight (dependent : J → J → Prop) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) (x : WordHeapPiece h.1.out dependent) : ℝ :=
  a (h.2 (Fin.cast (historyShapeLength_out dependent h.1).symm x.position))
def historyMarkedDensity (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) : ℝ :=
  historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ Finset.univ t
theorem historyMarkedDensity_measurable (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a) :
    Measurable (historyMarkedDensity dependent ρ t a) :=
  have h_historyMarkedDensity_fiber_measurable (g : HistoryShape (fun i j => ¬ dependent i j)) : Measurable (fun marks => historyMarkedDensity dependent ρ t a ⟨g, marks⟩) := by
    unfold historyMarkedDensity
    simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
    change Measurable (fun marks : Fin (historyShapeLength dependent g) → E =>
      ∑ P ∈ historyUpperSets (Finset.univ : Finset (WordHeapPiece g.out dependent)),
        (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P,
          a (marks (Fin.cast (historyShapeLength_out dependent g).symm x.position)))
    apply Finset.measurable_fun_sum _
    intro P hP
    apply Measurable.const_mul
    apply Finset.measurable_fun_prod _
    intro x hx
    exact ha.comp (measurable_pi_apply _)
  (historyMarked_measurable_iff dependent _).2
    h_historyMarkedDensity_fiber_measurable
theorem historyMarkedDensity_bounds (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ t B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    {E : Type*} (a : E → ℝ) (ha : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) (h : HistoryMarked dependent E) :
    (1 / 2 : ℝ) ^ Fintype.card J ≤ historyMarkedDensity dependent ρ t a h ∧
      historyMarkedDensity dependent ρ t a h ≤ (3 / 2 : ℝ) ^ Fintype.card J :=
  have h_wordHeap_density_bounds (word : List J) (weight : WordHeapPiece word dependent → ℝ) (ρ : ℝ) (t : ℝ) (B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B) (hw : ∀ x, |weight x| ≤ B) (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) : (1 / 2 : ℝ) ^ Fintype.card J ≤ historyScaledUpperDensity weight ρ Finset.univ t ∧
      historyScaledUpperDensity weight ρ Finset.univ t ≤ (3 / 2 : ℝ) ^ Fintype.card J := by
    have hb := historyUpperDensity_bounds_of_degree_bound weight ρ t B hρ ht hB hw (2 * Δ) (by intro x; change (wordHeapCoverGraph word dependent).degree x ≤ 2 * Δ; exact (wordHeapCoverGraph_degree_le hrefl hsymm x).trans (Nat.mul_le_mul_left 2 (hlabels _))) (by convert hsmall using 1; push_cast; ring)
    have hc := wordHeap_maximal_card_le_labels hrefl hsymm (Finset.univ : Finset (WordHeapPiece word dependent))
    refine ⟨?_, ?_⟩
    · exact (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hc).trans hb.1
    · exact hb.2.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2) hc)
  (h_wordHeap_density_bounds h.1.out)
    (historyMarkedPieceWeight dependent a h) ρ t B hρ ht hB (fun _ => ha _) hsmall
theorem historyIntegral_pi_finset_prod  [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (S : Finset I) :
    (∫ marks : I → E, ∏ i ∈ S, a (marks i) ∂Measure.pi (fun _ => π)) =
      ∏ _i ∈ S, ∫ e, a e ∂π := by
  have hp : ∀ marks : I → E, (∏ i : I, if i ∈ S then a (marks i) else 1) =
      ∏ i ∈ S, a (marks i) := fun marks => Finset.prod_ite_mem_eq S _
  simp_rw [← hp]
  rw [integral_fintype_prod_eq_prod (fun (i : I) (e : E) => if i ∈ S then a e else 1)]
  calc
    _ = ∏ i : I, if i ∈ S then ∫ e, a e ∂π else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hS : i ∈ S <;> simp [hS]
    _ = _ := Finset.prod_ite_mem_eq S _
theorem historyIntegral_pi_indexed_prod  [Fintype I] [DecidableEq I]
    [DecidableEq A] [MeasurableSpace E] (π ) [IsProbabilityMeasure π]
    (a : E → ℝ) (index : A → I) (hi : Function.Injective index) (P : Finset A) :
    (∫ marks : I → E, ∏ x ∈ P, a (marks (index x)) ∂Measure.pi (fun _ => π)) =
      ∏ _x ∈ P, ∫ e, a e ∂π := by
  have hp : ∀ marks : I → E, (∏ i ∈ P.image index, a (marks i)) =
      ∏ x ∈ P, a (marks (index x)) := fun marks => Finset.prod_image hi.injOn
  calc
    _ = ∫ marks : I → E, ∏ i ∈ P.image index, a (marks i) ∂Measure.pi (fun _ => π) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun marks => (hp marks).symm)
    _ = ∏ _i ∈ P.image index, ∫ e, a e ∂π := historyIntegral_pi_finset_prod π a _
    _ = _ := Finset.prod_image hi.injOn
def historyMarkedPieceIndex (dependent : J → J → Prop)
    (g : HistoryShape (fun i j => ¬ dependent i j)) : WordHeapPiece g.out dependent → Fin (historyShapeLength dependent g) :=
  fun x => Fin.cast (historyShapeLength_out dependent g).symm x.position
def historyMarkedFiberPrior (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    Measure (Fin (historyShapeLength dependent g) → E) :=
  (Measure.pi (fun _ => π)).withDensity
    (fun marks => ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a ⟨g, marks⟩))
def historyMarkedPriorRaw (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ) : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
    Measure.map (Sigma.mk g) (historyMarkedFiberPrior dependent Δ t π a g)
def historyMarkedPrior (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ) : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedPriorRaw dependent Δ t π a
theorem historyMarkedPrior_probability (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Integrable a π)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) :
    IsProbabilityMeasure (historyMarkedPrior dependent Δ t π a) := by
  let : IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) :=
    historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  constructor
  unfold historyMarkedPrior
  have h_historyMarkedPriorRaw_univ : historyMarkedPriorRaw dependent Δ t π a Set.univ = historyMarkedReferenceRaw dependent Δ π Set.univ := by
    rw [historyMarkedReferenceRaw_univ]
    unfold historyMarkedPriorRaw
    rw [Measure.sum_apply _ MeasurableSet.univ]
    congr 1
    funext g
    have h_historyMarkedFiberPrior_probability : IsProbabilityMeasure (historyMarkedFiberPrior dependent Δ t π a g) := by
      have h_historyMarkedDensity_fiber_integral_one (ρ : ℝ) : (∫ marks, historyMarkedDensity dependent ρ t a ⟨g, marks⟩
          ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) = 1 := by
        let index := historyMarkedPieceIndex dependent g
        have hi : Function.Injective index := (by intro x y hxy; apply WordHeapPiece.ext; exact Fin.cast_injective _ hxy)
        have hterm : ∀ P : Finset (WordHeapPiece g.out dependent),
            Integrable (fun marks => (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, a (marks (index x)))
              (Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) := by
          intro P
          have h_historyIntegrable_pi_indexed_prod : Integrable (fun marks => ∏ x ∈ P, a (marks (index x))) (Measure.pi (fun _ => π)) := by
            have h_historyIntegrable_pi_finset_prod : Integrable (fun marks => ∏ i ∈ (P.image index), a (marks i)) (Measure.pi (fun _ => π)) := by
              have hp := Integrable.fintype_prod (μ := fun _ => π)
                (f := fun i e => if i ∈ (P.image index) then a e else 1)
                (fun i => by by_cases hi : i ∈ (P.image index) <;> simp [hi, ha])
              simpa only [Finset.prod_ite_mem_eq] using hp
            have hp := h_historyIntegrable_pi_finset_prod
            simpa only [Finset.prod_image hi.injOn] using hp
          exact h_historyIntegrable_pi_indexed_prod.const_mul _
        unfold historyMarkedDensity
        simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
        change (∫ marks, ∑ P ∈ historyUpperSets (Finset.univ : Finset (WordHeapPiece g.out dependent)),
          (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, a (marks (index x))
          ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) = 1
        rw [integral_finsetSum _ (fun P _ => hterm P)]
        simp_rw [integral_const_mul, historyIntegral_pi_indexed_prod π a index hi, hcenter]
        rw [Finset.sum_eq_single ∅]
        · simp
        · intro P hP hne
          rw [Finset.prod_const]
          simp [zero_pow (Finset.card_ne_zero.2 (Finset.nonempty_iff_ne_empty.2 hne))]
        · intro hnot
          exact (hnot (mem_historyUpperSets.2 ⟨Finset.empty_subset _, by simp⟩)).elim
      have he := h_historyMarkedDensity_fiber_integral_one (historyReferenceRho Δ)
      have hi := integrable_of_integral_eq_one he
      have hnonneg : ∀ marks, 0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a ⟨g, marks⟩ := by
        intro marks
        have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels _ t B
          (historyReferenceRho_pos Δ) ht hB a habound hsmall ⟨g, marks⟩
        exact (by positivity : ↑0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
      constructor
      unfold historyMarkedFiberPrior
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnonneg), he]
      simp
    let : IsProbabilityMeasure (historyMarkedFiberPrior dependent Δ t π a g) :=
      h_historyMarkedFiberPrior_probability
    rw [Measure.smul_apply, Measure.map_apply (historyMarked_measurable_mk dependent g) MeasurableSet.univ]
    simp
  rw [Measure.smul_apply, h_historyMarkedPriorRaw_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (lt_of_lt_of_le zero_lt_one (historyMarkedReferenceRaw_univ_one_le dependent Δ π))) (measure_ne_top _ _)
end NearlyMinimax
