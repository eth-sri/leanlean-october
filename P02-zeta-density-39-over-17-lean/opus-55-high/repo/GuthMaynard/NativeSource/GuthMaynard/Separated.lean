module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Basic
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Set Metric

namespace GuthMaynard.NativeMoment

/-- A finite set `W` of real numbers is `δ`-separated if the distance between any two distinct points is at least `δ`. -/
def IsSeparated (δ : ℝ) (W : Finset ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → δ ≤ dist x y

/-- The interval for the basic Large Values Estimate (Theorem 1.1) is `[0, T]`. -/
def InBaseInterval (T : ℝ) (W : Finset ℝ) : Prop :=
  ∀ (x : ℝ), x ∈ W → x ∈ Icc 0 T

/-- 
Translation of a finite set by a constant `c`. 
This is used in Phase 4 to map `[T, 2T]` to `[0, T]`.
-/
noncomputable def translateSet (c : ℝ) (W : Finset ℝ) : Finset ℝ :=
  W.image (fun x => x - c)

theorem isSeparated_translate (δ c : ℝ) (W : Finset ℝ) (h : IsSeparated δ W) : 
    IsSeparated δ (translateSet c W) := by
  pm_874 translateSet
  have hx'y' : x' ≠ y' := by
    intro hc
    rw [hc] at hxy
    grind
  have hd : dist (x' - c) (y' - c) = dist x' y' := by
    dsimp [dist]
    congr 1
    ring
  rw [hd]
  aesop

theorem translateSet_card (c : ℝ) (W : Finset ℝ) : (translateSet c W).card = W.card := by
  unfold translateSet
  apply Finset.card_image_of_injective
  intro x y hxy
  change x - c = y - c at hxy
  have h1 : x - c + c = y - c + c := by grind
  ring_nf at h1
  exact h1

/-- 
Combinatorial separation extraction hypothesis. 
States that from any finite set S where local occupancy in [x, x+1) is bounded by L,
we can extract a 1-separated subset W whose size is proportional to S.
Isolated as a hypothesis pending a full Lean combinatorial proof.
-/
def SeparatedSelectionProp : Prop :=
  ∀ (S : Finset ℝ) (L : ℕ),
    (∀ (x : ℤ), (S.filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card ≤ L) →
    ∃ W ⊆ S, GuthMaynard.NativeMoment.IsSeparated 1 W ∧ S.card ≤ 2 * L * W.card

open scoped Classical

theorem separated_selection : SeparatedSelectionProp := by
  intro S L hL
  pm_1059
  have H : S_even ∪ S_odd = S := by
    pm_7018
    have : Even ⌊a⌋ ∨ Odd ⌊a⌋ := Int.even_or_odd ⌊a⌋
    tauto
  have H_card : S_even.card + S_odd.card = S.card := by
    rw [← Finset.card_union_of_disjoint]
    grind
    · rw [Finset.disjoint_filter]
      intro x hx h_even h_odd
      pm_4828 h_even h_odd

  have H_L : ∀ z : ℤ, (S.filter (fun t => ⌊t⌋ = z)).card ≤ L := by
    intro z
    have := hL z
    have H_eq : (S.filter (fun t => ⌊t⌋ = z)) = S.filter (fun t => (z : ℝ) ≤ t ∧ t < (z : ℝ) + 1) := by
      pm_8132
    rw [H_eq]
    exact this
  have H_card_le : S.card ≤ 2 * S_even.card ∨ S.card ≤ 2 * S_odd.card := by
    omega

  pm_970 g_even S_even.filter

  let W_even := (S_even.image (fun t => ⌊t⌋)).image g_even

  have W_even_sub_S : W_even ⊆ S := by
    pm_4829 S_even.image g_even
    pm_4822
    pm_4817
    dsimp [g_even]
    pm_4827 S_even S_even.filter
    · case isFalse h =>
      have H_nonempty : (S_even.filter (fun t' => ⌊t'⌋ = ⌊t⌋)).Nonempty := by
        pm_4823
      contradiction

  have g_even_floor : ∀ z ∈ S_even.image (fun t => ⌊t⌋), ⌊g_even z⌋ = z := by
    intro z hz
    dsimp [g_even]
    have H_nonempty : (S_even.filter (fun t => ⌊t⌋ = z)).Nonempty := by
      pm_4817
      pm_4823
    pm_955

  have H_floor : ∀ x ∈ W_even, ⌊x⌋ ∈ S_even.image (fun t => ⌊t⌋) ∧ x = g_even ⌊x⌋ := by
    pm_4829 S_even.image g_even
    pm_4822
    pm_6845 g_even g_even_floor

  have W_even_sep : GuthMaynard.NativeMoment.IsSeparated 1 W_even := by
    intro x hx y hy hxy
    pm_268 hx_fl H_floor x hx hy_fl y hy
    have hx_even : Even ⌊x⌋ := by
      pm_8032 S_even
      pm_4821
    have hy_even : Even ⌊y⌋ := by
      pm_8033 S_even
      pm_4821
    pm_4826
    cases le_total ⌊x⌋ ⌊y⌋ with
    | inl hle =>
      have H_le : ⌊y⌋ - ⌊x⌋ ≥ 2 := by
        pm_4828 hx_even hy_even
      pm_4818
    | inr hle =>
      have H_le : ⌊x⌋ - ⌊y⌋ ≥ 2 := by
        pm_4828 hx_even hy_even
      pm_4819

  have W_even_card : W_even.card = (S_even.image (fun t => ⌊t⌋)).card := by
    apply Finset.card_image_of_injOn
    intro z1 hz1 z2 hz2 hz
    pm_268 hz1_eq g_even_floor z1 hz1 hz2_eq z2 hz2
    pm_7565

  have S_even_card_le : S_even.card ≤ L * W_even.card := by
    have eq1 : S_even = (S_even.image (fun t => ⌊t⌋)).biUnion (fun z => S_even.filter (fun t => ⌊t⌋ = z)) := by
      pm_4820
    have eq2 : S_even.card = ∑ z ∈ S_even.image (fun t => ⌊t⌋), (S_even.filter (fun t => ⌊t⌋ = z)).card := by
      pm_4824
    rw [W_even_card]
    pm_4825 S_even.image S_even.filter

  pm_970 g_odd S_odd.filter

  let W_odd := (S_odd.image (fun t => ⌊t⌋)).image g_odd

  have W_odd_sub_S : W_odd ⊆ S := by
    pm_4829 S_odd.image g_odd
    pm_4822
    pm_4817
    dsimp [g_odd]
    pm_4827 S_odd S_odd.filter
    · case isFalse h =>
      have H_nonempty : (S_odd.filter (fun t' => ⌊t'⌋ = ⌊t⌋)).Nonempty := by
        pm_4823
      contradiction

  have g_odd_floor : ∀ z ∈ S_odd.image (fun t => ⌊t⌋), ⌊g_odd z⌋ = z := by
    intro z hz
    dsimp [g_odd]
    have H_nonempty : (S_odd.filter (fun t => ⌊t⌋ = z)).Nonempty := by
      pm_4817
      pm_4823
    pm_955

  have H_floor_odd : ∀ x ∈ W_odd, ⌊x⌋ ∈ S_odd.image (fun t => ⌊t⌋) ∧ x = g_odd ⌊x⌋ := by
    pm_4829 S_odd.image g_odd
    pm_4822
    pm_6845 g_odd g_odd_floor

  have W_odd_sep : GuthMaynard.NativeMoment.IsSeparated 1 W_odd := by
    intro x hx y hy hxy
    pm_268 hx_fl H_floor_odd x hx hy_fl y hy
    have hx_odd : Odd ⌊x⌋ := by
      pm_8032 S_odd
      pm_4821
    have hy_odd : Odd ⌊y⌋ := by
      pm_8033 S_odd
      pm_4821
    pm_4826
    cases le_total ⌊x⌋ ⌊y⌋ with
    | inl hle =>
      have H_le : ⌊y⌋ - ⌊x⌋ ≥ 2 := by
        pm_4828 hx_odd hy_odd
      pm_4818
    | inr hle =>
      have H_le : ⌊x⌋ - ⌊y⌋ ≥ 2 := by
        pm_4828 hx_odd hy_odd
      pm_4819

  have W_odd_card : W_odd.card = (S_odd.image (fun t => ⌊t⌋)).card := by
    apply Finset.card_image_of_injOn
    intro z1 hz1 z2 hz2 hz
    pm_268 hz1_eq g_odd_floor z1 hz1 hz2_eq z2 hz2
    pm_7565

  have S_odd_card_le : S_odd.card ≤ L * W_odd.card := by
    have eq1 : S_odd = (S_odd.image (fun t => ⌊t⌋)).biUnion (fun z => S_odd.filter (fun t => ⌊t⌋ = z)) := by
      pm_4820
    have eq2 : S_odd.card = ∑ z ∈ S_odd.image (fun t => ⌊t⌋), (S_odd.filter (fun t => ⌊t⌋ = z)).card := by
      pm_4824
    rw [W_odd_card]
    pm_4825 S_odd.image S_odd.filter

  grind

/-- Weighted local-occupancy form of finite one-dimensional separated selection. -/
def WeightedSeparatedSelectionProp : Prop :=
  ∀ (S : Finset ℝ) (weight : ℝ → ℕ) (L : ℕ),
    (∀ (z : ℤ),
      ∑ t ∈ S.filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1), weight t ≤ L) →
    ∃ W ⊆ S, GuthMaynard.NativeMoment.IsSeparated 1 W ∧
      ∑ t ∈ S, weight t ≤ 2 * L * W.card

/--
Choose one representative from every occupied even or odd unit bin, selecting
the parity class carrying at least half of the total weight.
-/
theorem weighted_separated_selection : WeightedSeparatedSelectionProp := by
  intro S weight L hL
  pm_1059
  have hDisjoint : Disjoint S_even S_odd := by
    rw [Finset.disjoint_filter]
    intro x hx hEven hOdd
    pm_4828 hEven hOdd
  have hUnion : S_even ∪ S_odd = S := by
    pm_7018
    have hParity : Even ⌊a⌋ ∨ Odd ⌊a⌋ := Int.even_or_odd ⌊a⌋
    tauto
  have hWeightSplit :
      (∑ t ∈ S_even, weight t) + (∑ t ∈ S_odd, weight t) = ∑ t ∈ S, weight t := by
    rw [← Finset.sum_union hDisjoint, hUnion]
  have hHeavy :
      (∑ t ∈ S, weight t) ≤ 2 * (∑ t ∈ S_even, weight t) ∨
        (∑ t ∈ S, weight t) ≤ 2 * (∑ t ∈ S_odd, weight t) := by
    omega

  have hBinWeight : ∀ z : ℤ, ∑ t ∈ S.filter (fun u => ⌊u⌋ = z), weight t ≤ L := by
    intro z
    have hEq : S.filter (fun u => ⌊u⌋ = z) =
        S.filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1) := by
      pm_8132
    rw [hEq]
    exact hL z

  let representative (A : Finset ℝ) (z : ℤ) : ℝ :=
    if h : (A.filter (fun t => ⌊t⌋ = z)).Nonempty then
      (A.filter (fun t => ⌊t⌋ = z)).max' h
    else
      0
  let chooseBins (A : Finset ℝ) : Finset ℝ :=
    (A.image (fun t => ⌊t⌋)).image (representative A)

  have representative_mem (A : Finset ℝ) (z : ℤ)
      (hz : z ∈ A.image (fun t => ⌊t⌋)) : representative A z ∈ A := by
    dsimp [representative]
    have hNonempty : (A.filter (fun t => ⌊t⌋ = z)).Nonempty := by
      pm_4817
      exact ⟨t, Finset.mem_filter.mpr ⟨ht, rfl⟩⟩
    split
    · exact (Finset.mem_filter.mp (Finset.max'_mem _ hNonempty)).1
    · contradiction

  have representative_floor (A : Finset ℝ) (z : ℤ)
      (hz : z ∈ A.image (fun t => ⌊t⌋)) : ⌊representative A z⌋ = z := by
    dsimp [representative]
    have hNonempty : (A.filter (fun t => ⌊t⌋ = z)).Nonempty := by
      pm_4817
      exact ⟨t, Finset.mem_filter.mpr ⟨ht, rfl⟩⟩
    split
    · exact (Finset.mem_filter.mp (Finset.max'_mem _ hNonempty)).2
    · contradiction

  have chooseBins_subset (A : Finset ℝ) : chooseBins A ⊆ A := by
    pm_1187
    exact representative_mem A z hz

  have chooseBins_floor (A : Finset ℝ) :
      ∀ x ∈ chooseBins A,
        ⌊x⌋ ∈ A.image (fun t => ⌊t⌋) ∧ x = representative A ⌊x⌋ := by
    pm_1187
    have hzFloor := representative_floor A z hz
    rw [hzFloor]
    exact ⟨hz, rfl⟩

  have chooseBins_card (A : Finset ℝ) :
      (chooseBins A).card = (A.image (fun t => ⌊t⌋)).card := by
    dsimp [chooseBins]
    apply Finset.card_image_of_injOn
    intro z₁ hz₁ z₂ hz₂ hRep
    have h₁ := representative_floor A z₁ hz₁
    have h₂ := representative_floor A z₂ hz₂
    rw [hRep] at h₁
    exact h₁.symm.trans h₂

  have separated_of_parity (A : Finset ℝ)
      (hParity : (∀ x ∈ A, Even ⌊x⌋) ∨ (∀ x ∈ A, Odd ⌊x⌋)) :
      GuthMaynard.NativeMoment.IsSeparated 1 (chooseBins A) := by
    intro x hx y hy hxy
    have hxData := chooseBins_floor A x hx
    have hyData := chooseBins_floor A y hy
    have hFloorNe : ⌊x⌋ ≠ ⌊y⌋ := by
      intro hEq
      apply hxy
      rw [hxData.2, hyData.2, hEq]
    have hxMem : x ∈ A := chooseBins_subset A hx
    have hyMem : y ∈ A := chooseBins_subset A hy
    pm_5922 hxBounds x
    pm_5922 hyBounds y
    dsimp [dist]
    by_cases hxyFloor : ⌊x⌋ ≤ ⌊y⌋
    · have hInt : 2 ≤ ⌊y⌋ - ⌊x⌋ := by
        pm_4830
      pm_5247 y x hYX
      rw [abs_sub_comm]
      exact hYX.trans (le_abs_self (y - x))
    · have hInt : 2 ≤ ⌊x⌋ - ⌊y⌋ := by
        pm_4830
      pm_5247 x y hXY
      exact hXY.trans (le_abs_self (x - y))

  have weighted_by_bins (A : Finset ℝ) (hAS : A ⊆ S) :
      ∑ t ∈ A, weight t ≤ L * (chooseBins A).card := by
    have hFiber :
        (∑ z ∈ A.image (fun t => ⌊t⌋),
          ∑ t ∈ A.filter (fun u => ⌊u⌋ = z), weight t) = ∑ t ∈ A, weight t := by
      have hAll : A.filter (fun t => ⌊t⌋ ∈ A.image (fun u => ⌊u⌋)) = A := by
        apply Finset.filter_eq_self.mpr
        pm_4831 t ht
      have hFiberwise := Finset.sum_fiberwise_eq_sum_filter
        A (A.image (fun t => ⌊t⌋)) (fun t => ⌊t⌋) weight
      rw [hAll] at hFiberwise
      exact hFiberwise
    rw [← hFiber, chooseBins_card]
    calc
      (∑ z ∈ A.image (fun t => ⌊t⌋),
          ∑ t ∈ A.filter (fun u => ⌊u⌋ = z), weight t)
          ≤ ∑ _z ∈ A.image (fun t => ⌊t⌋), L := by
            apply Finset.sum_le_sum
            intro z hz
            exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
              (fun t ht => by
                simp only [Finset.mem_filter] at ht ⊢
                exact ⟨hAS ht.1, ht.2⟩)
              (fun _ _ _ => Nat.zero_le _)) (hBinWeight z)
      _ = L * (A.image (fun t => ⌊t⌋)).card := by
        simp [mul_comm]

  pm_5147 even_subset S_even S odd_subset S_odd
  pm_7899 evenParity S_even Even
  pm_7899 oddParity S_odd Odd

  rcases hHeavy with hEven | hOdd
  · refine ⟨chooseBins S_even, chooseBins_subset S_even |>.trans even_subset,
      separated_of_parity S_even (Or.inl evenParity), ?_⟩
    pm_1197 S_even hEven even_subset
  · refine ⟨chooseBins S_odd, chooseBins_subset S_odd |>.trans odd_subset,
      separated_of_parity S_odd (Or.inr oddParity), ?_⟩
    pm_1197 S_odd hOdd odd_subset

end GuthMaynard.NativeMoment
