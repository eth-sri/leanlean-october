/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.WhiteNoise.HaarBasis.Basic

/-!
# GaussianFields Haar dyadic algebra

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace Topology symmDiff
open Filter

namespace GaussianFields

/-- The tensor-product normalization factor of an all-father Haar packet. -/
@[expose]
noncomputable def haarBoxScaleFactor (d : Nat) (j : ℤ) : ℝ :=
  ∏ _r : Fin d, haarScaleFactor j




/-- The countable family of dyadic boxes at nonnegative scales. -/
@[expose]
def nonnegativeDyadicBoxFamily (d : Nat) : Set (Set (Vec d)) :=
  Set.range fun p : ℕ × (Fin d → ℤ) => dyadicBox (p.1 : ℤ) p.2



/-- The integer floor cell contains the point at any nonnegative dyadic scale. -/
theorem mem_dyadicInterval_floor (n : ℕ) x :
    x ∈ dyadicInterval (n : ℤ) ⌊dyadicPower (n : ℤ) * x⌋ := by
  rw [mem_dyadicInterval_iff]
  constructor
  · have hfloor : ((⌊dyadicPower (n : ℤ) * x⌋ : ℤ) : ℝ) ≤
        dyadicPower (n : ℤ) * x :=
      Int.floor_le _
    linarith
  · have hfloor : dyadicPower (n : ℤ) * x <
        ((⌊dyadicPower (n : ℤ) * x⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    linarith


/-- A dyadic interval is the union of its two children at the next scale. -/
theorem dyadicInterval_eq_union_children j k :
    dyadicInterval j k =
      dyadicInterval (j + 1) (2 * k) ∪ dyadicInterval (j + 1) (2 * k + 1) := by
  ext x
  let y := dyadicPower j * x - (k : ℝ)
  have hleft :
      dyadicPower (j + 1) * x - ((2 * k : ℤ) : ℝ) = 2 * y := by
    simp [y, dyadicPower_add_one]
    ring
  have hright :
      dyadicPower (j + 1) * x - ((2 * k + 1 : ℤ) : ℝ) = 2 * y - 1 := by
    simp [y, dyadicPower_add_one]
    ring
  constructor
  · intro hx
    have hy := (mem_dyadicInterval_iff j k x).1 hx
    by_cases hyhalf : y < 1 / 2
    · left
      rw [mem_dyadicInterval_iff, hleft]
      constructor <;> nlinarith [hy.1, hyhalf]
    · right
      rw [mem_dyadicInterval_iff, hright]
      constructor <;> nlinarith [hy.2, le_of_not_gt hyhalf]
  · intro hx
    rw [mem_dyadicInterval_iff]
    rcases hx with hx | hx
    · have hchild : 2 * y ∈ Set.Ico (0 : ℝ) 1 := by
        have hraw := (mem_dyadicInterval_iff (j + 1) (2 * k) x).1 hx
        rw [hleft] at hraw
        exact hraw
      constructor <;> nlinarith [hchild.1, hchild.2]
    · have hchild : 2 * y - 1 ∈ Set.Ico (0 : ℝ) 1 := by
        have hraw := (mem_dyadicInterval_iff (j + 1) (2 * k + 1) x).1 hx
        rw [hright] at hraw
        exact hraw
      constructor <;> nlinarith [hchild.1, hchild.2]

/-- Distinct dyadic boxes at the same scale are disjoint. -/
theorem disjoint_dyadicBox_same_scale {d : Nat} {j : ℤ}
    {cell₁ cell₂ : Fin d → ℤ} (hcell : cell₁ ≠ cell₂) :
    Disjoint (dyadicBox j cell₁) (dyadicBox j cell₂) := by
  classical
  have disjoint_dyadicInterval_same_scale {j} {k₁} {k₂} (hk : k₁ ≠ k₂) : Disjoint (dyadicInterval j k₁) (dyadicInterval j k₂) := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    exact not_both_mem_Ico_sub_int (z := dyadicPower j * x) hk
      ⟨(mem_dyadicInterval_iff j k₁ x).1 hx₁,
        (mem_dyadicInterval_iff j k₂ x).1 hx₂⟩
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hcoord : ∃ r : Fin d, cell₁ r ≠ cell₂ r := by
    by_contra h
    apply hcell
    funext r
    by_contra hr
    exact h ⟨r, hr⟩
  rcases hcoord with ⟨r, hr⟩
  have hdisj := disjoint_dyadicInterval_same_scale (j := j) hr
  rw [Set.disjoint_left] at hdisj
  exact hdisj (hx₁ r trivial) (hx₂ r trivial)


/-- The finite set of children of a dyadic cell. -/
@[expose]
def dyadicChildCellFinset {d : Nat} (cell : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  (Finset.univ : Finset (Fin d → Bool)).image (haarChildCell cell)


/-- A finite union of dyadic boxes at one common scale. -/
@[expose]
def dyadicBoxFinsetUnion {d : Nat} (j : ℤ) (s : Finset (Fin d → ℤ)) : Set (Vec d) :=
  ⋃ cell ∈ s, dyadicBox j cell

/-- A dyadic box is a finite union of its children at the next scale. -/
theorem dyadicBox_eq_dyadicBoxFinsetUnion_children {d : Nat}
    j cell :
    dyadicBox j cell =
      dyadicBoxFinsetUnion (d := d) (j + 1) (dyadicChildCellFinset cell) := by
  have mem_dyadicChildCellFinset {d} {cell} {child} : child ∈ dyadicChildCellFinset cell ↔ ∃ side : Fin d → Bool, haarChildCell cell side = child := by
    classical
    simp [dyadicChildCellFinset]
  have dyadicBox_eq_iUnion_children {d} j cell : dyadicBox j cell = ⋃ side : Fin d → Bool, dyadicBox (j + 1) (haarChildCell cell side) := by
    classical
    ext x
    constructor
    · intro hx
      let side : Fin d → Bool := fun r =>
        if x r ∈ dyadicInterval (j + 1) (2 * cell r) then false else true
      refine Set.mem_iUnion.2 ⟨side, ?_⟩
      intro r _hr
      have := hx r trivial
      by_cases hleft : x r ∈ dyadicInterval (j + 1) (2 * cell r)
      · simp [side, haarChildCell, hleft]
      · have hright : x r ∈ dyadicInterval (j + 1) (2 * cell r + 1) :=
          (show x r ∈ dyadicInterval (j + 1) (2 * cell r) ∪ dyadicInterval (j + 1) (2 * cell r + 1) by rwa [← dyadicInterval_eq_union_children j (cell r)]).resolve_left hleft
        simpa [side, haarChildCell, hleft] using hright
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨side, hxside⟩
      intro r _hr
      have hchild := hxside r trivial
      change x r ∈ dyadicInterval j (cell r)
      rw [dyadicInterval_eq_union_children j (cell r)]
      by_cases hside : side r
      · right
        simpa [haarChildCell, hside] using hchild
      · left
        simpa [haarChildCell, hside] using hchild
  rw [dyadicBox_eq_iUnion_children]
  ext x
  simp [dyadicBoxFinsetUnion, mem_dyadicChildCellFinset]




/-- The set algebra generated by nonnegative dyadic boxes. -/
@[expose]
def nonnegativeDyadicBoxAlgebra (d : Nat) : Set (Set (Vec d)) :=
  generateSetAlgebra (nonnegativeDyadicBoxFamily d)

theorem isSetAlgebra_nonnegativeDyadicBoxAlgebra d :
    IsSetAlgebra (nonnegativeDyadicBoxAlgebra d) := by
  exact isSetAlgebra_generateSetAlgebra

theorem nonnegativeDyadicBoxFamily_subset_algebra d :
    nonnegativeDyadicBoxFamily d ⊆ nonnegativeDyadicBoxAlgebra d := by
  exact self_subset_generateSetAlgebra

theorem measurableSpace_eq_generateFrom_nonnegativeDyadicBoxAlgebra d :
    (inferInstance : MeasurableSpace (Vec d)) =
      MeasurableSpace.generateFrom (nonnegativeDyadicBoxAlgebra d) := by
  have generateFrom_nonnegativeDyadicBoxFamily_eq : MeasurableSpace.generateFrom (nonnegativeDyadicBoxFamily d) = (inferInstance : MeasurableSpace (Vec d)) := by
    have measurableSet_preimage_eval_Iio_generateFrom_nonnegativeDyadicBoxFamily {d} r a : MeasurableSet[MeasurableSpace.generateFrom (nonnegativeDyadicBoxFamily d)] {x : Vec d | x r < a} := by
      have preimage_eval_Iio_eq_iUnion_dyadicBox : {x : Vec d | x r < a} = ⋃ p : ℕ × (Fin d → ℤ), ⋃ _h : (((p.2 r : ℝ) + 1) / dyadicPower (p.1 : ℤ) < a), dyadicBox (p.1 : ℤ) p.2 := by
        have exists_nat_inv_dyadicPower_lt {ε} (hε : 0 < ε) : ∃ n : ℕ, (dyadicPower (n : ℤ))⁻¹ < ε := by
          have hlim :
              Tendsto (fun n => ((1 / 2 : ℝ) ^ n)) atTop (𝓝 (0 : ℝ)) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
          rcases eventually_atTop.1 (hlim.eventually (Iio_mem_nhds hε)) with ⟨N, hN⟩
          refine ⟨N, ?_⟩
          simpa [dyadicPower, zpow_natCast, one_div, inv_pow] using (hN N le_rfl)
        ext x
        constructor
        · intro hx
          obtain ⟨n, hn⟩ := exists_nat_inv_dyadicPower_lt (sub_pos.2 hx)
          let cell : Fin d → ℤ := fun r => ⌊dyadicPower (n : ℤ) * x r⌋
          refine Set.mem_iUnion.2 ⟨(n, cell), ?_⟩
          refine Set.mem_iUnion.2 ⟨?_, ?_⟩
          · let p : ℝ := dyadicPower (n : ℤ)
            have hp : 0 < p := dyadicPower_pos (n : ℤ)
            have : ((⌊p * x r⌋ : ℤ) : ℝ) ≤ p * x r :=
              Int.floor_le _
            have hupper_le : (((⌊p * x r⌋ : ℤ) : ℝ) + 1) / p ≤ x r + p⁻¹ := by
              calc
                (((⌊p * x r⌋ : ℤ) : ℝ) + 1) / p ≤ (p * x r + 1) / p := by
                  exact div_le_div_of_nonneg_right (by linarith) hp.le
                _ = x r + p⁻¹ := by
                  field_simp [ne_of_gt hp]
            simpa [cell, p] using lt_of_le_of_lt hupper_le (by linarith)
          · intro s _hs
            exact mem_dyadicInterval_floor n (x s)
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨p, hp⟩
          rcases Set.mem_iUnion.1 hp with ⟨hupper, hbox⟩
          have hr := hbox r trivial
          unfold dyadicInterval at hr
          exact hr.2.trans hupper
      rw [preimage_eval_Iio_eq_iUnion_dyadicBox]
      refine MeasurableSet.iUnion fun p =>
        MeasurableSet.iUnion fun _h =>
          MeasurableSpace.measurableSet_generateFrom ?_
      exact ⟨p, rfl⟩
    have measurableSet_of_mem_nonnegativeDyadicBoxFamily {d} {s} (hs : s ∈ nonnegativeDyadicBoxFamily d) : MeasurableSet s := by
      rcases hs with ⟨p, rfl⟩
      exact measurableSet_dyadicBox (p.1 : ℤ) p.2
    apply le_antisymm
    · exact MeasurableSpace.generateFrom_le fun s hs =>
        measurableSet_of_mem_nonnegativeDyadicBoxFamily hs
    · rw [MeasurableSpace.pi]
      refine iSup_le fun r => ?_
      have hmeas :
          @Measurable (Vec d) ℝ
            (MeasurableSpace.generateFrom (nonnegativeDyadicBoxFamily d)) (borel ℝ)
            (fun x => x r) := by
        rw [borel_eq_generateFrom_Iio]
        refine @measurable_generateFrom (Vec d) ℝ
          (MeasurableSpace.generateFrom (nonnegativeDyadicBoxFamily d))
          (Set.range (Set.Iio : ℝ → Set ℝ)) (fun x => x r) ?_
        intro t ht
        rcases ht with ⟨a, rfl⟩
        change MeasurableSet[MeasurableSpace.generateFrom (nonnegativeDyadicBoxFamily d)]
          {x : Vec d | x r < a}
        exact measurableSet_preimage_eval_Iio_generateFrom_nonnegativeDyadicBoxFamily r a
      exact hmeas.comap_le
  rw [nonnegativeDyadicBoxAlgebra, generateFrom_generateSetAlgebra_eq]
  exact (generateFrom_nonnegativeDyadicBoxFamily_eq).symm

theorem dyadicBoxFinsetUnion_empty {d : Nat} j :
    dyadicBoxFinsetUnion (d := d) j ∅ = ∅ := by
  simp [dyadicBoxFinsetUnion]


theorem mem_dyadicBoxFinsetUnion {d : Nat} {j : ℤ} {s : Finset (Fin d → ℤ)}
    {x : Vec d} :
    x ∈ dyadicBoxFinsetUnion j s ↔ ∃ cell ∈ s, x ∈ dyadicBox j cell := by
  simp [dyadicBoxFinsetUnion]

theorem dyadicBoxFinsetUnion_singleton {d : Nat} (j : ℤ) (cell : Fin d → ℤ) :
    dyadicBoxFinsetUnion j {cell} = dyadicBox j cell := by
  ext x
  simp [mem_dyadicBoxFinsetUnion]

theorem dyadicBoxFinsetUnion_union {d : Nat} (j : ℤ)
    (s t : Finset (Fin d → ℤ)) :
    dyadicBoxFinsetUnion j (s ∪ t) =
      dyadicBoxFinsetUnion j s ∪ dyadicBoxFinsetUnion j t := by
  ext x
  simp [mem_dyadicBoxFinsetUnion, or_and_right, exists_or]

theorem dyadicBoxFinsetUnion_inter {d : Nat} (j : ℤ)
    (s t : Finset (Fin d → ℤ)) :
    dyadicBoxFinsetUnion j (s ∩ t) =
      dyadicBoxFinsetUnion j s ∩ dyadicBoxFinsetUnion j t := by
  classical
  ext x
  constructor
  · intro hx
    rcases (mem_dyadicBoxFinsetUnion.1 hx) with ⟨cell, hcell, hxcell⟩
    exact ⟨mem_dyadicBoxFinsetUnion.2 ⟨cell, (Finset.mem_inter.1 hcell).1, hxcell⟩,
      mem_dyadicBoxFinsetUnion.2 ⟨cell, (Finset.mem_inter.1 hcell).2, hxcell⟩⟩
  · intro hx
    rcases (mem_dyadicBoxFinsetUnion.1 hx.1) with ⟨cell₁, hcell₁, hxcell₁⟩
    rcases (mem_dyadicBoxFinsetUnion.1 hx.2) with ⟨cell₂, hcell₂, hxcell₂⟩
    have : cell₁ = cell₂ := by
      by_contra hne
      have hdisj := disjoint_dyadicBox_same_scale (j := j) hne
      rw [Set.disjoint_left] at hdisj
      exact hdisj hxcell₁ hxcell₂
    subst cell₂
    exact mem_dyadicBoxFinsetUnion.2 ⟨cell₁, Finset.mem_inter.2 ⟨hcell₁, hcell₂⟩, hxcell₁⟩

theorem dyadicBoxFinsetUnion_diff {d : Nat} (j : ℤ)
    (s t : Finset (Fin d → ℤ)) :
    dyadicBoxFinsetUnion j (s \ t) =
      dyadicBoxFinsetUnion j s \ dyadicBoxFinsetUnion j t := by
  classical
  ext x
  constructor
  · intro hx
    rcases (mem_dyadicBoxFinsetUnion.1 hx) with ⟨cell, hcell, hxcell⟩
    refine ⟨mem_dyadicBoxFinsetUnion.2 ⟨cell, (Finset.mem_sdiff.1 hcell).1, hxcell⟩, ?_⟩
    intro hxt
    rcases (mem_dyadicBoxFinsetUnion.1 hxt) with ⟨cell', hcell', hxcell'⟩
    by_cases hEq : cell = cell'
    · exact (Finset.mem_sdiff.1 hcell).2 (hEq ▸ hcell')
    · have hdisj := disjoint_dyadicBox_same_scale (j := j) hEq
      rw [Set.disjoint_left] at hdisj
      exact hdisj hxcell hxcell'
  · intro hx
    rcases (mem_dyadicBoxFinsetUnion.1 hx.1) with ⟨cell, hcell, hxcell⟩
    exact mem_dyadicBoxFinsetUnion.2
      ⟨cell, Finset.mem_sdiff.2 ⟨hcell, (by intro hcellt; exact hx.2 (mem_dyadicBoxFinsetUnion.2 ⟨cell, hcellt, hxcell⟩))⟩, hxcell⟩

/-- The finite set of descendants of a dyadic cell after `n` bisections in every coordinate. -/
@[expose]
def dyadicDescendantCellFinset {d : Nat} :
    ℕ → (Fin d → ℤ) → Finset (Fin d → ℤ)
  | 0, cell => {cell}
  | n + 1, cell => (dyadicDescendantCellFinset n cell).biUnion dyadicChildCellFinset

@[simp]
theorem dyadicDescendantCellFinset_zero {d : Nat} (cell : Fin d → ℤ) :
    dyadicDescendantCellFinset 0 cell = {cell} :=
  rfl



theorem dyadicBoxFinsetUnion_refine_nat {d} {n N : ℕ} (hnN : n ≤ N)
    (s : Finset (Fin d → ℤ)) :
    dyadicBoxFinsetUnion (n : ℤ) s =
      dyadicBoxFinsetUnion (N : ℤ)
        (s.biUnion (dyadicDescendantCellFinset (N - n))) := by
  have dyadicBoxFinsetUnion_refine_steps {d : Nat} (j : ℤ) (n : ℕ) (s : Finset (Fin d → ℤ)) : dyadicBoxFinsetUnion j s = dyadicBoxFinsetUnion (j + (n : ℤ)) (s.biUnion (dyadicDescendantCellFinset n)) := by
    classical
    have dyadicBoxFinsetUnion_refine_once {d : Nat} (j : ℤ) (s : Finset (Fin d → ℤ)) : dyadicBoxFinsetUnion j s = dyadicBoxFinsetUnion (j + 1) (s.biUnion dyadicChildCellFinset) := by
      classical
      ext x
      constructor
      · intro hx
        rcases mem_dyadicBoxFinsetUnion.1 hx with ⟨cell, hcell, hxcell⟩
        rw [dyadicBox_eq_dyadicBoxFinsetUnion_children] at hxcell
        rcases mem_dyadicBoxFinsetUnion.1 hxcell with ⟨child, hchild, hxchild⟩
        exact mem_dyadicBoxFinsetUnion.2
          ⟨child, Finset.mem_biUnion.2 ⟨cell, hcell, hchild⟩, hxchild⟩
      · intro hx
        rcases mem_dyadicBoxFinsetUnion.1 hx with ⟨child, hchild, hxchild⟩
        rcases Finset.mem_biUnion.1 hchild with ⟨cell, hcell, hchildcell⟩
        exact mem_dyadicBoxFinsetUnion.2 ⟨cell, hcell, by
          rw [dyadicBox_eq_dyadicBoxFinsetUnion_children]
          exact mem_dyadicBoxFinsetUnion.2 ⟨child, hchildcell, hxchild⟩⟩
    induction n generalizing j s with
    | zero =>
        ext x
        simp [mem_dyadicBoxFinsetUnion]
    | succ n ih =>
        rw [ih, dyadicBoxFinsetUnion_refine_once (j + (n : ℤ))]
        congr 1
        · omega
        · ext cell
          constructor
          · intro hcell
            rcases Finset.mem_biUnion.1 hcell with ⟨childParent, hchildParent, hchild⟩
            rcases Finset.mem_biUnion.1 hchildParent with ⟨parent, hparent, hdesc⟩
            exact Finset.mem_biUnion.2
              ⟨parent, hparent, Finset.mem_biUnion.2 ⟨childParent, hdesc, hchild⟩⟩
          · intro hcell
            rcases Finset.mem_biUnion.1 hcell with ⟨parent, hparent, hchildren⟩
            rcases Finset.mem_biUnion.1 hchildren with ⟨childParent, hdesc, hchild⟩
            exact Finset.mem_biUnion.2
              ⟨childParent, Finset.mem_biUnion.2 ⟨parent, hparent, hdesc⟩, hchild⟩
  simpa [(show (n : ℤ) + ((N - n : ℕ) : ℤ) = (N : ℤ) by omega)] using
    dyadicBoxFinsetUnion_refine_steps (d := d) (j := (n : ℤ)) (n := N - n) s

theorem measurableSet_dyadicBoxFinsetUnion {d : Nat} (j : ℤ)
    (s : Finset (Fin d → ℤ)) :
    MeasurableSet (dyadicBoxFinsetUnion j s) := by
  unfold dyadicBoxFinsetUnion
  exact MeasurableSet.biUnion s.countable_toSet fun cell _hcell =>
    measurableSet_dyadicBox j cell

theorem volume_dyadicBoxFinsetUnion_ne_top {d} j
    s :
    (volume : Measure (Vec d)) (dyadicBoxFinsetUnion j s) ≠ ∞ := by
  unfold dyadicBoxFinsetUnion
  exact (measure_biUnion_lt_top (μ := (volume : Measure (Vec d)))
    (s := (s : Set (Fin d → ℤ))) (Finset.finite_toSet _) fun cell _hcell =>
      lt_top_iff_ne_top.2 (volume_dyadicBox_ne_top j cell)).ne

/-- Finite unions of dyadic boxes at a common nonnegative scale. -/
@[expose]
def nonnegativeDyadicBoxFinsetUnionFamily (d : Nat) : Set (Set (Vec d)) :=
  Set.range fun p : ℕ × Finset (Fin d → ℤ) =>
    dyadicBoxFinsetUnion (d := d) (p.1 : ℤ) p.2

theorem measurableSet_of_mem_nonnegativeDyadicBoxFinsetUnionFamily {d : Nat}
    {s} (hs : s ∈ nonnegativeDyadicBoxFinsetUnionFamily d) :
    MeasurableSet s := by
  rcases hs with ⟨p, rfl⟩
  exact measurableSet_dyadicBoxFinsetUnion (d := d) (p.1 : ℤ) p.2



theorem indicatorConstLp_mem_haarBasisSubmodule_of_mem_nonnegativeDyadicBoxFinsetUnionFamily
    {d} {s}
    (hs : s ∈ nonnegativeDyadicBoxFinsetUnionFamily d)
    hsm (hμs : (volume : Measure (Vec d)) s ≠ ∞) :
    indicatorConstLp 2 hsm hμs (1 : ℝ) ∈ haarBasisSubmodule d := by
  have indicatorConstLp_dyadicBoxFinsetUnion_mem_haarBasisSubmodule_of_nonnegative {d : Nat} {j : ℤ} (hj : 0 ≤ j) (s : Finset (Fin d → ℤ)) : indicatorConstLp 2 (measurableSet_dyadicBoxFinsetUnion j s) (volume_dyadicBoxFinsetUnion_ne_top j s) (1 : ℝ) ∈ haarBasisSubmodule d := by
    classical
    have disjoint_dyadicBox_dyadicBoxFinsetUnion_of_notMem {d : Nat} {j : ℤ} {cell} {s : Finset (Fin d → ℤ)} (hcell : cell ∉ s) : Disjoint (dyadicBox j cell) (dyadicBoxFinsetUnion j s) := by
      rw [Set.disjoint_left]
      intro x hx hxs
      rw [dyadicBoxFinsetUnion] at hxs
      rcases Set.mem_iUnion.1 hxs with ⟨cell', hcell'⟩
      rcases Set.mem_iUnion.1 hcell' with ⟨hmem, hx'⟩
      have hdisj := disjoint_dyadicBox_same_scale (j := j) (show cell ≠ cell' by intro h; exact hcell (h ▸ hmem))
      rw [Set.disjoint_left] at hdisj
      exact hdisj hx hx'
    have dyadicBoxFinsetUnion_insert {d} {cell : Fin d → ℤ} {s} : dyadicBoxFinsetUnion j (insert cell s) = dyadicBox j cell ∪ dyadicBoxFinsetUnion j s := by
      ext x
      simp [dyadicBoxFinsetUnion, Finset.mem_insert]
    have indicatorConstLp_dyadicBox_mem_haarBasisSubmodule_of_nonnegative {d} cell : indicatorConstLp 2 (measurableSet_dyadicBox j cell) (volume_dyadicBox_ne_top j cell) (1 : ℝ) ∈ haarBasisSubmodule d := by
      have haarPacketLp_father_eq_smul_indicatorConstLp {d} j (cell : Fin d → ℤ) : haarPacketLp { scale := j, cell := cell, signature := fun _ => false } = haarBoxScaleFactor d j • indicatorConstLp 2 (measurableSet_dyadicBox j cell) (volume_dyadicBox_ne_top j cell) (1 : ℝ) := by
        refine Lp.ext ?_
        let idx : HaarIndex d := { scale := j, cell := cell, signature := fun _ => false }
        filter_upwards [(memLp_haarPacket idx).coeFn_toLp,
          Lp.coeFn_smul (haarBoxScaleFactor d j)
            (indicatorConstLp 2 (measurableSet_dyadicBox j cell)
              (volume_dyadicBox_ne_top j cell) (1 : ℝ)),
          indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Vec d)))
            (hs := measurableSet_dyadicBox j cell)
            (hμs := volume_dyadicBox_ne_top j cell) (c := (1 : ℝ))] with
          x hpacket hsmul hind
        change (haarPacketLp idx) x =
          (haarBoxScaleFactor d j •
            indicatorConstLp 2 (measurableSet_dyadicBox j cell)
              (volume_dyadicBox_ne_top j cell) (1 : ℝ)) x
        change ((memLp_haarPacket idx).toLp (haarPacket idx)) x =
          (haarBoxScaleFactor d j •
            indicatorConstLp 2 (measurableSet_dyadicBox j cell)
              (volume_dyadicBox_ne_top j cell) (1 : ℝ)) x
        rw [hpacket, hsmul]
        change haarPacket idx x =
          haarBoxScaleFactor d j * (indicatorConstLp 2 (measurableSet_dyadicBox j cell)
            (volume_dyadicBox_ne_top j cell) (1 : ℝ)) x
        rw [hind]
        change haarPacket idx x =
          haarBoxScaleFactor d j *
            Set.indicator (dyadicBox j cell) (fun _ : Vec d => (1 : ℝ)) x
        exact haarPacket_father_eq_indicator_dyadicBox j cell x
      have hsmul :
          (haarBoxScaleFactor d j)⁻¹ •
            haarPacketLp { scale := j, cell := cell, signature := fun _ => false } ∈
            haarBasisSubmodule d :=
        Submodule.smul_mem _ _ (haarPacketLp_father_mem_haarBasisSubmodule_of_nonnegative (d := d) hj cell)
      rw [(haarPacketLp_father_eq_smul_indicatorConstLp (d := d) j cell), smul_smul] at hsmul
      simpa [(inv_mul_cancel₀ ((show haarBoxScaleFactor d j ≠ 0 by unfold haarBoxScaleFactor; exact Finset.prod_ne_zero_iff.2 fun _r _hr => ne_of_gt (haarScaleFactor_pos j))))] using hsmul
    induction s using Finset.induction with
    | empty =>
        simp [dyadicBoxFinsetUnion_empty]
    | insert cell s hcell ih =>
        have hbox := indicatorConstLp_dyadicBox_mem_haarBasisSubmodule_of_nonnegative cell
        have hEq :
            indicatorConstLp 2 (measurableSet_dyadicBoxFinsetUnion j (insert cell s))
              (volume_dyadicBoxFinsetUnion_ne_top j (insert cell s)) (1 : ℝ) =
              indicatorConstLp 2 (measurableSet_dyadicBox j cell)
                (volume_dyadicBox_ne_top j cell) (1 : ℝ) +
              indicatorConstLp 2 (measurableSet_dyadicBoxFinsetUnion j s)
                (volume_dyadicBoxFinsetUnion_ne_top j s) (1 : ℝ) := by
          refine Lp.ext ?_
          filter_upwards [
            indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Vec d)))
              (hs := measurableSet_dyadicBoxFinsetUnion j (insert cell s))
              (hμs := volume_dyadicBoxFinsetUnion_ne_top j (insert cell s))
              (c := (1 : ℝ)),
            Lp.coeFn_add
              (indicatorConstLp 2 (measurableSet_dyadicBox j cell)
                (volume_dyadicBox_ne_top j cell) (1 : ℝ))
              (indicatorConstLp 2 (measurableSet_dyadicBoxFinsetUnion j s)
                (volume_dyadicBoxFinsetUnion_ne_top j s) (1 : ℝ)),
            indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Vec d)))
              (hs := measurableSet_dyadicBox j cell)
              (hμs := volume_dyadicBox_ne_top j cell)
              (c := (1 : ℝ)),
            indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Vec d)))
              (hs := measurableSet_dyadicBoxFinsetUnion j s)
              (hμs := volume_dyadicBoxFinsetUnion_ne_top j s)
              (c := (1 : ℝ))] with x hleft hadd hbox hunion
          rw [hleft, hadd]
          change Set.indicator (dyadicBoxFinsetUnion j (insert cell s))
              (fun _ : Vec d => (1 : ℝ)) x =
            (indicatorConstLp 2 (measurableSet_dyadicBox j cell)
                (volume_dyadicBox_ne_top j cell) (1 : ℝ) :
              Lp ℝ 2 (volume : Measure (Vec d))) x +
              (indicatorConstLp 2 (measurableSet_dyadicBoxFinsetUnion j s)
                (volume_dyadicBoxFinsetUnion_ne_top j s) (1 : ℝ) :
              Lp ℝ 2 (volume : Measure (Vec d))) x
          rw [hbox, hunion]
          change Set.indicator (dyadicBoxFinsetUnion j (insert cell s))
              (fun _ : Vec d => (1 : ℝ)) x =
            Set.indicator (dyadicBox j cell) (fun _ : Vec d => (1 : ℝ)) x +
              Set.indicator (dyadicBoxFinsetUnion j s) (fun _ : Vec d => (1 : ℝ)) x
          rw [dyadicBoxFinsetUnion_insert]
          exact congrFun (Set.indicator_union_of_disjoint (disjoint_dyadicBox_dyadicBoxFinsetUnion_of_notMem hcell) (fun _ : Vec d => (1 : ℝ))) x
        rw [hEq]
        exact Submodule.add_mem _ hbox ih
  rcases hs with ⟨p, rfl⟩
  simpa using
    indicatorConstLp_dyadicBoxFinsetUnion_mem_haarBasisSubmodule_of_nonnegative
      (d := d) (j := (p.1 : ℤ)) (by exact_mod_cast Nat.zero_le p.1) p.2

end GaussianFields

end
