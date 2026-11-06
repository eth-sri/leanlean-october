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

theorem haarBoxScaleFactor_ne_zero (d : Nat) (j : ℤ) :
    haarBoxScaleFactor d j ≠ 0 := by
  exact Finset.prod_ne_zero_iff.2 fun _r _hr => ne_of_gt (haarScaleFactor_pos j)
section
variable {d : Nat}

theorem haarPacketLp_father_eq_smul_indicatorConstLp (j : ℤ) (cell : Fin d → ℤ) :
    haarPacketLp { scale := j, cell := cell, signature := fun _ => false } =
      haarBoxScaleFactor d j •
        indicatorConstLp 2 (measurableSet_dyadicBox j cell)
          (volume_dyadicBox_ne_top j cell) (1 : ℝ) := by
  refine Lp.ext ?_
  let idx : HaarIndex d := { scale := j, cell := cell, signature := fun _ => false }
  filter_upwards [(memLp_haarPacket idx).coeFn_toLp,
    Lp.coeFn_smul (haarBoxScaleFactor d j)
      (indicatorConstLp 2 _
        (volume_dyadicBox_ne_top j cell) (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (μ := volume)
      (hs := measurableSet_dyadicBox j cell)
      (hμs := volume_dyadicBox_ne_top j cell) (c := (1 : ℝ))] with
    x hpacket hsmul hind
  change (haarPacketLp idx) x =
    (haarBoxScaleFactor d j •
      indicatorConstLp 2 _
        (volume_dyadicBox_ne_top j cell) (1 : ℝ)) x
  change ((memLp_haarPacket idx).toLp (haarPacket idx)) x =
    (haarBoxScaleFactor d j •
      indicatorConstLp 2 _
        (volume_dyadicBox_ne_top j cell) (1 : ℝ)) x
  rw [hpacket, hsmul]
  change haarPacket idx x =
    haarBoxScaleFactor d j * (indicatorConstLp 2 _
      (volume_dyadicBox_ne_top j cell) (1 : ℝ)) x
  rw [hind]
  change haarPacket idx x =
    haarBoxScaleFactor d j *
      Set.indicator _ (fun _ => 1) x
  exact haarPacket_father_eq_indicator_dyadicBox j cell x

theorem indicatorConstLp_dyadicBox_mem_haarBasisSubmodule_of_nonnegative
    {j : ℤ} (hj : 0 ≤ j) (cell : Fin d → ℤ) :
    indicatorConstLp 2 (measurableSet_dyadicBox j cell)
      (volume_dyadicBox_ne_top j cell) (1 : ℝ) ∈ haarBasisSubmodule d := by
  have hpacket :=
    haarPacketLp_father_mem_haarBasisSubmodule_of_nonnegative hj cell
  have hsmul :
      (haarBoxScaleFactor d j)⁻¹ •
        haarPacketLp { scale := j, cell := cell, signature := fun _ => false } ∈
        haarBasisSubmodule d :=
    Submodule.smul_mem _ _ hpacket
  rw [(haarPacketLp_father_eq_smul_indicatorConstLp (d := d) j cell), smul_smul] at hsmul
  have hc :=
    inv_mul_cancel₀ (haarBoxScaleFactor_ne_zero d j)
  simp_all

end

/-- The countable family of dyadic boxes at nonnegative scales. -/
@[expose]
def nonnegativeDyadicBoxFamily (d : Nat) : Set (Set (Vec d)) :=
  Set.range fun p : ℕ × (Fin d → ℤ) => dyadicBox (p.1 : ℤ) p.2

theorem measurableSet_of_mem_nonnegativeDyadicBoxFamily {d : Nat}
    {s : Set (Vec d)} (hs : s ∈ nonnegativeDyadicBoxFamily d) :
    MeasurableSet s := by
  rcases hs with ⟨p, rfl⟩
  exact measurableSet_dyadicBox p.1 p.2

/-- At sufficiently fine nonnegative dyadic scale, the mesh is smaller than any positive real. -/
theorem exists_nat_inv_dyadicPower_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, (dyadicPower (n : ℤ))⁻¹ < ε := by
  have hlim :
      Tendsto (fun n => ((1 / 2) ^ n)) atTop (𝓝 (0 : ℝ)) := by
    norm_num
  have hev : ∀ᶠ n in atTop, ((1 / 2 : ℝ) ^ n) ∈ Set.Iio ε :=
    hlim.eventually (Iio_mem_nhds hε)
  aesop

/-- The integer floor cell contains the point at any nonnegative dyadic scale. -/
theorem mem_dyadicInterval_floor (n : ℕ) (x : ℝ) :
    x ∈ dyadicInterval (n : ℤ) ⌊dyadicPower (n : ℤ) * x⌋ := by
  rw [mem_dyadicInterval_iff]
  constructor
  · simp
  · have hfloor : dyadicPower (n : ℤ) * x <
        ((⌊dyadicPower (n : ℤ) * x⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    linarith

/-- Distinct dyadic intervals at the same scale are disjoint. -/
theorem disjoint_dyadicInterval_same_scale {j k₁ k₂ : ℤ} (hk : k₁ ≠ k₂) :
    Disjoint (dyadicInterval j k₁) (dyadicInterval j k₂) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  exact not_both_mem_Ico_sub_int (z := dyadicPower j * x) hk
    ⟨(mem_dyadicInterval_iff j k₁ x).1 hx₁,
      (mem_dyadicInterval_iff j k₂ x).1 hx₂⟩

/-- A dyadic interval is the union of its two children at the next scale. -/
theorem dyadicInterval_eq_union_children (j k : ℤ) :
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
    grind
  constructor
  · intro hx
    have hy : y ∈ Set.Ico (0 : ℝ) 1 := (mem_dyadicInterval_iff j k x).1 hx
    by_cases hyhalf : y < 1 / 2
    · left
      rw [mem_dyadicInterval_iff, hleft]
      grind
    · right
      rw [mem_dyadicInterval_iff, hright]
      grind
  · intro hx
    rw [mem_dyadicInterval_iff]
    rcases hx with hx | hx
    · have hchild : 2 * y ∈ Set.Ico (0 : ℝ) 1 := by
        have hraw := (mem_dyadicInterval_iff _ _ x).1 hx
        simp_all
      grind
    · have hchild : 2 * y - 1 ∈ Set.Ico (0 : ℝ) 1 := by
        have hraw := (mem_dyadicInterval_iff _ _ x).1 hx
        simp_all
      grind
section
variable {d : Nat}

/-- Distinct dyadic boxes at the same scale are disjoint. -/
theorem disjoint_dyadicBox_same_scale {j : ℤ}
    {cell₁ cell₂ : Fin d → ℤ} (hcell : cell₁ ≠ cell₂) :
    Disjoint (dyadicBox j cell₁) (dyadicBox j cell₂) := by
  classical
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hcoord : ∃ r : Fin d, cell₁ r ≠ cell₂ r := by
    grind
  rcases hcoord with ⟨r, hr⟩
  have hdisj := disjoint_dyadicInterval_same_scale (j := j) hr
  rw [Set.disjoint_left] at hdisj
  tauto

/-- A dyadic box is the union of its `2^d` children at the next scale. -/
theorem dyadicBox_eq_iUnion_children (j : ℤ) (cell : Fin d → ℤ) :
    dyadicBox j cell =
      ⋃ side : Fin d → Bool, dyadicBox (j + 1) (haarChildCell cell side) := by
  classical
  ext x
  constructor
  · intro hx
    let side : Fin d → Bool := fun r =>
      if x r ∈ dyadicInterval (j + 1) (2 * cell r) then false else true
    refine Set.mem_iUnion.2 ⟨side, ?_⟩
    intro r _hr
    have hxparent := hx r trivial
    have hxsplit :
        x r ∈ dyadicInterval (j + 1) (2 * cell r) ∪
          dyadicInterval (j + 1) (2 * cell r + 1) := by
      rwa [← dyadicInterval_eq_union_children j (cell r)]
    by_cases hleft : x r ∈ dyadicInterval (j + 1) (2 * cell r)
    · simp [side, haarChildCell, hleft]
    · have hright :=
        hxsplit.resolve_left hleft
      simpa [side, haarChildCell, hleft] using hright
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨side, hxside⟩
    intro r _hr
    have hchild :=
      hxside r trivial
    change x r ∈ dyadicInterval j (cell r)
    rw [dyadicInterval_eq_union_children j (cell r)]
    by_cases hside : side r
    · right
      simpa [haarChildCell, hside] using hchild
    · left
      simpa [haarChildCell, hside] using hchild

end

/-- The finite set of children of a dyadic cell. -/
@[expose]
def dyadicChildCellFinset {d : Nat} (cell : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  (Finset.univ : Finset (Fin d → Bool)).image (haarChildCell cell)

theorem mem_dyadicChildCellFinset {d : Nat} {cell child : Fin d → ℤ} :
    child ∈ dyadicChildCellFinset cell ↔
      ∃ side : Fin d → Bool, haarChildCell cell side = child := by
  classical
  simp [dyadicChildCellFinset]

/-- A finite union of dyadic boxes at one common scale. -/
@[expose]
def dyadicBoxFinsetUnion {d : Nat} (j : ℤ) (s : Finset (Fin d → ℤ)) : Set (Vec d) :=
  ⋃ cell ∈ s, dyadicBox j cell
section
variable {d : Nat}

/-- A dyadic box is a finite union of its children at the next scale. -/
theorem dyadicBox_eq_dyadicBoxFinsetUnion_children (j : ℤ) (cell : Fin d → ℤ) :
    dyadicBox j cell =
      dyadicBoxFinsetUnion (d := d) (j + 1) (dyadicChildCellFinset cell) := by
  rw [dyadicBox_eq_iUnion_children]
  ext x
  simp [dyadicBoxFinsetUnion, mem_dyadicChildCellFinset]
section
variable (r : Fin d) (a : ℝ)

/-- A coordinate half-line is the union of dyadic boxes whose coordinate upper edge lies below
the half-line endpoint. -/
theorem preimage_eval_Iio_eq_iUnion_dyadicBox :
    {x : Vec d | x r < a} =
      ⋃ p : ℕ × (Fin d → ℤ),
        ⋃ _h : (((p.2 r : ℝ) + 1) / dyadicPower (p.1 : ℤ) < a),
          dyadicBox (p.1 : ℤ) p.2 := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_inv_dyadicPower_lt (sub_pos.2 hx)
    let cell : Fin d → ℤ := fun r => ⌊dyadicPower (n : ℤ) * x r⌋
    refine Set.mem_iUnion.2 ⟨(n, cell), ?_⟩
    refine Set.mem_iUnion.2 ⟨?_, ?_⟩
    · let p := dyadicPower (n : ℤ)
      have hp : 0 < p := dyadicPower_pos (n : ℤ)
      have hfloor : ((⌊p * x r⌋ : ℤ) : ℝ) ≤ p * x r :=
        Int.floor_le _
      have hupper_le : (((⌊p * x r⌋ : ℤ) : ℝ) + 1) / p ≤ x r + p⁻¹ := by
        calc
          (((⌊p * x r⌋ : ℤ) : ℝ) + 1) / p ≤ (p * x r + 1) / p := by
            bound
          _ = x r + p⁻¹ := by
            field_simp
      linarith
    · intro s _hs
      exact mem_dyadicInterval_floor n (x s)
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨p, hp⟩
    rcases Set.mem_iUnion.1 hp with ⟨hupper, hbox⟩
    have hr : x r ∈ dyadicInterval (p.1 : ℤ) (p.2 r) := hbox r trivial
    exact hr.2.trans hupper

/-- Coordinate half-lines are measurable for the sigma-algebra generated by nonnegative dyadic
boxes. -/
theorem measurableSet_preimage_eval_Iio_generateFrom_nonnegativeDyadicBoxFamily
    :
    MeasurableSet[MeasurableSpace.generateFrom (nonnegativeDyadicBoxFamily d)]
      {x : Vec d | x r < a} := by
  rw [preimage_eval_Iio_eq_iUnion_dyadicBox r a]
  refine MeasurableSet.iUnion fun p =>
    MeasurableSet.iUnion fun _h =>
      MeasurableSpace.measurableSet_generateFrom ?_
  tauto

end

end

/-- Nonnegative dyadic boxes generate the Borel sigma-algebra on `R^d`. -/
theorem generateFrom_nonnegativeDyadicBoxFamily_eq (d : Nat) :
    MeasurableSpace.generateFrom (nonnegativeDyadicBoxFamily d) =
      (inferInstance : MeasurableSpace (Vec d)) := by
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
        (Set.range Set.Iio) (fun x => x r) ?_
      intro t ht
      rcases ht with ⟨a, rfl⟩
      change MeasurableSet[MeasurableSpace.generateFrom (nonnegativeDyadicBoxFamily d)]
        {x : Vec d | x r < a}
      exact measurableSet_preimage_eval_Iio_generateFrom_nonnegativeDyadicBoxFamily r a
    exact hmeas.comap_le

/-- The set algebra generated by nonnegative dyadic boxes. -/
@[expose]
def nonnegativeDyadicBoxAlgebra (d : Nat) : Set (Set (Vec d)) :=
  generateSetAlgebra (nonnegativeDyadicBoxFamily d)
section
variable (d : Nat)

theorem isSetAlgebra_nonnegativeDyadicBoxAlgebra :
    IsSetAlgebra (nonnegativeDyadicBoxAlgebra d) := isSetAlgebra_generateSetAlgebra

theorem nonnegativeDyadicBoxFamily_subset_algebra :
    nonnegativeDyadicBoxFamily d ⊆ nonnegativeDyadicBoxAlgebra d := self_subset_generateSetAlgebra

theorem measurableSpace_eq_generateFrom_nonnegativeDyadicBoxAlgebra :
    (inferInstance : MeasurableSpace (Vec d)) =
      MeasurableSpace.generateFrom (nonnegativeDyadicBoxAlgebra d) := by
  rw [nonnegativeDyadicBoxAlgebra, generateFrom_generateSetAlgebra_eq]
  exact (generateFrom_nonnegativeDyadicBoxFamily_eq d).symm

end
section
variable {d : Nat}
section
variable (j : ℤ)

theorem dyadicBoxFinsetUnion_empty :
    dyadicBoxFinsetUnion (d := d) j ∅ = ∅ := by
  simp [dyadicBoxFinsetUnion]

theorem dyadicBoxFinsetUnion_insert {cell : Fin d → ℤ} {s : Finset (Fin d → ℤ)} :
    dyadicBoxFinsetUnion j (insert cell s) =
      dyadicBox j cell ∪ dyadicBoxFinsetUnion j s := by
  ext x
  simp [dyadicBoxFinsetUnion, Finset.mem_insert]

end

theorem mem_dyadicBoxFinsetUnion {j : ℤ} {s : Finset (Fin d → ℤ)}
    {x : Vec d} :
    x ∈ dyadicBoxFinsetUnion j s ↔ ∃ cell ∈ s, x ∈ dyadicBox j cell := by
  simp [dyadicBoxFinsetUnion]

theorem dyadicBoxFinsetUnion_singleton (j : ℤ) (cell : Fin d → ℤ) :
    dyadicBoxFinsetUnion j {cell} = dyadicBox j cell := by
  ext x
  simp [mem_dyadicBoxFinsetUnion]

end
section
variable {d : Nat} (j : ℤ) (s t : Finset (Fin d → ℤ))

theorem dyadicBoxFinsetUnion_union :
    dyadicBoxFinsetUnion j (s ∪ t) =
      dyadicBoxFinsetUnion j s ∪ dyadicBoxFinsetUnion j t := by
  ext x
  simp [mem_dyadicBoxFinsetUnion, or_and_right, exists_or]

theorem dyadicBoxFinsetUnion_inter :
    dyadicBoxFinsetUnion j (s ∩ t) =
      dyadicBoxFinsetUnion j s ∩ dyadicBoxFinsetUnion j t := by
  ext x
  constructor
  · intro hx
    rcases (mem_dyadicBoxFinsetUnion.1 hx) with ⟨cell, hcell, hxcell⟩
    exact ⟨mem_dyadicBoxFinsetUnion.2 ⟨cell, (Finset.mem_inter.1 hcell).1, hxcell⟩,
      mem_dyadicBoxFinsetUnion.2 ⟨cell, (Finset.mem_inter.1 hcell).2, hxcell⟩⟩
  · intro hx
    rcases (mem_dyadicBoxFinsetUnion.1 hx.1) with ⟨cell₁, hcell₁, hxcell₁⟩
    rcases (mem_dyadicBoxFinsetUnion.1 hx.2) with ⟨cell₂, hcell₂, hxcell₂⟩
    have hcell_eq : cell₁ = cell₂ := by
      by_contra hne
      have hdisj := disjoint_dyadicBox_same_scale (j := j) hne
      grind
    subst cell₂
    exact mem_dyadicBoxFinsetUnion.2 ⟨cell₁, Finset.mem_inter.2 ⟨hcell₁, hcell₂⟩, hxcell₁⟩

theorem dyadicBoxFinsetUnion_diff :
    dyadicBoxFinsetUnion j (s \ t) =
      dyadicBoxFinsetUnion j s \ dyadicBoxFinsetUnion j t := by
  ext x
  constructor
  · intro hx
    rcases (mem_dyadicBoxFinsetUnion.1 hx) with ⟨cell, hcell, hxcell⟩
    refine ⟨mem_dyadicBoxFinsetUnion.2 ⟨cell, (Finset.mem_sdiff.1 hcell).1, hxcell⟩, ?_⟩
    intro hxt
    rcases (mem_dyadicBoxFinsetUnion.1 hxt) with ⟨cell', hcell', hxcell'⟩
    by_cases hEq : cell = cell'
    · simp_all
    · have hdisj := disjoint_dyadicBox_same_scale (j := j) hEq
      grind
  · intro hx
    rcases (mem_dyadicBoxFinsetUnion.1 hx.1) with ⟨cell, hcell, hxcell⟩
    have hcell_notMem : cell ∉ t := by
      intro hcellt
      exact hx.2 (mem_dyadicBoxFinsetUnion.2 ⟨cell, hcellt, hxcell⟩)
    exact mem_dyadicBoxFinsetUnion.2
      ⟨cell, Finset.mem_sdiff.2 ⟨hcell, hcell_notMem⟩, hxcell⟩

end

/-- The finite set of descendants of a dyadic cell after `n` bisections in every coordinate. -/
@[expose]
def dyadicDescendantCellFinset {d : Nat} :
    ℕ → (Fin d → ℤ) → Finset (Fin d → ℤ)
  | 0, cell => {cell}
  | n + 1, cell => (dyadicDescendantCellFinset n cell).biUnion dyadicChildCellFinset
section
variable {d : Nat}

@[simp]
theorem dyadicDescendantCellFinset_zero (cell : Fin d → ℤ) :
    dyadicDescendantCellFinset 0 cell = {cell} :=
  rfl

theorem dyadicBoxFinsetUnion_refine_once (j : ℤ)
    (s : Finset (Fin d → ℤ)) :
    dyadicBoxFinsetUnion j s =
      dyadicBoxFinsetUnion (j + 1) (s.biUnion dyadicChildCellFinset) := by
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

theorem dyadicBoxFinsetUnion_refine_steps (j : ℤ) (n : ℕ)
    (s : Finset (Fin d → ℤ)) :
    dyadicBoxFinsetUnion j s =
      dyadicBoxFinsetUnion (j + (n : ℤ))
        (s.biUnion (dyadicDescendantCellFinset n)) := by
  classical
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

theorem dyadicBoxFinsetUnion_refine_nat {n N : ℕ} (hnN : n ≤ N)
    (s : Finset (Fin d → ℤ)) :
    dyadicBoxFinsetUnion (n : ℤ) s =
      dyadicBoxFinsetUnion (N : ℤ)
        (s.biUnion (dyadicDescendantCellFinset (N - n))) := by
  have hscale : n + ((N - n : ℕ) : ℤ) = (N : ℤ) := by
    omega
  simpa [hscale] using
    dyadicBoxFinsetUnion_refine_steps (d := d) (j := n) (n := N - n) s

end
section
variable {d : Nat} (j : ℤ) (s : Finset (Fin d → ℤ))

theorem measurableSet_dyadicBoxFinsetUnion :
    MeasurableSet (dyadicBoxFinsetUnion j s) := by
  exact MeasurableSet.biUnion s.countable_toSet fun cell _hcell =>
    measurableSet_dyadicBox j cell

theorem volume_dyadicBoxFinsetUnion_ne_top :
    (volume : Measure (Vec d)) (dyadicBoxFinsetUnion j s) ≠ ∞ := by
  exact (measure_biUnion_lt_top
    (Finset.finite_toSet _) fun cell _hcell =>
      lt_top_iff_ne_top.2 (volume_dyadicBox_ne_top j cell)).ne

end

/-- Finite unions of dyadic boxes at a common nonnegative scale. -/
@[expose]
def nonnegativeDyadicBoxFinsetUnionFamily (d : Nat) : Set (Set (Vec d)) :=
  Set.range fun p : ℕ × Finset (Fin d → ℤ) =>
    dyadicBoxFinsetUnion (d := d) (p.1 : ℤ) p.2
section
variable {d : Nat}

theorem measurableSet_of_mem_nonnegativeDyadicBoxFinsetUnionFamily {s : Set (Vec d)} (hs : s ∈ nonnegativeDyadicBoxFinsetUnionFamily d) :
    MeasurableSet s := by
  rcases hs with ⟨p, rfl⟩
  exact measurableSet_dyadicBoxFinsetUnion p.1 p.2
section
variable {j : ℤ}

theorem disjoint_dyadicBox_dyadicBoxFinsetUnion_of_notMem {cell : Fin d → ℤ} {s : Finset (Fin d → ℤ)} (hcell : cell ∉ s) :
    Disjoint (dyadicBox j cell) (dyadicBoxFinsetUnion j s) := by
  rw [Set.disjoint_left]
  intro x hx hxs
  rw [dyadicBoxFinsetUnion] at hxs
  rcases Set.mem_iUnion.1 hxs with ⟨cell', hcell'⟩
  rcases Set.mem_iUnion.1 hcell' with ⟨hmem, hx'⟩
  have hne : cell ≠ cell' := by
    aesop
  have hdisj := disjoint_dyadicBox_same_scale (j := j) hne
  grind

theorem indicatorConstLp_dyadicBoxFinsetUnion_mem_haarBasisSubmodule_of_nonnegative
    (hj : 0 ≤ j) (s : Finset (Fin d → ℤ)) :
    indicatorConstLp 2 (measurableSet_dyadicBoxFinsetUnion j s)
      (volume_dyadicBoxFinsetUnion_ne_top j s) (1 : ℝ) ∈
      haarBasisSubmodule d := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [dyadicBoxFinsetUnion_empty]
  | insert cell s hcell ih =>
      have hbox :
          indicatorConstLp 2 _
            (volume_dyadicBox_ne_top j cell) (1 : ℝ) ∈ haarBasisSubmodule d :=
        indicatorConstLp_dyadicBox_mem_haarBasisSubmodule_of_nonnegative hj cell
      have hdisj :
          Disjoint (dyadicBox j cell) (dyadicBoxFinsetUnion j s) :=
        disjoint_dyadicBox_dyadicBoxFinsetUnion_of_notMem hcell
      have hEq :
          indicatorConstLp 2 (measurableSet_dyadicBoxFinsetUnion j (insert cell s))
            (volume_dyadicBoxFinsetUnion_ne_top j (insert cell s)) (1 : ℝ) =
            indicatorConstLp 2 (measurableSet_dyadicBox j cell)
              (volume_dyadicBox_ne_top j cell) (1 : ℝ) +
            indicatorConstLp 2 (measurableSet_dyadicBoxFinsetUnion j s)
              (volume_dyadicBoxFinsetUnion_ne_top j s) (1 : ℝ) := by
        refine Lp.ext ?_
        filter_upwards [
          indicatorConstLp_coeFn (p := 2) (μ := volume)
            (hs := measurableSet_dyadicBoxFinsetUnion j _)
            (hμs := volume_dyadicBoxFinsetUnion_ne_top j _)
            (c := (1 : ℝ)),
          Lp.coeFn_add
            (indicatorConstLp 2 _
              (volume_dyadicBox_ne_top j cell) (1 : ℝ))
            (indicatorConstLp 2 _
              (volume_dyadicBoxFinsetUnion_ne_top j s) (1 : ℝ)),
          indicatorConstLp_coeFn (p := 2) (μ := volume)
            (hs := measurableSet_dyadicBox j cell)
            (hμs := volume_dyadicBox_ne_top j cell)
            (c := (1 : ℝ)),
          indicatorConstLp_coeFn (p := 2) (μ := volume)
            (hs := measurableSet_dyadicBoxFinsetUnion j s)
            (hμs := volume_dyadicBoxFinsetUnion_ne_top j s)
            (c := (1 : ℝ))] with x hleft hadd hbox hunion
        rw [hleft, hadd]
        change Set.indicator _
            (fun _ => 1) x =
          (indicatorConstLp 2 _
              (volume_dyadicBox_ne_top j cell) 1 :
            Lp ℝ 2 volume) x +
            (indicatorConstLp 2 _
              (volume_dyadicBoxFinsetUnion_ne_top j s) 1 :
            Lp ℝ 2 volume) x
        rw [hbox, hunion]
        change Set.indicator _
            (fun _ => 1) x =
          Set.indicator _ (fun _ => 1) x +
            Set.indicator _ (fun _ => 1) x
        rw [dyadicBoxFinsetUnion_insert j]
        exact congrFun (Set.indicator_union_of_disjoint hdisj (fun _ : Vec d => (1 : ℝ))) x
      rw [hEq]
      exact Submodule.add_mem _ hbox ih

end

theorem indicatorConstLp_mem_haarBasisSubmodule_of_mem_nonnegativeDyadicBoxFinsetUnionFamily
    {s : Set (Vec d)}
    (hs : s ∈ nonnegativeDyadicBoxFinsetUnionFamily d)
    (hsm : MeasurableSet s) (hμs : (volume : Measure (Vec d)) s ≠ ∞) :
    indicatorConstLp 2 hsm hμs (1 : ℝ) ∈ haarBasisSubmodule d := by
  rcases hs with ⟨p, rfl⟩
  simpa using
    indicatorConstLp_dyadicBoxFinsetUnion_mem_haarBasisSubmodule_of_nonnegative
      (by simp) p.2

end

end GaussianFields

end
