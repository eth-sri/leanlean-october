/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopedSourcePrefixLayer

/-! # Weighted owners on a source-prefix layer

Install weighted nodes and ceiling-height leaves at one actual index. A node's
diagonal is its weight, not the common source ceiling. Its row is the master
source capped at that weight; the master source includes the weighted columns
of *every* sibling. All inherited rows remain literal.

This proves the row-construction step, including cross-grade locality and
availability, from lawful predecessor sources. It does not construct receiving
predecessor sources or prove lifting. No shortness assumption is made on old
rows: in particular, their long ladder rows are retained unchanged.
-/

@[expose] public section

namespace VaughtConjecture.Knight.WeightedSourcePrefixLayer
open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer
noncomputable section

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
variable (F : ScopedSourcePrefixLayer.Data D k X)
variable (weight : Controller D k → ExtOrd)

section
variable (q : Controller D k)

/-- The uncapped master has weighted new columns and literal old columns. -/
def master (d : Cell D) : ExtOrd :=
  if hd : D.cell d = (A, k) then min (F.profile q d) (weight ⟨d, hd⟩)
  else F.profile q d

theorem master_old {d} (hd : D.cell d ≠ (A, k)) :
    master F weight q d = F.lower q d := by
  simp only [master, hd, ↓reduceDIte, F.profile_old q hd]

end

theorem master_new q p :
    master F weight q p.1 = min (cut F.grid (F.boundary q) (F.boundary p)) (weight p) := by
  simp only [master, p.2, ↓reduceDIte, F.profile_new]

section
variable (q : Controller D k) (d : Cell D)

theorem master_le_profile  :
    master F weight q d ≤ F.profile q d := by
  unfold master
  grind

theorem master_bound (hd : D.grade d ≤ k) :
    master F weight q d ≤ F.ceiling :=
  (master_le_profile F weight q d).trans (F.profile_bound q d hd)

end

theorem master_agreement p q d (hd : D.grade d ≤ k) :
    min (master F weight p d) (cut F.grid (F.boundary p) (F.boundary q)) =
      min (master F weight q d) (cut F.grid (F.boundary p) (F.boundary q)) := by
  unfold master
  split_ifs with he
  · simpa only [min_right_comm] using
      congrArg (fun x => min x (weight ⟨d, he⟩)) (F.profile_agreement p q d hd)
  · exact F.profile_agreement p q d hd

theorem master_prefix {p q} {h}
    (hh : h ∈ F.grid) (hpq : Agree (F.boundary p) (F.boundary q) h) :
    Agree (fun d => master F weight p d.1)
      (fun d : D.below (A, k) => master F weight q d.1) h := by
  have ha : Agree (fun d => master F weight p d.1)
      (fun d : D.below (A, k) => master F weight q d.1)
      (cut F.grid (F.boundary p) (F.boundary q)) :=
    fun d => master_agreement F weight p q d.1 d.2.2
  exact ha.mono (le_cut hh hpq)

variable (hvis : ∀ q, SelfVis k (weight q))

include hvis in
theorem master_visible (q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    SelfVis (D.grade d) (master F weight q d) := by
  unfold master
  split_ifs with he
  · exact selfVis_min (F.profile_visible q d hd) ((hvis ⟨d, he⟩).mono hd)
  · exact F.profile_visible q d hd

/-- Weighted installation only changes the new index. -/
def rows : Semantics D where
  E c d := if hc : D.cell c = (A, k) then
    min (master F weight ⟨c, hc⟩ d.1) (weight ⟨c, hc⟩) else F.base.E c d
  orderly c d := by
    dsimp only
    split_ifs with hc
    · have hd : D.grade d.1 ≤ k := by
        simpa only [CellScheme.grade, hc] using d.2.2
      exact (selfVis_min (master_visible F weight hvis ⟨c, hc⟩ d.1 hd)
        ((hvis ⟨c, hc⟩).mono hd)).symm
    · exact F.base.orderly c d

theorem row_old {c} (hc : D.cell c ≠ (A, k)) :
    (rows F weight hvis).E c = F.base.E c := by
  simp only [rows, hc, ↓reduceDIte]

theorem row_new q d :
    (rows F weight hvis).E q.1 d = min (master F weight q d.1) (weight q) := by
  simp only [rows, q.2, ↓reduceDIte]

theorem old_respects_iff {c} (hc : D.cell c ≠ (A, k))
    {r} :
    RespectsSemanticsBelow (rows F weight hvis) (D.cell c) r ↔
      RespectsSemanticsBelow F.base (D.cell c) r := by
  constructor <;> intro hr <;> refine ⟨hr.orderly, ?_, hr.availability⟩
  · intro d
    simpa only [row_old F weight hvis (F.below_old hc d)] using hr.locality d
  · intro d
    rw [row_old F weight hvis (F.below_old hc d)]
    exact hr.locality d

theorem master_locality (q p : Controller D k) :
    TransformsTo (fun d => D.grade d.1)
      ((rows F weight hvis).E p.1)
      (fun d => min (master F weight q d.1) (master F weight q p.1)) := by
  have hb (d : D.below (D.cell p.1)) : D.grade d.1 ≤ k := by
    simpa only [CellScheme.grade, p.2] using d.2.2
  have ht := (TransformsTo.refl
    (grade := fun d => D.grade d.1)
    ((rows F weight hvis).E p.1)).cap
    hb (F.grid_visible _ (cut_mem F.bot_mem (F.boundary q) (F.boundary p)))
  have he : (fun d =>
      min ((rows F weight hvis).E p.1 d) (cut F.grid (F.boundary q) (F.boundary p))) =
      (fun d => min (master F weight q d.1) (master F weight q p.1)) := by
    funext d
    rw [row_new, master_new, min_right_comm,
      ← master_agreement F weight q p d.1 (hb d)]
    exact min_assoc _ _ _
  rwa [he] at ht

variable (hbound : ∀ q, weight q ≤ F.ceiling)

include hbound in
theorem diagonal (q : Controller D k) :
    (rows F weight hvis).E q.1 ⟨q.1, GradedLe.refl _⟩ = weight q := by
  simp only [rows, q.2, ↓reduceDIte]
  rw [master_new, cut_refl F.ceiling_mem F.grid_bound,
    min_eq_right (hbound q), min_self]

include hbound in
theorem parent_read (q p : Controller D k)
    (hp : F.boundary p = F.boundary q) (hw : weight p = F.ceiling) :
    (rows F weight hvis).E q.1 ⟨p.1, by rw [p.2, q.2]; exact GradedLe.refl _⟩ =
      weight q := by
  simp only [rows, q.2, ↓reduceDIte]
  rw [master_new, hp, hw, cut_refl F.ceiling_mem F.grid_bound, min_self,
    min_eq_right (hbound q)]

include hbound in
/-- Actual locality promotes a top weighted node to its ceiling leaf; this is
about arbitrary lawful sections, not selected source displays. -/
theorem le_parent {BJ : Finset ι × ℕ} (hBJ : GradedLe (A, k) BJ)
    {v : D.below BJ → ExtOrd} (hv : RespectsSemanticsBelow (rows F weight hvis) BJ v)
    (q p : Controller D k) (hp : F.boundary p = F.boundary q)
    (hw : weight p = F.ceiling) :
    v ⟨q.1, q.2.symm ▸ hBJ⟩ ≤ v ⟨p.1, p.2.symm ▸ hBJ⟩ := by
  let c : D.below BJ := ⟨q.1, q.2.symm ▸ hBJ⟩
  let self : D.below (D.cell q.1) := ⟨q.1, GradedLe.refl _⟩
  let parent : D.below (D.cell q.1) :=
    ⟨p.1, by rw [p.2, q.2]; exact GradedLe.refl _⟩
  have he :=
    (parent_read F weight hvis hbound q p hp hw).trans
      (diagonal F weight hvis hbound q).symm
  obtain ⟨g, σ, _, _, _, _, _, hr⟩ := hv.locality c
  have ha := hr parent
  have hb := hr self
  have hg : D.grade p.1 = D.grade q.1 :=
    (congrArg Prod.snd p.2).trans (congrArg Prod.snd q.2).symm
  change min (v ⟨p.1, p.2.symm ▸ hBJ⟩) (v c) =
    min (σ ((rows F weight hvis).E q.1 parent)) (g (D.grade p.1)) at ha
  change min (v c) (v c) =
    min (σ ((rows F weight hvis).E q.1 self)) (g (D.grade q.1)) at hb
  rw [he, hg, ← hb, min_self] at ha
  exact min_eq_right_iff.mp ha

include hvis in
/-- Weighted columns introduce no unhosted orbit: below a common cut a field
node's weight is represented by this source's own field vector. -/
theorem master_supported
    (hkind : ∀ p, weight p = F.ceiling ∨ ∃ x, weight p = F.boundary p x)
    (hlower : ∀ q d, D.grade d ≤ k → D.cell d ≠ (A, k) →
      OrbitPrefixSupport.Supported k (F.grid : Set ExtOrd) (F.boundary q) (F.lower q d))
    (q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    OrbitPrefixSupport.Supported k (F.grid : Set ExtOrd) (F.boundary q)
      (master F weight q d) := by
  by_cases he : D.cell d = (A, k)
  · let p : Controller D k := ⟨d, he⟩
    change OrbitPrefixSupport.Supported k (F.grid : Set ExtOrd) (F.boundary q)
      (master F weight q p.1)
    rw [master_new]
    by_cases hc : cut F.grid (F.boundary q) (F.boundary p) ≤ weight p
    · rw [min_eq_left hc]
      exact Or.inr (Or.inl (cut_mem F.bot_mem _ _))
    · have hc' := lt_of_not_ge hc
      rw [min_eq_right hc'.le]
      rcases hkind p with hw | ⟨x, hw⟩
      · exact False.elim (hc ((cut_le F.grid_bound _ _).trans_eq hw.symm))
      · have ha := agree_cut F.bot_mem (F.boundary q) (F.boundary p) x
        rw [← hw, min_eq_left hc'.le] at ha
        have hx : F.boundary q x = weight p := by grind
        exact Or.inr (Or.inr ⟨x, 0, Nat.zero_le _, by
          rw [hx]; exact (evr_eq_self_of_selfVis (hvis p) 0).symm⟩)
  · rw [master_old F weight q he]
    exact hlower q d hd he

/-- A ceiling leaf with the same source supplies availability even for zero nodes. -/
theorem master_respects
    (hleaf : ∀ q, ∃ p, F.boundary p = F.boundary q ∧ weight p = F.ceiling)
    (q : Controller D k) :
    RespectsSemanticsBelow (rows F weight hvis) (A, k)
      (fun d => master F weight q d.1) where
  orderly d := (master_visible F weight hvis q d.1 d.2.2).symm
  locality c := by
    by_cases hc : D.cell c.1 = (A, k)
    · exact master_locality F weight hvis q ⟨c.1, hc⟩
    · have ht := (F.lower_lawful q c.1 c.2.2 hc).locality ⟨c.1, GradedLe.refl _⟩
      simpa only [row_old F weight hvis hc, master_old F weight q hc,
        master_old F weight q (F.below_old hc _), CellScheme.below.incl] using ht
  availability c t hs hg := by
    by_cases ht : D.cell t.1 = (A, k)
    · obtain ⟨p, hp, hw⟩ := hleaf q
      refine ⟨⟨p.1, by grind⟩, p.2.trans ht.symm, ?_⟩
      rw [master_new, hp, hw, cut_refl F.ceiling_mem F.grid_bound, min_self]
      exact master_bound F weight q c.1 c.2.2
    · have hc : GradedLe (D.cell c.1) (D.cell t.1) := ⟨hs, hg.le⟩
      obtain ⟨w, hw, hle⟩ := (F.lower_lawful q t.1 t.2.2 ht).availability
        ⟨c.1, hc⟩ ⟨t.1, GradedLe.refl _⟩ hs hg
      refine ⟨⟨w.1, w.2.trans t.2⟩, hw, ?_⟩
      simpa only [master_old F weight q (F.below_old ht ⟨c.1, hc⟩),
        master_old F weight q (F.below_old ht w)] using hle

theorem consistent
    (hleaf : ∀ q, ∃ p, F.boundary p = F.boundary q ∧ weight p = F.ceiling)
    (hbase : ∀ c, D.cell c ≠ (A, k) →
      RespectsSemanticsBelow F.base (D.cell c) (F.base.E c)) :
    (rows F weight hvis).IsConsistent := by
  intro c
  by_cases hc : D.cell c = (A, k)
  · have hr := (master_respects F weight hvis hleaf ⟨c, hc⟩).cap (hvis ⟨c, hc⟩)
    have ht := GradeCutLayerRows.cast_respects D (rows F weight hvis) hc.symm hr
    convert ht using 1
    exact funext (row_new F weight hvis ⟨c, hc⟩)
  · rw [row_old F weight hvis hc]
    exact (old_respects_iff F weight hvis hc).mpr (hbase c hc)

end
end VaughtConjecture.Knight.WeightedSourcePrefixLayer
