
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.SourcePrefixRows

/-! # Installing one common-prefix controller layer

On an actual finite cell scheme, replace the rows at one maximal full-scope
grade by common-prefix rows. All other rows stay literal. The input profiles
are lawful only on the already constructed lower domains. The new-controller
incidences and their availability are constructed here, not input assumptions.

This is the row-installation half of the coupled grade induction. Existence
of the supported, grid-compatible selected lower profiles is still separate;
no full source-prefix extension or bountifulness theorem is claimed here.
-/

namespace VaughtConjecture.Knight.SourcePrefixLayer

open Transform   SourcePrefixRows

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}

abbrev Controller (D : CellScheme A) (k : ℕ) := {c : Cell D // D.cell c = (A, k)}

/-- An old owner's entire lower domain is old. In particular no full-scope
controller at grade `k` has been smuggled into a proper face. -/
theorem below_old (hmax : BoundedBy D.grade k)
    {c} (hc : D.cell c ≠ (A, k)) (d : D.belowCell c) :
    D.cell d.1 ≠ (A, k) := by
  intro hd
  apply hc
  apply Prod.ext
  · apply Finset.Subset.antisymm (D.scope_subset c)
    change A ⊆ (D.cell c).1
    simpa only [hd] using d.2.1
  · apply le_antisymm (hmax c)
    change k ≤ (D.cell c).2
    simpa only [hd] using d.2.2

/-- The actual lower-domain input to one grade step. `lower_lawful` concerns
only old owners. `grid_agreement` is the grid-agreement invariant of the already
constructed whole lower sections, not new-row locality or future completion.
The new-controller source readings are not fields: `profile` constructs them.
-/
structure Data (D : CellScheme A) (k : ℕ) (X : Type*) where
  base : Semantics D
  max_grade : ∀ d , D.grade d ≤ k
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis k h
  boundary : Controller D k → X → ExtOrd
  lower : Controller D k → CellLabels D
  lower_bound : ∀ q d, D.cell d ≠ (A, k) → lower q d ≤ ceiling
  lower_lawful : ∀ q c, D.cell c ≠ (A, k) →
    Semantics.RowLawful base c (fun d => lower q d.1)
  grid_agreement : ∀ p q h, h ∈ grid → Agree (boundary p) (boundary q) h →
    ∀ d, D.cell d ≠ (A, k) → min (lower p d) h = min (lower q d) h

namespace Data

variable (F : Data D k X)

local notation "Controller₀" => Controller D k

noncomputable def profile (q : Controller₀) (d : Cell D) :=
  if hd : D.cell d = (A, k) then cut F.grid (F.boundary q) (F.boundary ⟨d, hd⟩)
  else F.lower q d

theorem profile_old (q : Controller₀) {d : Cell D} (hd : D.cell d ≠ (A, k)) :
    F.profile q d = F.lower q d := by simp only [profile, hd, ↓reduceDIte]

theorem profile_new (q p : Controller₀) :
    F.profile q p.1 = cut F.grid (F.boundary q) (F.boundary p) := by
  simp only [profile, p.2, ↓reduceDIte]

theorem profile_diagonal (q : Controller₀) : F.profile q q.1 = F.ceiling := by
  rw [F.profile_new]
  exact cut_refl F.ceiling_mem F.grid_bound _

theorem profile_bound (q : Controller₀) (d : Cell D) : F.profile q d ≤ F.ceiling := by
  by_cases hd : D.cell d = (A, k)
  · rw [show d = (⟨d, hd⟩ : Controller₀).1 from rfl, F.profile_new]
    exact cut_le F.grid_bound
  · rw [F.profile_old q hd]
    exact F.lower_bound q d hd

theorem profile_visible (q : Controller₀) (d : Cell D) :
    SelfVis (D.grade d) (F.profile q d) := by
  by_cases hd : D.cell d = (A, k)
  · have hg : D.grade d = k := congrArg Prod.snd hd
    rw [hg, show d = (⟨d, hd⟩ : Controller₀).1 from rfl, F.profile_new]
    exact F.grid_visible _ (cut_mem F.bot_mem _ _)
  · rw [F.profile_old q hd]
    exact ((F.lower_lawful q d hd).orderly ⟨d, GradedLe.refl _⟩).symm

theorem profile_agreement (q p : Controller₀) :
    Agree (F.profile q) (F.profile p) (cut F.grid (F.boundary q) (F.boundary p)) := by
  intro d
  by_cases hd : D.cell d = (A, k)
  · rw [show d = (⟨d, hd⟩ : Controller₀).1 from rfl, F.profile_new, F.profile_new]
    exact cross_agreement F.bot_mem _ _ _
  · rw [F.profile_old q hd, F.profile_old p hd]
    exact F.grid_agreement q p _ (cut_mem F.bot_mem _ _) (agree_cut F.bot_mem _ _) d hd

def profile_prefix {p q : Controller₀} {h : ExtOrd}
    (hh : h ∈ F.grid) (hpq : Agree (F.boundary p) (F.boundary q) h) :=
  (F.profile_agreement p q).mono (le_cut hh hpq)

/-- Shortness of new rows is proved entry by entry, not imposed as a new-row
locality assumption. Only the selected old part and source grid are inputs. -/
theorem profile_short
    (hgrid : ∀ h ∈ F.grid, SharpWitnessComposition.Short k h)
    (hlower : ∀ q d, D.cell d ≠ (A, k) →
      SharpWitnessComposition.Short k (F.lower q d)) (q : Controller₀) :
    ∀ d, SharpWitnessComposition.Short k (F.profile q d) := by
  intro d
  by_cases hd : D.cell d = (A, k)
  · rw [show d = (⟨d, hd⟩ : Controller₀).1 from rfl, F.profile_new]
    exact hgrid _ (cut_mem F.bot_mem _ _)
  · rw [F.profile_old q hd]
    exact hlower q d hd

noncomputable def rows : Semantics D where
  E c d := if hc : D.cell c = (A, k) then F.profile ⟨c, hc⟩ d.1 else F.base.E c d
  orderly c d := by
    dsimp only
    split_ifs with hc
    · exact (F.profile_visible ⟨c, hc⟩ d.1).symm
    · exact F.base.orderly c d

theorem row_old {c} (hc : D.cell c ≠ (A, k)) : F.rows.E c = F.base.E c := by
  funext d
  simp only [rows, hc, ↓reduceDIte]

theorem row_new (q : Controller₀) (d : D.belowCell q.1) :
    F.rows.E q.1 d = F.profile q d.1 := by
  simp only [rows, q.2, ↓reduceDIte]

/-- Full-source shortness propagates from the preceding layers. -/
theorem full_source_short
    (hgrid : ∀ h ∈ F.grid, SharpWitnessComposition.Short k h)
    (hlower : ∀ q d, D.cell d ≠ (A, k) →
      SharpWitnessComposition.Short k (F.lower q d))
    (hbase : ∀ c , D.scope c = A → D.cell c ≠ (A, k) →
      ∀ d , SharpWitnessComposition.Short (D.grade c) (F.base.E c d)) :
    ∀ c , D.scope c = A → ∀ d ,
      SharpWitnessComposition.Short (D.grade c) (F.rows.E c d) := by
  intro c hs d
  by_cases hc : D.cell c = (A, k)
  · have he : F.rows.E c d = F.profile ⟨c, hc⟩ d.1 := F.row_new ⟨c, hc⟩ d
    rw [he, show D.grade c = k from congrArg Prod.snd hc]
    exact F.profile_short hgrid hlower ⟨c, hc⟩ d.1
  · rw [F.row_old hc]
    exact hbase c hs hc d

/-- Respect on each old lower domain is literally unchanged. -/
theorem old_respects_iff {c} (hc : D.cell c ≠ (A, k))
    {r} :
    RespectsSemanticsBelow F.rows (D.cell c) r ↔
      Semantics.RowLawful F.base c r := by
  constructor <;> intro hr <;> refine ⟨hr.orderly, ?_, hr.availability⟩
  · intro d
    simpa only [F.row_old (below_old F.max_grade hc d)] using hr.locality d
  · intro d
    rw [F.row_old (below_old F.max_grade hc d)]
    exact hr.locality d

/-- Locality at every newly installed controller, using its actual
cross-reading as cap. The identity-and-cap witness covers the whole lower
domain, including every previously installed auxiliary. -/
def new_locality (q p : Controller₀) := by
  have ht := (TransformsTo.refl
     (F.rows.E p.1)).cap
    (fun d => F.max_grade d.1)
    (F.grid_visible _ (cut_mem F.bot_mem (F.boundary q) (F.boundary p)))
  have he : (fun d =>
      min (F.rows.E p.1 d) (cut F.grid (F.boundary q) (F.boundary p))) =
      (fun d => min (F.profile q d.1) (F.profile q p.1)) := by
    funext d
    rw [F.row_new, F.profile_new]
    exact (F.profile_agreement q p d.1).symm
  rwa [he] at ht

/-- A constructed whole row is lawful on the actual carrier. Old-target
availability is taken from that target's lawful lower section; new-target
availability uses the row's own diagonal controller inside the target.
No whole-section lawfulness is assumed. -/
theorem profile_respects (q : Controller₀) : RespectsSemantics F.rows (F.profile q) where
  orderly d := (F.profile_visible q d).symm
  locality c := by
    by_cases hc : D.cell c = (A, k)
    · exact F.new_locality q ⟨c, hc⟩
    · have ht := (F.lower_lawful q c hc).locality ⟨c, GradedLe.refl _⟩
      simpa only [F.row_old hc, F.profile_old q hc,
        F.profile_old q (below_old F.max_grade hc _), CellScheme.below.incl] using ht
  availability c t hs hg := by
    by_cases ht : D.cell t = (A, k)
    · refine ⟨q.1, q.2.trans ht.symm, ?_⟩
      rw [F.profile_diagonal]
      exact F.profile_bound q c
    · have hc : GradedLe (D.cell c) (D.cell t) := ⟨hs, hg.le⟩
      obtain ⟨w, hw, hle⟩ := (F.lower_lawful q t ht).availability
        ⟨c, hc⟩ ⟨t, GradedLe.refl _⟩ hs hg
      refine ⟨w.1, hw, ?_⟩
      simpa only [F.profile_old q (below_old F.max_grade ht ⟨c, hc⟩),
        F.profile_old q (below_old F.max_grade ht w)] using hle

/-- The actual one-layer consistency constructor. It consumes consistency
only at old owners, never a consistency assumption for the rows it creates. -/
theorem consistent
    (hbase : ∀ c , D.cell c ≠ (A, k) →
      Semantics.RowLawful F.base c (F.base.E c)) : F.rows.IsConsistent := by
  intro c
  by_cases hc : D.cell c = (A, k)
  · let q : Controller₀ := ⟨c, hc⟩
    have hp := F.profile_respects q
    have he : F.rows.E q.1 = fun d => F.profile q d.1 := funext (F.row_new q)
    change RespectsSemanticsBelow F.rows (D.cell q.1) (F.rows.E q.1)
    refine ⟨F.rows.orderly c, ?_, ?_⟩
    · intro d
      simpa only [he, CellScheme.below.incl] using hp.locality d.1
    · intro d t hs hg
      obtain ⟨w, hw, hle⟩ := hp.availability d.1 t.1 hs hg
      refine ⟨⟨w, ?_⟩, hw, ?_⟩
      · rw [hw]
        exact t.2
      · simpa only [he] using hle
  · rw [F.row_old hc]
    exact (F.old_respects_iff hc).mpr (hbase c hc)

/-- Decode a constructed row without assuming that protected proper rows
are short. Proper-owner locality comes from the literal decoded boundary.
All full-scope source rows are grade-short by the coupled construction, so
the repaired composition theorem supplies their faithful witnesses, including
clause 5 at every threshold. Availability is transported on actual indices.
-/
theorem decoded_respects (q : Controller₀) {K : ℕ} (hkK : k ≤ K)
    {ν : LabelMap} (hν : Witness (gTop K) ν)
    (hproper : ∀ c , D.scope c ≠ A →
      Semantics.RowLawful F.base c (fun d => ν (F.lower q d.1)))
    (hshort : ∀ c , D.scope c = A → ∀ d ,
      SharpWitnessComposition.Short (D.grade c) (F.rows.E c d)) :
    RespectsSemantics F.rows (fun d => ν (F.profile q d)) where
  orderly d := by
    have h := hν.clause5 (F.profile q d) (D.grade d)
      (by rw [gTop_of_le ((F.max_grade d).trans hkK)]; exact le_top) (D.grade d) le_rfl
    rwa [F.profile_visible q d] at h
  locality c := by
    by_cases hc : D.scope c = A
    · exact SharpWitnessComposition.map_capped_locality
        
        (c := (⟨c, GradedLe.refl _⟩))
        (p := fun d : D.belowCell c => F.profile q d.1) (fun d => d.2.2)
        ((F.max_grade c).trans hkK) (hshort c hc) (F.profile_visible q c)
        ((F.profile_respects q).locality c) hν
    · have hc' : D.cell c ≠ (A, k) := fun he => hc (congrArg Prod.fst he)
      have ht := (hproper c hc).locality ⟨c, GradedLe.refl _⟩
      simpa only [F.row_old hc', F.profile_old q hc',
        F.profile_old q (below_old F.max_grade hc' _), CellScheme.below.incl] using ht
  availability c t hs hg := by
    obtain ⟨w, hw, hle⟩ := (F.profile_respects q).availability c t hs hg
    exact ⟨w, hw, hν.mono hle⟩


