/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourcePrefixRows

/-! # Installing one common-prefix controller layer (scoped and bounded) -/

@[expose] public section

namespace VaughtConjecture.Knight.SourcePrefixLayer
open Transform Value ExtOrd SourcePrefixRows

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}

abbrev Controller (D : CellScheme A) (k : ℕ) := {c : Cell D // D.cell c = (A, k)}



end VaughtConjecture.Knight.SourcePrefixLayer

namespace VaughtConjecture.Knight.ScopedSourcePrefixLayer
open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer
noncomputable section

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}

theorem respects_below_of_lower (sem : Semantics D) (J : Finset ι × ℕ)
    (p : Cell D → ExtOrd)
    (hl : ∀ c : D.below J, RespectsSemanticsBelow sem (D.cell c.1) (fun d => p d.1)) :
    RespectsSemanticsBelow sem J (fun d => p d.1) where
  orderly d := (hl d).orderly ⟨d.1, GradedLe.refl _⟩
  locality c := (hl c).locality ⟨c.1, GradedLe.refl _⟩
  availability c t hs hg := by
    obtain ⟨w, hw, hle⟩ := (hl t).availability ⟨c.1, hs, hg.le⟩ ⟨t.1, GradedLe.refl _⟩ hs hg
    exact ⟨⟨w.1, w.2.trans t.2⟩, hw, hle⟩

structure Data (D : CellScheme A) (k : ℕ) (X : Type*) where
  base : Semantics D
  separated : ∀ c : Cell D, D.cell c ≠ (A, k) → ¬ GradedLe (A, k) (D.cell c)
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis k h
  boundary : Controller D k → X → ExtOrd
  lower : Controller D k → Cell D → ExtOrd
  lower_bound : ∀ q d, D.grade d ≤ k → D.cell d ≠ (A, k) → lower q d ≤ ceiling
  lower_lawful : ∀ q c, D.grade c ≤ k → D.cell c ≠ (A, k) →
    RespectsSemanticsBelow base (D.cell c) (fun d => lower q d.1)
  grid_agreement : ∀ p q h, h ∈ grid → Agree (boundary p) (boundary q) h →
    ∀ d, D.grade d ≤ k → D.cell d ≠ (A, k) → min (lower p d) h = min (lower q d) h

namespace Data
variable (F : Data D k X)

include F in
theorem below_old {c : Cell D} (hc : D.cell c ≠ (A, k)) (d : D.below (D.cell c)) :
    D.cell d.1 ≠ (A, k) := fun hd => F.separated c hc (hd ▸ d.2)

def profile (q : Controller D k) (d : Cell D) : ExtOrd :=
  if hd : D.cell d = (A, k) then cut F.grid (F.boundary q) (F.boundary ⟨d, hd⟩)
  else F.lower q d

theorem profile_old (q : Controller D k) {d : Cell D} (hd : D.cell d ≠ (A, k)) :
    F.profile q d = F.lower q d := by simp only [profile, hd, ↓reduceDIte]

theorem profile_new (q p : Controller D k) :
    F.profile q p.1 = cut F.grid (F.boundary q) (F.boundary p) := by
  simp only [profile, p.2, ↓reduceDIte]

theorem profile_diagonal (q : Controller D k) : F.profile q q.1 = F.ceiling := by
  rw [F.profile_new]; exact cut_refl F.ceiling_mem F.grid_bound _

theorem profile_bound (q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    F.profile q d ≤ F.ceiling := by
  by_cases he : D.cell d = (A, k)
  · rw [show d = (⟨d, he⟩ : Controller D k).1 from rfl, F.profile_new]
    exact cut_le F.grid_bound _ _
  · rw [F.profile_old q he]; exact F.lower_bound q d hd he

theorem profile_visible (q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    SelfVis (D.grade d) (F.profile q d) := by
  by_cases he : D.cell d = (A, k)
  · rw [show D.grade d = k from congrArg Prod.snd he,
      show d = (⟨d, he⟩ : Controller D k).1 from rfl, F.profile_new]
    exact F.grid_visible _ (cut_mem F.bot_mem _ _)
  · rw [F.profile_old q he]
    exact ((F.lower_lawful q d hd he).orderly ⟨d, GradedLe.refl _⟩).symm

theorem profile_agreement (p q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    min (F.profile p d) (cut F.grid (F.boundary p) (F.boundary q)) =
      min (F.profile q d) (cut F.grid (F.boundary p) (F.boundary q)) := by
  by_cases he : D.cell d = (A, k)
  · rw [show d = (⟨d, he⟩ : Controller D k).1 from rfl, F.profile_new, F.profile_new]
    exact cross_agreement F.bot_mem _ _ _
  · rw [F.profile_old p he, F.profile_old q he]
    exact F.grid_agreement p q _ (cut_mem F.bot_mem _ _) (agree_cut F.bot_mem _ _) d hd he

theorem profile_prefix {p q : Controller D k} {h : ExtOrd}
    (hh : h ∈ F.grid) (hpq : Agree (F.boundary p) (F.boundary q) h) :
    Agree (fun d : D.below (A, k) => F.profile p d.1)
      (fun d : D.below (A, k) => F.profile q d.1) h :=
  (show Agree (fun d : D.below (A, k) => F.profile p d.1)
      (fun d : D.below (A, k) => F.profile q d.1)
      (cut F.grid (F.boundary p) (F.boundary q)) from
    fun d => F.profile_agreement p q d.1 d.2.2).mono (le_cut hh hpq)

def rows : Semantics D where
  E c d := if hc : D.cell c = (A, k) then F.profile ⟨c, hc⟩ d.1 else F.base.E c d
  orderly c d := by
    dsimp only
    split_ifs with hc
    · exact (F.profile_visible ⟨c, hc⟩ d.1
        (by simpa only [CellScheme.grade, hc] using d.2.2)).symm
    · exact F.base.orderly c d

theorem row_old {c : Cell D} (hc : D.cell c ≠ (A, k)) : F.rows.E c = F.base.E c := by
  funext d; simp only [rows, hc, ↓reduceDIte]

theorem row_new (q : Controller D k) (d : D.below (D.cell q.1)) :
    F.rows.E q.1 d = F.profile q d.1 := by simp only [rows, q.2, ↓reduceDIte]

theorem old_respects_iff {c : Cell D} (hc : D.cell c ≠ (A, k))
    {r : D.below (D.cell c) → ExtOrd} :
    RespectsSemanticsBelow F.rows (D.cell c) r ↔
      RespectsSemanticsBelow F.base (D.cell c) r := by
  constructor <;> intro hr <;> refine ⟨hr.orderly, ?_, hr.availability⟩
  · intro d; simpa only [F.row_old (F.below_old hc d)] using hr.locality d
  · intro d; rw [F.row_old (F.below_old hc d)]; exact hr.locality d

theorem new_locality (q p : Controller D k) :
    TransformsTo (fun d : D.below (D.cell p.1) => D.grade d.1)
      (F.rows.E p.1) (fun d => min (F.profile q d.1) (F.profile q p.1)) := by
  have hb (d : D.below (D.cell p.1)) : D.grade d.1 ≤ k := by
    simpa only [CellScheme.grade, p.2] using d.2.2
  have ht := (TransformsTo.refl
    (grade := fun d : D.below (D.cell p.1) => D.grade d.1) (F.rows.E p.1)).cap
    hb (F.grid_visible _ (cut_mem F.bot_mem (F.boundary q) (F.boundary p)))
  have he : (fun d : D.below (D.cell p.1) =>
      min (F.rows.E p.1 d) (cut F.grid (F.boundary q) (F.boundary p))) =
      (fun d => min (F.profile q d.1) (F.profile q p.1)) := by
    funext d; rw [F.row_new, F.profile_new]; exact (F.profile_agreement q p d.1 (hb d)).symm
  rwa [he] at ht

theorem profile_respects (q : Controller D k) :
    RespectsSemanticsBelow F.rows (A, k) (fun d => F.profile q d.1) where
  orderly d := (F.profile_visible q d.1 d.2.2).symm
  locality c := by
    by_cases hc : D.cell c.1 = (A, k)
    · exact F.new_locality q ⟨c.1, hc⟩
    · have ht := (F.lower_lawful q c.1 c.2.2 hc).locality ⟨c.1, GradedLe.refl _⟩
      simpa only [F.row_old hc, F.profile_old q hc,
        F.profile_old q (F.below_old hc _), CellScheme.below.incl] using ht
  availability c t hs hg := by
    by_cases ht : D.cell t.1 = (A, k)
    · refine ⟨⟨q.1, by rw [q.2]; exact GradedLe.refl _⟩, q.2.trans ht.symm, ?_⟩
      rw [F.profile_diagonal]; exact F.profile_bound q c.1 c.2.2
    · have hc : GradedLe (D.cell c.1) (D.cell t.1) := ⟨hs, hg.le⟩
      obtain ⟨w, hw, hle⟩ := (F.lower_lawful q t.1 t.2.2 ht).availability
        ⟨c.1, hc⟩ ⟨t.1, GradedLe.refl _⟩ hs hg
      refine ⟨⟨w.1, w.2.trans t.2⟩, hw, ?_⟩
      simpa only [F.profile_old q (F.below_old ht ⟨c.1, hc⟩),
        F.profile_old q (F.below_old ht w)] using hle

theorem decoded_respects (q : Controller D k) {K : ℕ} (hkK : k ≤ K)
    {ν : ExtOrd → ExtOrd} (hν : Witness (gTop K) ν)
    (hproper : ∀ c : D.below (A, k), D.scope c.1 ≠ A →
      RespectsSemanticsBelow F.base (D.cell c.1) (fun d => ν (F.lower q d.1)))
    (hshort : ∀ c : D.below (A, k), D.scope c.1 = A → ∀ d : D.below (D.cell c.1),
      SharpWitnessComposition.Short (D.grade c.1) (F.rows.E c.1 d)) :
    RespectsSemanticsBelow F.rows (A, k) (fun d => ν (F.profile q d.1)) where
  orderly d := by
    have h := hν.clause5 (F.profile q d.1) (D.grade d.1)
      (by rw [gTop_of_le (show D.grade d.1 ≤ K from d.2.2.trans hkK)]; exact le_top)
      (D.grade d.1) le_rfl
    rwa [F.profile_visible q d.1 d.2.2] at h
  locality c := by
    by_cases hc : D.scope c.1 = A
    · exact SharpWitnessComposition.map_capped_locality
        (grade := fun d : D.below (D.cell c.1) => D.grade d.1)
        (c := (⟨c.1, GradedLe.refl _⟩ : D.below (D.cell c.1)))
        (p := fun d : D.below (D.cell c.1) => F.profile q d.1) (fun d => d.2.2)
        (c.2.2.trans hkK) (hshort c hc) (F.profile_visible q c.1 c.2.2)
        ((F.profile_respects q).locality c) hν
    · have hc' : D.cell c.1 ≠ (A, k) := fun he => hc (congrArg Prod.fst he)
      have ht := (hproper c hc).locality ⟨c.1, GradedLe.refl _⟩
      simpa only [F.row_old hc', F.profile_old q hc',
        F.profile_old q (F.below_old hc' _), CellScheme.below.incl] using ht
  availability c t hs hg := by
    obtain ⟨w, hw, hle⟩ := (F.profile_respects q).availability c t hs hg
    exact ⟨w, hw, hν.mono hle⟩

theorem consistent (hbase : ∀ c : Cell D, D.cell c ≠ (A, k) →
    RespectsSemanticsBelow F.base (D.cell c) (F.base.E c)) : F.rows.IsConsistent := by
  intro c
  by_cases hc : D.cell c = (A, k)
  · let q : Controller D k := ⟨c, hc⟩
    have hp := F.profile_respects q
    have he : F.rows.E q.1 = fun d => F.profile q d.1 := funext (F.row_new q)
    change RespectsSemanticsBelow F.rows (D.cell q.1) (F.rows.E q.1)
    refine ⟨F.rows.orderly c, ?_, ?_⟩
    · intro d
      simpa only [he, CellScheme.below.incl] using
        hp.locality ⟨d.1, by simpa only [q.2] using d.2⟩
    · intro d t hs hg
      obtain ⟨w, hw, hle⟩ := hp.availability
        ⟨d.1, by simpa only [q.2] using d.2⟩ ⟨t.1, by simpa only [q.2] using t.2⟩ hs hg
      exact ⟨⟨w.1, by rw [hw]; exact t.2⟩, hw, by simpa only [he] using hle⟩
  · rw [F.row_old hc]
    exact (F.old_respects_iff hc).mpr (hbase c hc)

end Data
end
end VaughtConjecture.Knight.ScopedSourcePrefixLayer

namespace VaughtConjecture.Knight.SourcePrefixLayer
open Transform Value ExtOrd SourcePrefixRows

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}

structure Data (D : CellScheme A) (k : ℕ) (X : Type*) where
  base : Semantics D
  max_grade : ∀ d : Cell D, D.grade d ≤ k
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis k h
  boundary : Controller D k → X → ExtOrd
  lower : Controller D k → Cell D → ExtOrd
  lower_bound : ∀ q d, D.cell d ≠ (A, k) → lower q d ≤ ceiling
  lower_lawful : ∀ q c, D.cell c ≠ (A, k) →
    RespectsSemanticsBelow base (D.cell c) (fun d => lower q d.1)
  grid_agreement : ∀ p q h, h ∈ grid → Agree (boundary p) (boundary q) h →
    ∀ d, D.cell d ≠ (A, k) → min (lower p d) h = min (lower q d) h

namespace Data
variable (F : Data D k X)

@[reducible] def toScoped : ScopedSourcePrefixLayer.Data D k X where
  base := F.base
  separated c hc h := hc (Prod.ext
    (Finset.Subset.antisymm (D.isPlan.subset_of_mem (D.scope_mem_plan c)) h.1)
    (le_antisymm (F.max_grade c) h.2))
  grid := F.grid
  bot_mem := F.bot_mem
  ceiling := F.ceiling
  ceiling_mem := F.ceiling_mem
  grid_bound := F.grid_bound
  grid_visible := F.grid_visible
  boundary := F.boundary
  lower := F.lower
  lower_bound q d _ hd := F.lower_bound q d hd
  lower_lawful q c _ hc := F.lower_lawful q c hc
  grid_agreement p q h hh hag d _ hd := F.grid_agreement p q h hh hag d hd

private def all (d : Cell D) : D.below (A, k) :=
  ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), F.max_grade d⟩

@[reducible] noncomputable def profile (q : Controller D k) (d : Cell D) : ExtOrd :=
  F.toScoped.profile q d

theorem profile_old (q : Controller D k) {d : Cell D} (hd : D.cell d ≠ (A, k)) :
    F.profile q d = F.lower q d := F.toScoped.profile_old q hd

theorem profile_new (q p : Controller D k) :
    F.profile q p.1 = cut F.grid (F.boundary q) (F.boundary p) := F.toScoped.profile_new q p



theorem profile_prefix {p q : Controller D k} {h : ExtOrd}
    (hh : h ∈ F.grid) (hpq : Agree (F.boundary p) (F.boundary q) h) :
    Agree (F.profile p) (F.profile q) h :=
  fun d => F.toScoped.profile_prefix hh hpq (F.all d)

theorem profile_short
    (hgrid : ∀ h ∈ F.grid, SharpWitnessComposition.Short k h)
    (hlower : ∀ q d, D.cell d ≠ (A, k) →
      SharpWitnessComposition.Short k (F.lower q d)) (q : Controller D k) :
    ∀ d, SharpWitnessComposition.Short k (F.profile q d) := by
  intro d
  by_cases hd : D.cell d = (A, k)
  · rw [show d = (⟨d, hd⟩ : Controller D k).1 from rfl, F.profile_new]
    exact hgrid _ (cut_mem F.bot_mem _ _)
  · rw [F.profile_old q hd]; exact hlower q d hd

@[reducible] noncomputable def rows : Semantics D := F.toScoped.rows

theorem row_old {c : Cell D} (hc : D.cell c ≠ (A, k)) : F.rows.E c = F.base.E c :=
  F.toScoped.row_old hc

theorem row_new (q : Controller D k) (d : D.below (D.cell q.1)) :
    F.rows.E q.1 d = F.profile q d.1 := F.toScoped.row_new q d

theorem full_source_short
    (hgrid : ∀ h ∈ F.grid, SharpWitnessComposition.Short k h)
    (hlower : ∀ q d, D.cell d ≠ (A, k) →
      SharpWitnessComposition.Short k (F.lower q d))
    (hbase : ∀ c : Cell D, D.scope c = A → D.cell c ≠ (A, k) →
      ∀ d : D.below (D.cell c), SharpWitnessComposition.Short (D.grade c) (F.base.E c d)) :
    ∀ c : Cell D, D.scope c = A → ∀ d : D.below (D.cell c),
      SharpWitnessComposition.Short (D.grade c) (F.rows.E c d) := by
  intro c hs d
  by_cases hc : D.cell c = (A, k)
  · rw [F.row_new ⟨c, hc⟩ d, show D.grade c = k from congrArg Prod.snd hc]
    exact F.profile_short hgrid hlower ⟨c, hc⟩ d.1
  · rw [F.row_old hc]; exact hbase c hs hc d



theorem profile_respects (q : Controller D k) : RespectsSemantics F.rows (F.profile q) :=
  (F.toScoped.profile_respects q).toRespects (fun d => (F.all d).2)

theorem consistent
    (hbase : ∀ c : Cell D, D.cell c ≠ (A, k) →
      RespectsSemanticsBelow F.base (D.cell c) (F.base.E c)) : F.rows.IsConsistent :=
  F.toScoped.consistent hbase

theorem decoded_respects (q : Controller D k) {K : ℕ} (hkK : k ≤ K)
    {ν : ExtOrd → ExtOrd} (hν : Witness (gTop K) ν)
    (hproper : ∀ c : Cell D, D.scope c ≠ A →
      RespectsSemanticsBelow F.base (D.cell c) (fun d => ν (F.lower q d.1)))
    (hshort : ∀ c : Cell D, D.scope c = A → ∀ d : D.below (D.cell c),
      SharpWitnessComposition.Short (D.grade c) (F.rows.E c d)) :
    RespectsSemantics F.rows (fun d => ν (F.profile q d)) :=
  (F.toScoped.decoded_respects q hkK hν (fun c hc => hproper c.1 hc)
    (fun c hc => hshort c.1 hc)).toRespects (fun d => (F.all d).2)

end Data
end VaughtConjecture.Knight.SourcePrefixLayer
