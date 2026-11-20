/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedLocality

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherMixed

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources

open GrowthPaddedContract GrowthPaddedIteration

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)

local notation "P" => G.tower

local notation "D" => carrier G

local notation "Rows" => rows G

variable {G} (W : Cut G)
  {p : CellScheme.below (carrier G) W.index → ExtOrd}

theorem native_orderly (hp : RespectsSemanticsBelow Rows W.index p)
    (d : (P).carrier.below (A, W.grade)) :
    nativeValue W p d.1 =
      extVisibilityReplace (nativeValue W p d.1)
        ((P).carrier.grade d.1) ((P).carrier.grade d.1) := by
  rcases original_or_full G d.1 with ⟨e, he⟩ | hd
  · have hh : GradedLe (G.I.boundary.cell e) (A, W.grade) :=
      (original_index G e) ▸ (he ▸ d.2)
    have hv := (boundary_projection W hp).orderly ⟨e, hh⟩
    simpa only [he, native_original, boundaryValue, CellScheme.grade, original_index] using hv
  · rw [native_full W p d.1 hd d.2.2]
    have hv := hp.orderly (place W d.1 hd d.2.2)
    have hi := congrArg Prod.snd (place_index W d.1 hd d.2.2)
    change (D).grade (place W d.1 hd d.2.2).1 =
      (P).carrier.grade d.1 at hi
    change _ = extVisibilityReplace _
      ((D).grade (place W d.1 hd d.2.2).1)
      ((D).grade (place W d.1 hd d.2.2).1) at hv
    rwa [hi] at hv

theorem native_le_gradeMax (p : (D).below W.index → ExtOrd)
    (d : Cell (P).carrier) (hd : (P).carrier.grade d ≤ W.grade) :
    nativeValue W p d ≤
      gradeMax W p ((P).carrier.grade d) := by
  rcases original_or_full G d with ⟨e, rfl⟩ | hf
  · have he : (P).carrier.grade (original G e) = G.I.boundary.grade e :=
      congrArg Prod.snd (original_index G e)
    rw [he] at hd ⊢
    rw [native_original, boundaryValue, height]
    split_ifs with he1
    · rw [min_top_right]
      have heq : G.I.boundary.grade e = 1 := le_antisymm he1 (G.I.boundary.grade_pos e)
      rw [heq]
      apply Finset.sup_le
      intro a _
      exact le_gradeMax W p 1 _
        (congrArg Prod.snd (ladderAt_index W _))
    · exact min_le_right _ _
  · rw [native_full W p d hf hd]
    have hi := congrArg Prod.snd (place_index W d hf hd)
    exact le_gradeMax W p _ _ hi

theorem native_availability (hp : RespectsSemanticsBelow Rows W.index p)
    (c v : (P).carrier.below (A, W.grade))
    (hs : (P).carrier.scope c.1 ⊆ (P).carrier.scope v.1)
    (hg : (P).carrier.grade c.1 = (P).carrier.grade v.1) :
    ∃ w : (P).carrier.below (A, W.grade), (P).carrier.cell w.1 = (P).carrier.cell v.1 ∧
      nativeValue W p c.1 ≤
        nativeValue W p w.1 := by
  rcases original_or_full G v.1 with ⟨e, he⟩ | hv
  · have hev : (P).carrier.cell v.1 = G.I.boundary.cell e :=
      he ▸ original_index G e
    have hem : GradedLe (G.I.boundary.cell e) (A, W.grade) := hev ▸ v.2
    rcases original_or_full G c.1 with ⟨d, hd⟩ | hc
    · have hdc : (P).carrier.cell c.1 = G.I.boundary.cell d :=
        hd ▸ original_index G d
      have hdm : GradedLe (G.I.boundary.cell d) (A, W.grade) := hdc ▸ c.2
      have hb := boundary_projection W hp
      obtain ⟨w, hw, hle⟩ := hb.availability
        ⟨d, hdm⟩ ⟨e, hem⟩
        ((congrArg Prod.fst hdc).symm.le.trans (hs.trans (congrArg Prod.fst hev).le))
        ((congrArg Prod.snd hdc).symm.trans (hg.trans (congrArg Prod.snd hev)))
      refine ⟨⟨original G w.1,
        (original_index G w.1) ▸ w.2⟩,
        (original_index G w.1).trans (hw.trans hev.symm), ?_⟩
      simpa [hd, native_original, boundaryValue] using hle
    · exact (GrowthOrderedBase.proper G.I G.leftProper G.rightProper e (le_antisymm
        (G.I.boundary.scope_subset e)
        (hc.symm.le.trans (hs.trans (congrArg Prod.fst hev).le)))).elim
  · obtain ⟨w, hw, hwg, hmax⟩ := exists_maximal_owner W
      hp ((P).carrier.grade v.1) ((P).carrier.grade_pos v.1) v.2.2
    refine ⟨⟨w, hw.le, hwg.le.trans v.2.2⟩, Prod.ext (hw.trans hv.symm) hwg, ?_⟩
    rw [native_full W p w hw (hwg.le.trans v.2.2),
      hmax, ← hg]
    exact native_le_gradeMax W p c.1 c.2.2

/-- Every locality and availability obligation of the constructed native
section is proved on its actual lower domain. -/
theorem native_lawful (hp : RespectsSemanticsBelow Rows W.index p) :
    RespectsSemanticsBelow (P).rows (A, W.grade)
      (fun d => nativeValue W p d.1) where
  orderly := native_orderly W hp
  locality c := by
    by_cases hc1 : (P).carrier.grade c.1 ≤ 1
    · exact (native_one_lawful W hp).locality
        ⟨c.1, c.2.1, hc1⟩
    rcases c with ⟨c, hcut⟩
    change ¬ (P).carrier.grade c ≤ 1 at hc1
    rcases original_or_full G c with ⟨d, hd⟩ | hc
    · have hgd : G.I.boundary.grade d ≤ W.grade :=
        (congrArg Prod.snd (original_index G d)).symm.le.trans
          ((congrArg (P).carrier.grade hd).symm.le.trans hcut.2)
      subst c
      exact (original_respects W hp d hgd).locality
        ⟨original G d, GradedLe.refl _⟩
    · exact higher_locality W hp c hc hcut.2 (by omega)
  availability := native_availability W hp

theorem lawful (hp : RespectsSemanticsBelow Rows W.index p) (V : Finset ι) :
    RespectsSemanticsBelow Rows (V, W.grade) (value W p) :=
  ScopeReplicationSemantics.duplicateBelow_respects (GrowthReplicatedRows.frame P)  (J := (V, W.grade)) (K := (A, W.grade))
    (fun d => ⟨(P).carrier.isPlan.subset_of_mem ((P).carrier.scope_mem_plan _),
      (ScopeReplicationCarrier.erase_grade (GrowthReplicatedRows.frame P) d.1).le.trans d.2.2⟩)
    (native_lawful W hp)

theorem lawfulExtension (V : Finset ι) (hUV : W.scope ⊆ V) :
    ExtensionInjectivity.LawfulExtension Rows
      (show GradedLe W.index (V, W.grade) from ⟨hUV, le_rfl⟩) := by
  intro p hp
  exact ⟨value W p,
    lawful W hp V,
    literal W p hp hUV⟩

/-- At every installed cutoff on one fixed carrier, choose an extension before any cap or
ambient. Every individual auxiliary occurrence is included in the simultaneous receipts. -/
theorem allCapsExtension (V : Finset ι) (hV : V ∈ R)
    (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V) (hUV : W.scope ⊆ V) :
    ExtensionInjectivity.AllCapsExtension Rows
      (show GradedLe W.index (V, W.grade) from ⟨hUV, le_rfl⟩) := by
  apply ExtensionInjectivity.allCapsExtension_of_extension_injective
    (lawfulExtension W V hUV)
  intro r s hr hs hag z
  exact congrFun (eq_of_restriction W V hV hmV hUV
    hr hs hag) z

/-- All-cap mixed lifting on one fixed final carrier, at any installed
positive cutoff. Every target occurrence retains its own cap. -/
theorem cappedLift (V : Finset ι) (hV : V ∈ R)
    (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V) (hUV : W.scope ⊆ V) :
    CoatomBoundaryExtension.CappedLift Rows
      (show GradedLe W.index (V, W.grade) from ⟨hUV, le_rfl⟩) :=
  (allCapsExtension W V hV hmV hUV).cappedLift

end

end VaughtConjecture.Knight.GrowthHigherMixed
