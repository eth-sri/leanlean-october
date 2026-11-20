/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopeReplicationCarrier
public import VaughtConjecture.Knight.ExactSemanticFace

@[expose] public section

namespace VaughtConjecture.Knight.ScopeReplicationSemantics

open AmalgamationPlan Transform Value ExtOrd ScopeReplicationCarrier

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (S : Frame A)

local notation "D" => S.base
local notation "B" => S.left
local notation "C" => S.right
local notation "sem" => S.sem

def rows : Semantics (scheme S) where
  E c d := (sem).E (erase S c) (belowErase S c d)
  orderly c d := by
    change (sem).E _ _ = extVisibilityReplace ((sem).E _ _)
      ((scheme S).grade d.1) ((scheme S).grade d.1)
    rw [← erase_grade]
    apply (sem).orderly

/-- Every old source column is literal, even when the owner's new lower domain
contains additional copies. -/
theorem inherited_row (c : Cell D) (d : (D).below ((D).cell c)) :
    (rows S).E (old S c)
      ⟨old S d.1, by rw [old_index, old_index]; grind⟩ = (sem).E c d := by
  change (sem).E _ _ = _
  exact (sem).E_congr (erase_old S c) (erase_old S d.1)

/-- Lawful pullback to an actual lower domain. Its erased coordinates must lie
in the supplied original domain; no completeness or extension is assumed. -/
theorem duplicateBelow_respects {J K : Finset ι × ℕ}
    (hdom : ∀ d : (scheme S).below J, GradedLe ((D).cell (erase S d.1)) K)
    {p : (D).below K → ExtOrd} (hp : RespectsSemanticsBelow sem K p) :
    RespectsSemanticsBelow (rows S) J
      (fun d => p ⟨erase S d.1, hdom d⟩) where
  orderly d := by
    change p _ = extVisibilityReplace (p _) ((scheme S).grade d.1)
      ((scheme S).grade d.1)
    rw [← erase_grade]
    exact hp.orderly _
  locality c := by
    have ht := (hp.locality ⟨erase S c.1, hdom c⟩).reindex
      (belowErase S c.1)
    exact transformsTo_congr (funext fun d => erase_grade S d.1) rfl rfl ht
  availability c t hs hg := by
    have he := erase_le S (d := c.1) (c := t.1) ⟨hs, hg.le⟩
    have heg : (D).grade (erase S c.1) = (D).grade (erase S t.1) := by
      rw [erase_grade, erase_grade]; exact hg
    obtain ⟨w, hw, hle⟩ := hp.availability
      ⟨erase S c.1, hdom c⟩ ⟨erase S t.1, hdom t⟩ he.1 heg
    obtain ⟨z, hz, hez⟩ := exists_at_index S t.1 w.1 hw
    refine ⟨⟨z, hz ▸ t.2⟩, hz, ?_⟩
    have hsub : (⟨erase S z, by grind⟩ : (D).below K) = w :=
      Subtype.ext hez
    grind

/-- Consistency of the installed replicated rows is constructed, independently
of any lifting theorem. -/
theorem consistent (hc : (sem).IsConsistent) : (rows S).IsConsistent := by solve_by_elim [duplicateBelow_respects, erase]

/-- Restriction to the retained single-copy occurrences is lawful. Availability
witnesses at old indices cannot be newly appended copies. -/
theorem restrict_respects {J : Finset ι × ℕ}
    {p : (scheme S).below J → ExtOrd}
    (hp : RespectsSemanticsBelow (rows S) J p) :
    RespectsSemanticsBelow sem J (p ∘ oldBelow S J) where
  orderly d := by
    simpa only [Function.comp_apply, CellScheme.grade, oldBelow, old_index]
      using hp.orderly (oldBelow S J d)
  locality c := by
    have ht := (hp.locality (oldBelow S J c)).reindex
      (fun d : (D).below ((D).cell c.1) =>
        (⟨old S d.1, by rw [old_index, old_index]; grind⟩ :
          (scheme S).below ((scheme S).cell (old S c.1))))
    exact transformsTo_congr
      (funext fun d => congrArg Prod.snd (old_index S d.1))
      (funext fun d => inherited_row S c.1 d) rfl ht
  availability c t hs hg := by
    obtain ⟨w, hw, hle⟩ := hp.availability (oldBelow S J c) (oldBelow S J t)
      (by simpa only [CellScheme.scope, oldBelow, old_index] using hs)
      (by simpa only [CellScheme.grade, oldBelow, old_index] using hg)
    obtain ⟨z, hz⟩ := old_index_exhaustive S t.1 w.1
      (hw.trans (old_index S t.1))
    have hzJ : GradedLe ((D).cell z) J := by rw [← old_index S z, hz]; grind
    refine ⟨⟨z, hzJ⟩, ?_, ?_⟩
    · exact (old_index S z).symm.trans (hz ▸ hw.trans (old_index S t.1))
    · have he : oldBelow S J ⟨z, hzJ⟩ = w := Subtype.ext hz
      change p (oldBelow S J c) ≤ p (oldBelow S J ⟨z, hzJ⟩)
      rw [he]
      exact hle

/-- An arbitrary lawful section assigns the same value to nested copies of
one prototype. This uses actual locality and availability, not a renderer or
any synchronization/admission hypothesis. -/
theorem copy_eq {J : Finset ι × ℕ} {p : (scheme S).below J → ExtOrd}
    (hp : RespectsSemanticsBelow (rows S) J p)
    (a b : (scheme S).below J)
    (hs : (scheme S).scope a.1 ⊆ (scheme S).scope b.1)
    (he : erase S a.1 = erase S b.1) : p a = p b := by
  have hg : (scheme S).grade a.1 = (scheme S).grade b.1 :=
    (erase_grade S a.1).symm.trans
      ((congrArg (D).grade he).trans (erase_grade S b.1))
  have hw : ∃ w : (scheme S).below J,
      (scheme S).cell w.1 = (scheme S).cell b.1 ∧ p a ≤ p w ∧ p b ≤ p w := by
    rcases le_total (p a) (p b) with h | h
    · grind
    · obtain ⟨w, hi, hv⟩ := hp.availability a b hs hg
      grind
  obtain ⟨w, hi, ha, hb⟩ := hw
  let da : (scheme S).below ((scheme S).cell w.1) :=
    ⟨a.1, hi ▸ (show GradedLe ((scheme S).cell a.1) ((scheme S).cell b.1)
      from ⟨hs, hg.le⟩)⟩
  let db : (scheme S).below ((scheme S).cell w.1) :=
    ⟨b.1, hi ▸ GradedLe.refl _⟩
  have hrow : (rows S).E w.1 da = (rows S).E w.1 db :=
    (sem).E_congr rfl he
  obtain ⟨g, σ, _, _, _, _, _, hread⟩ := hp.locality w
  have hval : min (p a) (p w) = min (p b) (p w) := by
    calc
      _ = min (σ ((rows S).E w.1 da))
          (g ((scheme S).grade a.1)) := hread da
      _ = min (σ ((rows S).E w.1 db))
          (g ((scheme S).grade b.1)) := by lia
      _ = _ := (hread db).symm
  grind

/-- Agreement on a smaller mixed cutoff determines every auxiliary value, even
if its scope is incomparable to the smaller cutoff. Compare both occurrences
with the same target-scope replica. -/
theorem auxiliary_eq {U V : Finset ι} {j : ℕ}
    (hU : U ∈ (D).plan) (hmU : U = A ∨ Mixed B C U) (hjU : j ≤ U.card)
    (hV : V ∈ (D).plan) (hmV : V = A ∨ Mixed B C V) (hjV : j ≤ V.card)
    (hUV : U ⊆ V) {p q : (scheme S).below (V, j) → ExtOrd}
    (hp : RespectsSemanticsBelow (rows S) (V, j) p)
    (hq : RespectsSemanticsBelow (rows S) (V, j) q)
    (hag : ∀ d : (scheme S).below (U, j),
      p (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) d) =
      q (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) d))
    (z : (scheme S).below (V, j)) (hz : (D).scope (erase S z.1) = A) : p z = q z := by
  have hg := (erase_grade S z.1).le.trans z.2.2
  let u := replica S hU hmU hjU _ hz hg
  let v := replica S hV hmV hjV _ hz hg
  let u' := CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) u
  have hi : (scheme S).scope v.1 = V := congrArg Prod.fst (replica_index S hV hmV hjV _ hz hg)
  have hu : (scheme S).scope u'.1 = U := congrArg Prod.fst (replica_index S hU hmU hjU _ hz hg)
  have he := erase_replica S hV hmV hjV _ hz hg
  have eq {r} (hr : RespectsSemanticsBelow (rows S) (V, j) r) : r z = r u' :=
    (copy_eq S hr z v (hi.symm ▸ z.2.1) he.symm).trans
      (copy_eq S hr u' v
        (by rwa [hu, hi])
        ((erase_replica S hU hmU hjU _ hz hg).trans he.symm)).symm
  exact (eq hp).trans ((hag u).trans (eq hq).symm)

/-- Any literal original face contained in either side remains occurrence-exact. -/
def face {T : Finset ι} {E : CellScheme T} {semE : Semantics E}
    (F : ExactSemanticFace semE sem) (hT : T ⊆ B ∨ T ⊆ C) :
    ExactSemanticFace semE (rows S) where
  map := F.map.trans ⟨old S, (old_order S).injective⟩
  index d := (old_index S (F.map d)).trans (F.index d)
  exhaustive z hz := by
    rcases cases S z with ⟨d, rfl⟩ | ⟨p, rfl⟩
    · obtain ⟨e, he⟩ := F.exhaustive d (by
        simpa only [CellScheme.scope, old_index] using hz)
      exact ⟨e, congrArg (old S) he⟩
    · have hs : p.1.1.1 ⊆ T := by
        simpa only [CellScheme.scope, added_index] using hz
      exact (hT.elim (fun h => p.2.2.1.1 (hs.trans h))
        (fun h => p.2.2.1.2 (hs.trans h))).elim
  row c d := (inherited_row S (F.map c)
    ⟨F.map d.1, by rw [F.index, F.index]; grind⟩).trans (F.row c d)

end

end VaughtConjecture.Knight.ScopeReplicationSemantics
