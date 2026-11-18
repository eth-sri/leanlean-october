/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedNativeRows
public import VaughtConjecture.Knight.ExactSemanticFace
public import VaughtConjecture.Knight.CoatomBoundaryExtension

@[expose] public section

namespace VaughtConjecture.Knight

namespace ScopeReplicationCarrier
open AmalgamationPlan
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (D : CellScheme A) (B C : Finset ι)

def Mixed (U : Finset ι) : Prop := ¬ U ⊆ B ∧ ¬ U ⊆ C

abbrev Copy := {p : (↑D.plan) × Cell D //
  p.1.1 ≠ A ∧ Mixed B C p.1.1 ∧ D.scope p.2 = A ∧ D.grade p.2 ≤ p.1.1.card}

instance : Fintype (Copy D B C) := Fintype.ofFinite _

def scheme : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := D.card + Fintype.card (Copy D B C)
  cell := Fin.addCases D.cell fun i =>
    let p := (Fintype.equivFin (Copy D B C)).symm i
    (p.1.1.1, D.grade p.1.2)
  cell_mem := Fin.addCases (fun d => by simpa only [Fin.addCases_left] using D.cell_mem d)
    fun i => by
      simp only [Fin.addCases_right]
      let p := (Fintype.equivFin (Copy D B C)).symm i
      exact Plan.mem_gradedPlan.mpr ⟨p.1.1.2, D.grade_pos _, p.2.2.2.2⟩

def enumeration : (Cell D ⊕ Copy D B C) ≃ Cell (scheme D B C) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin (Copy D B C))).trans finSumFinEquiv

abbrev old (d : Cell D) : Cell (scheme D B C) := enumeration D B C (.inl d)
abbrev added (p : Copy D B C) : Cell (scheme D B C) := enumeration D B C (.inr p)

theorem old_index (d : Cell D) : (scheme D B C).cell (old D B C d) = D.cell d := by
  change (scheme D B C).cell (Fin.castAdd (Fintype.card (Copy D B C)) d) = D.cell d
  unfold scheme; simp only [Fin.addCases_left]

theorem added_index (p : Copy D B C) :
    (scheme D B C).cell (added D B C p) = (p.1.1.1, D.grade p.1.2) := by
  change (scheme D B C).cell (Fin.natAdd D.card (Fintype.equivFin (Copy D B C) p)) = _
  unfold scheme; simp only [Fin.addCases_right, Equiv.symm_apply_apply]

theorem old_order : StrictMono (old D B C) := Fin.strictMono_castAdd _

theorem cases (d : Cell (scheme D B C)) :
    (∃ c, d = old D B C c) ∨ ∃ p, d = added D B C p := by
  obtain ⟨x, rfl⟩ := (enumeration D B C).surjective d
  cases x with | inl c => exact Or.inl ⟨c, rfl⟩ | inr p => exact Or.inr ⟨p, rfl⟩

def erase (d : Cell (scheme D B C)) : Cell D :=
  match (enumeration D B C).symm d with
  | .inl c => c
  | .inr p => p.1.2

@[simp] theorem erase_old (d : Cell D) : erase D B C (old D B C d) = d := by
  simp only [erase, old, Equiv.symm_apply_apply]

@[simp] theorem erase_added (p : Copy D B C) : erase D B C (added D B C p) = p.1.2 := by
  simp only [erase, added, Equiv.symm_apply_apply]

theorem erase_grade (d : Cell (scheme D B C)) :
    D.grade (erase D B C d) = (scheme D B C).grade d := by
  rcases cases D B C d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]; exact (congrArg Prod.snd (old_index D B C c)).symm
  · rw [erase_added]; exact (congrArg Prod.snd (added_index D B C p)).symm

theorem erase_scope_of_ne (d : Cell (scheme D B C)) (h : D.scope (erase D B C d) ≠ A) :
    D.scope (erase D B C d) = (scheme D B C).scope d := by
  rcases cases D B C d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]; exact (congrArg Prod.fst (old_index D B C c)).symm
  · exact (h (by rw [erase_added]; exact p.2.2.2.1)).elim

theorem scope_le_erase (d : Cell (scheme D B C)) :
    (scheme D B C).scope d ⊆ D.scope (erase D B C d) := by
  rcases cases D B C d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]; exact (congrArg Prod.fst (old_index D B C c)).le
  · rw [erase_added, p.2.2.2.1]
    exact (scheme D B C).isPlan.subset_of_mem ((scheme D B C).scope_mem_plan _)

theorem full_or_mixed (d : Cell (scheme D B C)) (h : D.scope (erase D B C d) = A) :
    (scheme D B C).scope d = A ∨ Mixed B C ((scheme D B C).scope d) := by
  rcases cases D B C d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl ((congrArg Prod.fst (old_index D B C c)).trans
      (by simpa only [erase_old, CellScheme.scope] using h))
  · exact Or.inr (by simpa only [CellScheme.scope, added_index] using p.2.2.1)

variable (hcover : ∀ c : Cell D, D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)

include hcover in
theorem erase_le {d c : Cell (scheme D B C)}
    (h : GradedLe ((scheme D B C).cell d) ((scheme D B C).cell c)) :
    GradedLe (D.cell (erase D B C d)) (D.cell (erase D B C c)) := by
  refine ⟨?_, ?_⟩
  · change D.scope (erase D B C d) ⊆ D.scope (erase D B C c)
    by_cases hc : D.scope (erase D B C c) = A
    · rw [hc]; exact D.isPlan.subset_of_mem (D.scope_mem_plan _)
    · rw [erase_scope_of_ne D B C c hc]
      rcases cases D B C d with ⟨e, rfl⟩ | ⟨p, rfl⟩
      · simpa only [erase_old, CellScheme.scope, old_index] using h.1
      · have hs : p.1.1.1 ⊆ D.scope (erase D B C c) := by
          rw [erase_scope_of_ne D B C c hc]
          simpa only [CellScheme.scope, added_index] using h.1
        exact (hcover _ hc).elim (fun hb => (p.2.2.1.1 (hs.trans hb)).elim)
          fun hc' => (p.2.2.1.2 (hs.trans hc')).elim
  · change D.grade (erase D B C d) ≤ D.grade (erase D B C c)
    rw [erase_grade, erase_grade]; exact h.2

def belowErase (c : Cell (scheme D B C)) :
    (scheme D B C).below ((scheme D B C).cell c) → D.below (D.cell (erase D B C c)) :=
  fun d => ⟨erase D B C d.1, erase_le D B C hcover d.2⟩

include hcover in
theorem old_index_exhaustive (c : Cell D) (z : Cell (scheme D B C))
    (hz : (scheme D B C).cell z = D.cell c) : ∃ d, old D B C d = z := by
  rcases cases D B C z with ⟨d, rfl⟩ | ⟨p, rfl⟩
  · exact ⟨d, rfl⟩
  · have hs : p.1.1.1 = D.scope c :=
      (congrArg Prod.fst (added_index D B C p)).symm.trans (congrArg Prod.fst hz)
    by_cases hc : D.scope c = A
    · exact (p.2.1 (hs.trans hc)).elim
    · exact (hcover c hc).elim (fun hb => (p.2.2.1.1 (hs ▸ hb)).elim)
        fun hc' => (p.2.2.1.2 (hs ▸ hc')).elim

def oldBelow (J : Finset ι × ℕ) (d : D.below J) : (scheme D B C).below J :=
  ⟨old D B C d.1, by rw [old_index]; exact d.2⟩

def atScope (U : Finset ι) (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U)
    (c : Cell D) (hc : D.scope c = A) (hg : D.grade c ≤ U.card) : Cell (scheme D B C) := by
  classical
  exact if h : U = A then old D B C c else added D B C ⟨(⟨U, hU⟩, c), h, hm.resolve_left h, hc, hg⟩

theorem atScope_index (U : Finset ι) (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U)
    (c : Cell D) (hc : D.scope c = A) (hg : D.grade c ≤ U.card) :
    (scheme D B C).cell (atScope D B C U hU hm c hc hg) = (U, D.grade c) := by
  classical
  unfold atScope; split_ifs with h
  · exact (old_index D B C c).trans (Prod.ext (hc.trans h.symm) rfl)
  · exact added_index D B C _

theorem erase_atScope (U : Finset ι) (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U)
    (c : Cell D) (hc : D.scope c = A) (hg : D.grade c ≤ U.card) :
    erase D B C (atScope D B C U hU hm c hc hg) = c := by
  classical
  unfold atScope; split_ifs <;> simp only [erase_old, erase_added]

theorem exists_at_index (t : Cell (scheme D B C)) (w : Cell D)
    (hw : D.cell w = D.cell (erase D B C t)) :
    ∃ z : Cell (scheme D B C),
      (scheme D B C).cell z = (scheme D B C).cell t ∧ erase D B C z = w := by
  by_cases ht : D.scope (erase D B C t) = A
  · have hws : D.scope w = A := (congrArg Prod.fst hw).trans ht
    have hwg : D.grade w = (scheme D B C).grade t :=
      (congrArg Prod.snd hw).trans (erase_grade D B C t)
    exact ⟨atScope D B C ((scheme D B C).scope t) ((scheme D B C).scope_mem_plan t)
        (full_or_mixed D B C t ht) w hws (hwg ▸ (scheme D B C).grade_le_card_scope t),
      (atScope_index D B C _ _ _ _ _ _).trans (by rw [hwg]; rfl),
      erase_atScope D B C _ _ _ _ _ _⟩
  · exact ⟨old D B C w,
      (old_index D B C w).trans (hw.trans (Prod.ext (erase_scope_of_ne D B C t ht) (erase_grade D B C t))),
      erase_old D B C w⟩
end
end ScopeReplicationCarrier

namespace ScopeReplicationSemantics
open AmalgamationPlan Transform Value ExtOrd ScopeReplicationCarrier
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (B C : Finset ι)
  (hcover : ∀ c : Cell D, D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)
  (sem : Semantics D)

def rows : Semantics (scheme D B C) where
  E c d := sem.E (erase D B C c) (belowErase D B C hcover c d)
  orderly c d := by
    change sem.E _ _ = extVisibilityReplace (sem.E _ _)
      ((scheme D B C).grade d.1) ((scheme D B C).grade d.1)
    rw [← erase_grade]; exact sem.orderly _ _

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows D B C hcover sem).E (old D B C c)
      ⟨old D B C d.1, by rw [old_index, old_index]; exact d.2⟩ = sem.E c d :=
  sem.E_congr (erase_old D B C c) (erase_old D B C d.1)

theorem duplicateBelow_respects {J K : Finset ι × ℕ}
    (hdom : ∀ d : (scheme D B C).below J, GradedLe (D.cell (erase D B C d.1)) K)
    {p : D.below K → ExtOrd} (hp : RespectsSemanticsBelow sem K p) :
    RespectsSemanticsBelow (rows D B C hcover sem) J (fun d => p ⟨erase D B C d.1, hdom d⟩) where
  orderly d := by
    change p _ = extVisibilityReplace (p _) ((scheme D B C).grade d.1) ((scheme D B C).grade d.1)
    rw [← erase_grade]; exact hp.orderly _
  locality c := transformsTo_congr (funext fun d => erase_grade D B C d.1) rfl rfl
    ((hp.locality ⟨erase D B C c.1, hdom c⟩).reindex (belowErase D B C hcover c.1))
  availability c t hs hg := by
    have he := erase_le D B C hcover (d := c.1) (c := t.1) ⟨hs, hg.le⟩
    obtain ⟨w, hw, hle⟩ := hp.availability ⟨erase D B C c.1, hdom c⟩ ⟨erase D B C t.1, hdom t⟩
      he.1 (by rw [erase_grade, erase_grade]; exact hg)
    obtain ⟨z, hz, hez⟩ := exists_at_index D B C t.1 w.1 hw
    exact ⟨⟨z, hz ▸ t.2⟩, hz, by
      simpa only [show (⟨erase D B C z, hdom ⟨z, hz ▸ t.2⟩⟩ : D.below K) = w from Subtype.ext hez]
        using hle⟩

theorem consistent (hc : sem.IsConsistent) : (rows D B C hcover sem).IsConsistent :=
  fun c => duplicateBelow_respects D B C hcover sem (fun d => erase_le D B C hcover d.2)
    (hc (erase D B C c))

theorem restrict_respects {J : Finset ι × ℕ} {p : (scheme D B C).below J → ExtOrd}
    (hp : RespectsSemanticsBelow (rows D B C hcover sem) J p) :
    RespectsSemanticsBelow sem J (p ∘ oldBelow D B C J) where
  orderly d := by
    simpa only [Function.comp_apply, CellScheme.grade, oldBelow, old_index] using
      hp.orderly (oldBelow D B C J d)
  locality c := transformsTo_congr
    (funext fun d => congrArg Prod.snd (old_index D B C d.1))
    (funext fun d => inherited_row D B C hcover sem c.1 d) rfl
    ((hp.locality (oldBelow D B C J c)).reindex fun d : D.below (D.cell c.1) =>
      (⟨old D B C d.1, by rw [old_index, old_index]; exact d.2⟩ :
        (scheme D B C).below ((scheme D B C).cell (old D B C c.1))))
  availability c t hs hg := by
    obtain ⟨w, hw, hle⟩ := hp.availability (oldBelow D B C J c) (oldBelow D B C J t)
      (by simpa only [CellScheme.scope, oldBelow, old_index] using hs)
      (by simpa only [CellScheme.grade, oldBelow, old_index] using hg)
    obtain ⟨z, hz⟩ := old_index_exhaustive D B C hcover t.1 w.1 (hw.trans (old_index D B C t.1))
    have hzJ : GradedLe (D.cell z) J := by rw [← old_index D B C z, hz]; exact w.2
    refine ⟨⟨z, hzJ⟩, (old_index D B C z).symm.trans (hz ▸ hw.trans (old_index D B C t.1)), ?_⟩
    change p (oldBelow D B C J c) ≤ p (oldBelow D B C J ⟨z, hzJ⟩)
    rwa [show oldBelow D B C J ⟨z, hzJ⟩ = w from Subtype.ext hz]

theorem copy_eq {J : Finset ι × ℕ} {p : (scheme D B C).below J → ExtOrd}
    (hp : RespectsSemanticsBelow (rows D B C hcover sem) J p)
    (a b : (scheme D B C).below J)
    (hs : (scheme D B C).scope a.1 ⊆ (scheme D B C).scope b.1)
    (he : erase D B C a.1 = erase D B C b.1) : p a = p b := by
  have hg : (scheme D B C).grade a.1 = (scheme D B C).grade b.1 :=
    (erase_grade D B C a.1).symm.trans ((congrArg D.grade he).trans (erase_grade D B C b.1))
  have hw : ∃ w : (scheme D B C).below J,
      (scheme D B C).cell w.1 = (scheme D B C).cell b.1 ∧ p a ≤ p w ∧ p b ≤ p w := by
    rcases le_total (p a) (p b) with h | h
    · exact ⟨b, rfl, h, le_rfl⟩
    · obtain ⟨w, hi, hv⟩ := hp.availability a b hs hg
      exact ⟨w, hi, hv, h.trans hv⟩
  obtain ⟨w, hi, ha, hb⟩ := hw
  let da : (scheme D B C).below ((scheme D B C).cell w.1) :=
    ⟨a.1, hi ▸ (show GradedLe ((scheme D B C).cell a.1) ((scheme D B C).cell b.1) from ⟨hs, hg.le⟩)⟩
  let db : (scheme D B C).below ((scheme D B C).cell w.1) := ⟨b.1, hi ▸ GradedLe.refl _⟩
  have hrow : (rows D B C hcover sem).E w.1 da = (rows D B C hcover sem).E w.1 db :=
    sem.E_congr rfl he
  obtain ⟨g, σ, _, _, _, _, _, hread⟩ := hp.locality w
  have hval : min (p a) (p w) = min (p b) (p w) :=
    (hread da).trans ((by rw [hrow, hg] : min (σ ((rows D B C hcover sem).E w.1 da))
      (g ((scheme D B C).grade a.1)) = _).trans (hread db).symm)
  simpa only [min_eq_left ha, min_eq_left hb] using hval

def face {T : Finset ι} {E : CellScheme T} {semE : Semantics E}
    (F : ExactSemanticFace semE sem) (hT : T ⊆ B ∨ T ⊆ C) :
    ExactSemanticFace semE (rows D B C hcover sem) where
  map := F.map.trans ⟨old D B C, (old_order D B C).injective⟩
  index d := (old_index D B C (F.map d)).trans (F.index d)
  exhaustive z hz := by
    rcases cases D B C z with ⟨d, rfl⟩ | ⟨p, rfl⟩
    · obtain ⟨e, he⟩ := F.exhaustive d (by simpa only [CellScheme.scope, old_index] using hz)
      exact ⟨e, congrArg (old D B C) he⟩
    · have hs : p.1.1.1 ⊆ T := by simpa only [CellScheme.scope, added_index] using hz
      exact (hT.elim (fun h => p.2.2.1.1 (hs.trans h)) fun h => p.2.2.1.2 (hs.trans h)).elim
  row c d := (inherited_row D B C hcover sem (F.map c)
    ⟨F.map d.1, by rw [F.index, F.index]; exact d.2⟩).trans (F.row c d)
end
end ScopeReplicationSemantics

namespace GrowthReplicatedRows
open AmalgamationPlan Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration ScopeReplicationCarrier ScopeReplicationSemantics
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {attach : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A}
  {k : ℕ} (P : Layer I X attach hA hB hC k)

theorem proper_covered (c : Cell P.carrier) (hc : P.carrier.scope c ≠ A) :
    P.carrier.scope c ⊆ B ∨ P.carrier.scope c ⊆ C := by
  rcases P.cases c with ⟨d, rfl⟩ | ⟨hs, _, _⟩
  · rcases RelativeLadderLayer.cell_cases I.boundary (by omega : 0 < A.card) d with ⟨e, rfl⟩ | ⟨v, rfl⟩
    · have hi := (P.base_index (RelativeLadderLayer.old I.boundary (by omega) e)).trans
        (RelativeLadderLayer.old_index I.boundary (by omega) e)
      simpa only [CellScheme.scope, hi] using (I.occupied_iff (I.boundary.cell_mem e)).mp ⟨e, rfl⟩
    · exact (hc ((congrArg Prod.fst (P.base_index _)).trans
        (congrArg Prod.fst (RelativeLadderLayer.added_index I.boundary (by omega) v)))).elim
  · exact (hc hs).elim

abbrev carrier := ScopeReplicationCarrier.scheme P.carrier B C
abbrev old := ScopeReplicationCarrier.old P.carrier B C
abbrev erase := ScopeReplicationCarrier.erase P.carrier B C

def rows : Semantics (carrier P) :=
  ScopeReplicationSemantics.rows P.carrier B C (proper_covered P) P.rows

theorem consistent : (rows P).IsConsistent :=
  ScopeReplicationSemantics.consistent P.carrier B C (proper_covered P) P.rows P.consistent

theorem coded (hp : P.rows.IsCoded) : (rows P).IsCoded := fun c _ => by
  change IsCodedLabel ((carrier P).grade c) (P.rows.E (erase P c) _)
  rw [← ScopeReplicationCarrier.erase_grade P.carrier B C c]; exact hp _ _

def face {T : Finset ι} {E : CellScheme T} {semE : Semantics E}
    (F : ExactSemanticFace semE P.rows) (hT : T ⊆ B ∨ T ⊆ C) :
    ExactSemanticFace semE (rows P) :=
  ScopeReplicationSemantics.face P.carrier B C (proper_covered P) P.rows F hT

theorem copy_eq {V : Finset ι × ℕ} {p : (carrier P).below V → ExtOrd}
    (hp : RespectsSemanticsBelow (rows P) V p) (a b : (carrier P).below V)
    (hs : (carrier P).scope a.1 ⊆ (carrier P).scope b.1) (he : erase P a.1 = erase P b.1) :
    p a = p b :=
  ScopeReplicationSemantics.copy_eq P.carrier B C (proper_covered P) P.rows hp a b hs he

theorem lift_to_full {U : Finset ι × ℕ} {j : ℕ} (h : GradedLe U (A, j))
    (hside : U.1 ⊆ B ∨ U.1 ⊆ C) (hl : CoatomBoundaryExtension.CappedLift P.rows h) :
    CoatomBoundaryExtension.CappedLift (rows P) h := by
  intro p q γ hp hq hγ hag
  let fullErase (d : (carrier P).below (A, j)) : P.carrier.below (A, j) :=
    ⟨erase P d.1, P.carrier.isPlan.subset_of_mem (P.carrier.scope_mem_plan _),
      (erase_grade P.carrier B C d.1).le.trans d.2.2⟩
  obtain ⟨r, hr, hcap, hread⟩ := hl (p ∘ oldBelow P.carrier B C U) (q ∘ oldBelow P.carrier B C (A, j)) γ
    (restrict_respects P.carrier B C (proper_covered P) P.rows hp)
    (restrict_respects P.carrier B C (proper_covered P) P.rows hq) hγ
    fun d => hag (oldBelow P.carrier B C U d)
  refine ⟨r ∘ fullErase,
    duplicateBelow_respects P.carrier B C (proper_covered P) P.rows (fun d => (fullErase d).2) hr,
    fun d => (hcap (fullErase d)).trans (congrArg (fun x => min x γ)
      (copy_eq P hq d (oldBelow P.carrier B C (A, j) (fullErase d))
        (by simpa only [CellScheme.scope, oldBelow, old_index] using scope_le_erase P.carrier B C d.1)
        (erase_old P.carrier B C (erase P d.1)).symm).symm),
    fun d => ?_⟩
  rcases cases P.carrier B C d.1 with ⟨c, hc⟩ | ⟨a, ha⟩
  · have hcI : GradedLe (P.carrier.cell c) U := by rw [← old_index P.carrier B C c, ← hc]; exact d.2
    rw [← show oldBelow P.carrier B C U ⟨c, hcI⟩ = d from Subtype.ext hc.symm]
    exact (congrArg r (Subtype.ext (erase_old P.carrier B C c))).trans (hread ⟨c, hcI⟩)
  · have hs : a.1.1.1 ⊆ U.1 := by simpa only [ha, added_index] using d.2.1
    exact (hside.elim (fun hb => a.2.2.1.1 (hs.trans hb)) fun hc => a.2.2.1.2 (hs.trans hc)).elim

section Constructed
variable (I X attach hA hB hC) (t : ℕ) (ht : t + 2 ≤ A.card)

abbrev built := build I X attach hA hB hC t ht

theorem build_consistent : (rows (built I X attach hA hB hC t ht)).IsConsistent := consistent _

theorem build_coded : (rows (built I X attach hA hB hC t ht)).IsCoded :=
  coded _ (GrowthPaddedInstallation.build_coded I X attach hA hB hC t ht)

def donorFace : ExactSemanticFace I.leftRows (rows (built I X attach hA hB hC t ht)) :=
  face _ (GrowthPaddedInstallation.donorFace I X attach hA hB hC t ht) (Or.inl le_rfl)

def privateFace : ExactSemanticFace I.rightRows (rows (built I X attach hA hB hC t ht)) :=
  face _ (GrowthPaddedInstallation.privateFace I X attach hA hB hC t ht) (Or.inr le_rfl)

theorem donor_order : StrictMono (donorFace I X attach hA hB hC t ht).map :=
  (old_order _ B C).comp (GrowthPaddedInstallation.donor_order I X attach hA hB hC t ht)

theorem private_order : StrictMono (privateFace I X attach hA hB hC t ht).map :=
  (old_order _ B C).comp (GrowthPaddedInstallation.private_order I X attach hA hB hC t ht)

theorem complete_through {V : Finset ι × ℕ} (hV : V ∈ Plan.gradedPlan R) (hv : V.2 ≤ t + 2) :
    ∃ d, (carrier (built I X attach hA hB hC t ht)).cell d = V := by
  classical
  let P := built I X attach hA hB hC t ht
  by_cases hside : V.1 ⊆ B ∨ V.1 ⊆ C
  · obtain ⟨d, hd⟩ := (I.occupied_iff hV).mpr hside
    exact ⟨old P (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) d)),
      (old_index _ B C _).trans ((P.base_index _).trans
        ((RelativeLadderLayer.old_index I.boundary (by omega) d).trans hd))⟩
  · obtain ⟨c, hc⟩ := GrowthPaddedInstallation.full_occupied I X attach hA hB hC t ht
      V.2 (Plan.mem_gradedPlan.mp hV).2.1 hv
    have hs : P.carrier.scope c = A := by rw [CellScheme.scope, hc]
    have hg : P.carrier.grade c = V.2 := by rw [CellScheme.grade, hc]
    have hm : V.1 = A ∨ Mixed B C V.1 := Or.inr ⟨fun h => hside (Or.inl h), fun h => hside (Or.inr h)⟩
    have hplan : V.1 ∈ P.carrier.plan := by
      rw [GrowthPaddedIteration.build_plan]; exact (Plan.mem_gradedPlan.mp hV).1
    exact ⟨atScope P.carrier B C V.1 hplan hm c hs (hg ▸ (Plan.mem_gradedPlan.mp hV).2.2),
      (atScope_index P.carrier B C _ _ _ _ _ _).trans (Prod.ext rfl hg)⟩
end Constructed

theorem complete :
    (carrier (built I X attach hA hB hC (A.card - 2) (by omega))).IsComplete := by
  intro V hV
  have hp : (carrier (built I X attach hA hB hC (A.card - 2) (by omega))).plan = R :=
    GrowthPaddedIteration.build_plan I X attach hA hB hC (A.card - 2) (by omega)
  have hV' : V ∈ Plan.gradedPlan R := hp ▸ hV
  have hg := (Plan.mem_gradedPlan.mp hV').2.2
  have hc := Finset.card_le_card (I.boundary.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hV').1)
  exact complete_through I X attach hA hB hC (A.card - 2) (by omega) hV' (by omega)

theorem inherited_lift (t : ℕ) (ht : t + 2 ≤ A.card) {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.1 ⊆ B ∨ V.1 ⊆ C) :
    CoatomBoundaryExtension.CappedLift (rows (built I X attach hA hB hC t ht)) h := by
  by_cases he : U = V
  · subst V; exact CoatomBoundaryExtension.lift_refl
  rcases hv with hb | hc
  · exact (donorFace I X attach hA hB hC t ht).lift hb
      (I.left_mem hU (h.1.trans hb)) (I.left_mem hV hb) h he
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
  · exact (privateFace I X attach hA hB hC t ht).lift hc
      (I.right_mem hU (h.1.trans hc)) (I.right_mem hV hc) h he
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)

end
end GrowthReplicatedRows
end VaughtConjecture.Knight
