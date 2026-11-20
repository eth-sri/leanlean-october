/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyCommonRoot

/-! # The gate-free LOW family on two original legal cofaces

Complete vectors retain all future occurrences. The only extra scalar field is
the cutoff. No receiving `Ref`, gate, shadow synchronization, or output scheme is
used. The common root is transported by its literal occurrence and row identities.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor

noncomputable section

variable {n K : ℕ} {P C : SemScheme n}

/-- The actual original-row and donor-display data of the LOW-only family. -/
structure Family (P C : SemScheme n) (K : ℕ) where
  root : CommonRoot P C
  gap : SourceGap C K
  p : P.scheme.Labelling
  p_lawful : RespectsSemantics P.rows p
  top_grade : ∀ d, p d = ⊤ → P.scheme.grade d ≤ K
  root_sub : root.B ⊆ C.scheme.scope gap.c
  root_gap : ∀ a (ht : p a.1 = ⊤),
    gap.h < C.rows.E gap.c ⟨(root.face a).1,
      ⟨(root.face a).2.1.trans root_sub,
        (root.grade a).symm.trans_le ((top_grade a.1 ht).trans_eq gap.c_grade.symm)⟩⟩

/-- Complete original vectors and the free cutoff; there is no gate field. -/
structure State (P C : SemScheme n) where
  u : P.scheme.Labelling
  v : C.scheme.Labelling
  b : ExtOrd

namespace State

def lowerP (S : State P C) j (d : P.ClippedCells j) : ExtOrd := S.u d.1
def lowerC (S : State P C) j (d : C.ClippedCells j) : ExtOrd := S.v d.1

def replace (S : State P C) {j} (u : P.ClippedCells j → ExtOrd)
    (v : C.ClippedCells j → ExtOrd) (b : ExtOrd) : State P C :=
  ⟨completeAt S.u u, completeAt S.v v, b⟩

theorem replace_lowerP (S : State P C) {j}
    u v
    b : (S.replace u v b).lowerP j = u := funext (completeAt_present S.u u)

theorem replace_lowerC (S : State P C) {j}
    u v
    b : (S.replace u v b).lowerC j = v := funext (completeAt_present S.v v)

def CapEq (γ : ExtOrd) (S S' : State P C) : Prop :=
  CappedEq S'.u S.u γ ∧
  CappedEq S'.v S.v γ ∧ min S'.b γ = min S.b γ

def FutureEq (j : ℕ) (S S' : State P C) : Prop :=
  (∀ d, j < P.scheme.grade d → S'.u d = S.u d) ∧
  (∀ d, j < C.scheme.grade d → S'.v d = S.v d)

theorem replace_future (S : State P C) {j}
    u (v : C.ClippedCells j → ExtOrd)
    b : S.FutureEq j (S.replace u v b) :=
  ⟨completeAt_future S.u u, completeAt_future S.v v⟩

theorem replace_caps (S : State P C) {j}
    {u} {v}
    {b γ} (hu : CappedEq u (S.lowerP j) γ)
    (hv : CappedEq v (S.lowerC j) γ) (hb : min b γ = min S.b γ) :
    S.CapEq γ (S.replace u v b) :=
  ⟨completeAt_cap S.u hu, completeAt_cap S.v hv, hb⟩

end State

namespace Family

variable (F : Family P C K)

def maximum (S : State P C) : ExtOrd := nonTopMax (fun d => F.p d = ⊤) S.u

/-- Lawfulness through the current grade, with future fields retained at grade one. -/
structure Source (j : ℕ) (S : State P C) : Prop where
  lawfulP : P.rows.Lawful (S.lowerP j)
  lawfulC : C.rows.Lawful (S.lowerC j)
  shared : F.root.Shared S.u S.v
  futureP : ∀ d, j < P.scheme.grade d → SelfVis 1 (S.u d)
  futureC : ∀ d, j < C.scheme.grade d → SelfVis 1 (S.v d)

structure Admissible (j : ℕ) (S : State P C) : Prop extends F.Source j S where
  cutoff : SelfVis (min j K) S.b
  low : ∀ hj : K ≤ j, F.maximum S < S.b → ∀ d, F.p d = ⊤ →
    max S.b (F.gap.eC hj (S.lowerC j)) ≤ S.u d

theorem Source.replace {j} {S} (hS : F.Source j S)
    {u} {v}
    (hu : P.rows.Lawful u)
    (hv : C.rows.Lawful v) b
    (hface : ∀ a : P.scheme.below (faceIndex F.root.A j),
      u (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
        v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a))) :
    F.Source j (S.replace u v b) where
  lawfulP := completeAt_respects S.u hu
  lawfulC := completeAt_respects S.v hv
  shared := F.root.shared_complete hS.shared u v hface
  futureP d hd := by
    rw [show (S.replace u v b).u d = S.u d from completeAt_future _ _ _ hd]
    exact hS.futureP d hd
  futureC d hd := by
    rw [show (S.replace u v b).v d = S.v d from completeAt_future _ _ _ hd]
    exact hS.futureC d hd

/-- First install only the prescribed root in the opposite original scheme. -/
theorem Source.install_private {j} {S} (hS : F.Source j S)
    {v}
    (hv : C.rows.Lawful v) {γ}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : CappedEq v (S.lowerC j) γ) :
    ∃ u, F.Source j (S.replace u v (min S.b γ)) ∧
      CappedEq u (S.lowerP j) γ := by
  obtain ⟨u, hu, hcap, hface⟩ := F.root.installP hS.lawfulP hv hγ (fun a => by
    simp only [Function.comp_apply]
    rw [hag]
    exact congrArg (fun x => min x γ) (F.root.shared_at hS.shared a))
  exact ⟨u, hS.replace F hu hv _ hface, hcap⟩

theorem Source.install_donor {j} {S} (hS : F.Source j S)
    {u}
    (hu : P.rows.Lawful u) {γ}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : CappedEq u (S.lowerP j) γ) :
    ∃ v, F.Source j (S.replace u v (min S.b γ)) ∧
      CappedEq v (S.lowerC j) γ := by
  obtain ⟨v, hv, hcap, hface⟩ := F.root.installC hS.lawfulC hu hγ (fun a => by
    rw [hag]
    exact congrArg (fun x => min x γ) (F.root.shared_at hS.shared a).symm)
  exact ⟨v, hS.replace F hu hv _ (fun a => (hface a).symm), hcap⟩

theorem frontier_cap {j} (hj : K ≤ j) {v v'}
    {γ} (hγ : SelfVis K γ) (hag : CappedEq v' v γ) :
    min (F.gap.eC hj v') γ = min (F.gap.eC hj v) γ := by
  unfold SourceGap.eC
  rw [← F.gap.e_min hγ, ← F.gap.e_min hγ]
  congr 1
  exact funext (fun d => hag (CellScheme.below.mono (F.gap.domLe hj) d))

end Family
end
end VaughtConjecture.Knight.LowOnly
