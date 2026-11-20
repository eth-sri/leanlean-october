/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WeightedSourcePrefixLayer
public import VaughtConjecture.Knight.OwnerwiseDecoding

@[expose] public section

namespace VaughtConjecture.Knight.ScopedSourcePrefixLayer

open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer

noncomputable section

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}

namespace Data

variable (F : Data D k X)

def rows : Semantics D where
  E c d := if hc : D.cell c = (A, k) then F.profile ⟨c, hc⟩ d.1 else F.base.E c d
  orderly c d := by
    dsimp only
    split_ifs with hc
    · exact (F.profile_visible ⟨c, hc⟩ d.1
        (by simpa only [CellScheme.grade, hc] using d.2.2)).symm
    · exact F.base.orderly c d

theorem row_old {c : Cell D} (hc : D.cell c ≠ (A, k)) : F.rows.E c = F.base.E c := by
  funext d
  simp only [rows, hc, ↓reduceDIte]

theorem row_new (q : Controller D k) (d : D.below (D.cell q.1)) :
    F.rows.E q.1 d = F.profile q d.1 := by simp only [rows, q.2, ↓reduceDIte]

private theorem rows_eq_weighted :
    F.rows = WeightedSourcePrefixLayer.rows F (fun _ => F.ceiling) (fun _ => F.grid_visible _ F.ceiling_mem) := by
  apply Semantics.ext
  funext c d
  by_cases hc : D.cell c = (A, k)
  · let q : Controller D k := ⟨c, hc⟩
    change F.rows.E q.1 d = _
    rw [F.row_new q, WeightedSourcePrefixLayer.row_new _ _ _ q, WeightedSourcePrefixLayer.master_ceiling,
      min_eq_left (F.profile_bound q d.1 (d.2.2.trans_eq (congrArg Prod.snd hc)))]
  · rw [F.row_old hc, WeightedSourcePrefixLayer.row_old _ _ _ hc]

theorem old_respects_iff {c : Cell D} (hc : D.cell c ≠ (A, k))
    {r : D.below (D.cell c) → ExtOrd} :
    RespectsSemanticsBelow F.rows (D.cell c) r ↔
      RespectsSemanticsBelow F.base (D.cell c) r :=
  F.rows_eq_weighted ▸ WeightedSourcePrefixLayer.old_respects_iff _ _ _ hc

theorem profile_respects (q : Controller D k) :
    RespectsSemanticsBelow F.rows (A, k) (fun d => F.profile q d.1) := by
  rw [F.rows_eq_weighted]
  simpa [WeightedSourcePrefixLayer.master_ceiling] using
    WeightedSourcePrefixLayer.master_respects F (fun _ => F.ceiling)
      (fun _ => F.grid_visible _ F.ceiling_mem) (fun p => ⟨p, rfl, rfl⟩) q

theorem decoded_respects (q : Controller D k) {K : ℕ} (hkK : k ≤ K)
    {ν : ExtOrd → ExtOrd} (hν : Witness (gTop K) ν)
    (hproper : ∀ c : D.below (A, k), D.scope c.1 ≠ A →
      RespectsSemanticsBelow F.base (D.cell c.1) (fun d => ν (F.lower q d.1)))
    (hshort : ∀ c : D.below (A, k), D.scope c.1 = A → ∀ d : D.below (D.cell c.1),
      SharpWitnessComposition.Short (D.grade c.1) (F.rows.E c.1 d)) :
    RespectsSemanticsBelow F.rows (A, k) (fun d => ν (F.profile q d.1)) := by
  apply SharpWitnessComposition.map_respects_of_short_or_local (F.profile_respects q)
    (fun d => d.2.2.trans hkK) hν
  intro c
  by_cases hc : D.scope c.1 = A
  · simp_all
  · right
    have hc' : D.cell c.1 ≠ (A, k) := by simp_all
    have ht := (hproper c hc).locality ⟨c.1, GradedLe.refl _⟩
    simpa only [F.row_old hc', F.profile_old q hc',
      F.profile_old q (F.below_old hc' _), CellScheme.below.incl] using ht

/-- The scoped decoder gives a whole section when all grades fit the target. -/
theorem decoded_respects_whole (hmax : ∀ d : Cell D, D.grade d ≤ k)
    (q : Controller D k) {K : ℕ} (hkK : k ≤ K) {ν : ExtOrd → ExtOrd}
    (hν : Witness (gTop K) ν)
    (hproper : ∀ c : Cell D, D.scope c ≠ A →
      RespectsSemanticsBelow F.base (D.cell c) (fun d => ν (F.lower q d.1)))
    (hshort : ∀ c : Cell D, D.scope c = A → ∀ d : D.below (D.cell c),
      SharpWitnessComposition.Short (D.grade c) (F.rows.E c d)) :
    RespectsSemantics F.rows (fun d => ν (F.profile q d)) :=
  (F.decoded_respects q hkK hν (fun c => hproper c.1) (fun c => hshort c.1)).toRespects
    (fun d => ⟨D.scope_subset d, hmax d⟩)

theorem consistent (hbase : ∀ c : Cell D, D.cell c ≠ (A, k) →
    RespectsSemanticsBelow F.base (D.cell c) (F.base.E c)) : F.rows.IsConsistent :=
  F.rows_eq_weighted ▸ WeightedSourcePrefixLayer.consistent F (fun _ => F.ceiling)
    (fun _ => F.grid_visible _ F.ceiling_mem) (fun p => ⟨p, rfl, rfl⟩) hbase

end Data

end

end VaughtConjecture.Knight.ScopedSourcePrefixLayer
