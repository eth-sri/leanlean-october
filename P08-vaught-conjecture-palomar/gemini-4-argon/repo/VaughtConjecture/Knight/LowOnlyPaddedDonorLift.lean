/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedDonorRepair
public import VaughtConjecture.Knight.GradeSplice
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.WitnessSplice

/-! # Active positive-cap donor lifting on the unchanged padded successor

Literal restoration uses the already-proved grade-one scope-raising lift.
The successor's bountifulness is neither assumed nor claimed here.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedDonorLift
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyPaddedSuccessor LowOnlyPaddedDecode LowOnlyPaddedCharts LowOnlyPaddedDonorRepair
open GradeTailRestoration

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem restore
    {p : I.left.scheme.below (effC n 2) → ExtOrd}
    {u : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 2) p)
    (hu : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) u)
    {M : ExtOrd} (hM : SelfVis 2 M)
    (hread : ∀ d, u (donorAt I F hroot hA hB hC d) = min (p d) M)
    (hbound : ∀ d, u d ≤ M)
    (hmax : ∀ d, I.left.scheme.grade d.1 = 2 → p d ≤ M) :
    ∃ r, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) r ∧
      (∀ d, r (donorAt I F hroot hA hB hC d) = p d) ∧
      ∀ d, min (r d) M = min (u d) M :=
  AmbientGradeCharts.restore_of_lower (CappedDonor.Ref.effC_mono (by decide : 1 ≤ 2))
    (donor_grade I F hroot hA hB hC) (fun d => d.2.2.trans (min_le_left 2 n))
    (lowerEquiv I F hroot hA hB hC) (lower_respects_iff I F hroot hA hB hC)
    (fun d hd => ⟨d.1, Finset.subset_univ _, le_min hd (gradeC_le d.1)⟩)
    hp hu hM (fun hp₀ hq₀ => LowOnlyOrderedLadder.donor_lift I F hroot (by omega) hB hC hp₀ hq₀)
    hread hbound hmax

theorem active_donor_lift
    {p : I.left.scheme.below (effC n 2) → ExtOrd}
    {q : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 2) p)
    (hq : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.left.scheme.grade d.1 = 2 ∧ γ < p d)
    (hag : ∀ d, min (q (donorAt I F hroot hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) r ∧
      (∀ d, r (donorAt I F hroot hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hn : 2 ≤ n := by simpa only [hd] using gradeC_le d.1
  obtain ⟨c₀, hc₀⟩ := I.left.complete (effC n 2)
    (CappedDonor.effC_mem (by decide) (by omega))
  exact AmbientGradeCharts.active_lift_of_restore hp hq hγ hpos hd hpd c₀ hc₀ (min_eq_left hn)
    (fun c hci hg hpc => owner_capped I F hroot hA hB hC c hci hg hp hq hγ hpos hpc hag)
    (fun hu hM hread hbound hmax => restore I F hroot hA hB hC hp hu hM hread hbound hmax)
