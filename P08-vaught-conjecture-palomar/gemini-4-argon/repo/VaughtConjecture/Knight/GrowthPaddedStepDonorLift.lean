/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedStepDonorRepair
public import VaughtConjecture.Knight.GrowthPaddedOriginalLifts
public import VaughtConjecture.Knight.GradeSplice
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.WitnessSplice

/-! # Active positive-cap donor lifting on the unchanged padded successor

Literal restoration uses the previously proved original-face lift.
The concrete grade-three endpoint discharges the lower input using the
checked all-cap grade-two theorem. No output bountifulness is assumed.
Adapted from `LowOnlyPaddedPrivateLift`; the predecessor lift and source fibre
are growth theorems, not LOW-family substitutions.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthPaddedStepDonorLift
open Transform Value ExtOrd CappedDonor Growth GrowthPaddedContract GrowthPaddedStepRows GrowthPaddedStepDecode
open GrowthPaddedStepDonorRepair GradeTailRestoration AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

/-- The previous donor face, on the actual predecessor. -/
def previousDonorAt (d : I.left.scheme.below (Finset.univ, k)) :
    P.carrier.below (A, k) :=
  ⟨P.baseMap (RelativeLadderLayer.old I.boundary (by omega) (I.leftFace.map d.1)), by
    rw [P.base_index, RelativeLadderLayer.old_index]
    exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2⟩⟩

/-- Only the predecessor's original-donor lift is needed for restoration. -/
def DonorLowerLift : Prop :=
  ∀ (p : I.left.scheme.below (Finset.univ, k) → ExtOrd)
    (q : P.carrier.below (A, k) → ExtOrd) (γ : ExtOrd),
    RespectsSemanticsBelow I.left.rows (Finset.univ, k) p →
    RespectsSemanticsBelow P.rows (A, k) q → SelfVis k γ →
    (∀ d, min (q (previousDonorAt P d)) γ = min (p d) γ) →
    ∃ r, RespectsSemanticsBelow P.rows (A, k) r ∧
      (∀ d, r (previousDonorAt P d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ

def lowerEquiv : P.carrier.below (A, k) ≃ (carrier P hnext).below (A, k) :=
  HighLayerBountiful.equiv P.carrier (Catalogue X (k + 1))
    (k + 1) (Nat.succ_pos k) hnext (A, k) (fun h => by have := h.2; omega)

theorem lower_respects_iff (p : P.carrier.below (A, k) → ExtOrd) :
    RespectsSemanticsBelow P.rows (A, k) p ↔
      RespectsSemanticsBelow (rows P hk hnext) (A, k)
        (p ∘ (lowerEquiv P hnext).symm) := by
  apply respects_iff_of_equiv (lowerEquiv P hnext)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell _ _ _ _ _ _ _ d)).symm)
    (fun d e => ?_) (fun b d _ => ?_) p
  · simp only [CellScheme.scope, lowerEquiv, HighLayerBountiful.equiv_cell]
  · exact (inherited_row P hk hnext b.1 d).symm

theorem restore (hprev : DonorLowerLift P)
    {p : I.left.scheme.below (Finset.univ, k + 1) → ExtOrd}
    {u : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hu : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) u)
    {M : ExtOrd} (hM : SelfVis (k + 1) M)
    (hread : ∀ d, u (donorAt P hnext d) = min (p d) M)
    (hbound : ∀ d, u d ≤ M)
    (hmax : ∀ d, I.left.scheme.grade d.1 = k + 1 → p d ≤ M) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      ∀ d, min (r d) M = min (u d) M :=
  AmbientGradeCharts.restore_of_lower
    (show GradedLe (Finset.univ, k) (Finset.univ, k + 1) from ⟨Finset.Subset.refl _, Nat.le_succ k⟩)
    (donor_grade P hnext) (fun d => d.2.2) (lowerEquiv P hnext)
    (lower_respects_iff P hk hnext) (fun d hd => ⟨d.1, Finset.subset_univ _, hd⟩)
    hp hu hM (hprev _ _ M) hread hbound hmax

theorem active_donor_lift (hN : k + 1 < X.req.N) (hprev : DonorLowerLift P)
    {p : I.left.scheme.below (Finset.univ, k + 1) → ExtOrd}
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.left.scheme.grade d.1 = k + 1 ∧ γ < p d)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hn : k + 1 ≤ n + 1 := by simpa only [hd] using gradeC_le d.1
  obtain ⟨c₀, hc₀⟩ := I.left.complete (Finset.univ, k + 1)
    (Plan.mem_gradedPlan.mpr ⟨I.left.scheme.isPlan.domain_mem, by omega,
      by simpa only [Finset.card_univ, Fintype.card_fin] using hn⟩)
  exact AmbientGradeCharts.active_lift_of_restore hp hq hγ hpos hd hpd c₀ hc₀ rfl
    (fun c hci hg hpc => owner_capped P hk hnext hN c hci hg hp hq hγ hpos hpc hag)
    (fun hu hM hread hbound hmax => restore P hk hnext hprev hp hu hM hread hbound hmax)
