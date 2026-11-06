/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedOriginalInduction
public import VaughtConjecture.Knight.SeparatedLayerFace

/-! # Actual lower domains on a fixed installed growth carrier

Only occurrences and literal rows are transported. Independently selected
renderings at different grades are not identified.
-/
@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedCutTransport
open Transform Value ExtOrd Growth
open GrowthPaddedContract GrowthPaddedIteration GrowthPaddedStepRows
open CoatomBoundaryExtension
noncomputable section
section Local
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k)

variable (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

/-- No added owner lies below a strictly lower cutoff. -/
def stepEquiv (U : Finset ι × ℕ) (hu : U.2 ≤ k) :
    P.carrier.below U ≃ (successor P hk hnext).carrier.below U :=
  HighLayerBountiful.equiv P.carrier (Catalogue X (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext U (fun h => by have := h.2; omega)

theorem step_lift {U V : Finset ι × ℕ} (h : GradedLe U V) (hv : V.2 ≤ k)
    (hl : CappedLift P.rows h) : CappedLift (successor P hk hnext).rows h :=
  SeparatedLayerFace.lift P.carrier (Catalogue X (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I X T hA hB hC (by omega))
    P.rows (rows P hk hnext) (inherited_row P hk hnext) h
    (fun h => by have := h.2; omega) hl

/-- Grade one is exactly the retained padded base, on every installed layer. -/
def baseEquiv : (base I X T hA hB hC).below (A, 1) ≃ P.carrier.below (A, 1) :=
  Equiv.ofBijective
    (fun d => ⟨P.baseMap d.1, by simpa only [P.base_index] using d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext (P.base_mono.injective (congrArg Subtype.val h)), by
      intro d
      rcases P.cases d.1 with ⟨b, hb⟩ | ⟨_, hg, _⟩
      · have hbm : GradedLe ((base I X T hA hB hC).cell b) (A, 1) := by
          simpa only [hb, P.base_index] using d.2
        exact ⟨⟨b, hbm⟩, Subtype.ext hb.symm⟩
      · have := d.2.2
        change 2 ≤ (P.carrier.cell d.1).2 at hg
        omega⟩

theorem base_index (d : (base I X T hA hB hC).below (A, 1)) :
    P.carrier.cell (baseEquiv P d).1 = (base I X T hA hB hC).cell d.1 :=
  P.base_index d.1

theorem base_respects_iff (p : (base I X T hA hB hC).below (A, 1) → ExtOrd) :
    RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, 1) p ↔
      RespectsSemanticsBelow P.rows (A, 1) (p ∘ (baseEquiv P).symm) := by
  apply respects_iff_of_equiv (baseEquiv P)
    (fun d => (congrArg Prod.snd (base_index P d)).symm)
    (fun d e => ?_) (fun c d _ => (P.base_row c.1 d).symm) p
  simp only [CellScheme.scope, base_index]

end Local

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

end
end VaughtConjecture.Knight.GrowthPaddedCutTransport
