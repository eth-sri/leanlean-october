/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryGlobalPredecessor

/-! # Constructed ordinary predecessor for the final receiving installer

`build` starts with compatible legal input schemes and executes the finite
scope construction. No local operator, predecessor lifting, or selected-section
receipt is an input. N is at least four in this initialized-recursion endpoint.
The missing full grade N and apex belong to the final installer, not this output.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryPredecessorSupply
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension
open SourcePrefixRows OrbitPrefixSupport
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)
variable (N : ℕ) (G : Finset ExtOrd) (θ : ExtOrd)

/-- Acceptance receipts of the constructed, deliberately incomplete full scope. -/
structure Output where
  carrier : CellScheme A
  rows : Semantics carrier
  plan : carrier.plan = R
  consistent : rows.IsConsistent
  coded : rows.IsCoded
  original : Cell I.boundary ↪o Cell carrier
  index : ∀ d, carrier.cell (original d) = I.boundary.cell d
  row : ∀ (c : Cell I.boundary) (d : I.boundary.below (I.boundary.cell c)),
    rows.E (original c) ⟨original d.1, by rw [index, index]; exact d.2⟩ = I.rows.E c d
  leftFace : ExactSemanticFace I.leftRows rows
  rightFace : ExactSemanticFace I.rightRows rows
  left_map : ∀ d, leftFace.map d = original (I.leftFace.map d)
  right_map : ∀ d, rightFace.map d = original (I.rightFace.map d)
  left_order : StrictMono leftFace.map
  right_order : StrictMono rightFace.map
  grade_bound : ∀ d, carrier.grade d ≤ N
  full_below : ∀ d, carrier.scope d = A → carrier.grade d < N
  complete : ∀ J ∈ Plan.gradedPlan R, J.1 ≠ A ∨ J.2 < N → ∃ d, carrier.cell d = J
  proper_lift : ∀ CI BJ, CI ∈ Plan.gradedPlan R → BJ ∈ Plan.gradedPlan R →
    BJ.1 ≠ A → (h : GradedLe CI BJ) → CappedLift rows h
  lower_lift : ∀ CI BJ, CI ∈ Plan.gradedPlan R → BJ ∈ Plan.gradedPlan R →
    (h : GradedLe CI BJ) → BJ.2 < N → CappedLift rows h
  mute : ∀ d, carrier.grade d = N → carrier.scope d ≠ B →
    rows.E d ⟨d, GradedLe.refl _⟩ = ⊥
  classification : OrderedScopeRelocation.OwnerClassification rows original
  render : ∀ {p : Cell I.boundary → ExtOrd}, RespectsSemantics I.rows p → (∀ d, p d ≤ θ) →
    Cell carrier → ExtOrd
  readback : ∀ {p} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ) d,
    render hp hb (original d) = p d
  lawful : ∀ {p} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ),
    RespectsSemantics rows (render hp hb)
  bound : ∀ {p} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ) d, render hp hb d ≤ θ
  support : ∀ {p} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ) d,
    Supported N (G : Set ExtOrd) p (render hp hb d)
  agreement : ∀ {p q} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ)
    (hq : RespectsSemantics I.rows q) (hqb : ∀ d, q d ≤ θ) {γ}, γ ∈ G → γ ≤ θ →
    Agree p q γ → Agree (render hp hb) (render hq hqb) γ

variable {N G θ}

/-- Construct every proper scope on the actual boundary, then the full scope
through N-1. The two tall facets used by lifting are obtained from the completed
plan; neither is assumed to be the smaller original donor. -/
def build (n : ℕ) (hBA : B ≠ A) (hCA : C ≠ A) (hunion : A = B ∪ C)
    (hcard : A.card = n + 5) (hB : B.card = n + 4) (hC : C.card < n + 4)
    (hG : ∀ z ∈ G, SelfVis (n + 4) z) (hθ : SelfVis (n + 4) θ)
    (htθ : θ ≠ ⊤) (hθG : θ ∈ G) : Output I (n + 4) G θ := by
  let X := OrdinaryProperPredecessor.construct I hBA hCA (n + 4) G θ
    hunion hcard hG hθ htθ hθG
  refine {
    carrier := OrdinaryGlobalPredecessor.carrier I n X hcard
    rows := OrdinaryGlobalPredecessor.rows I n X hcard
    plan := OrdinaryGlobalPredecessor.plan I n X hcard
    consistent := OrdinaryGlobalPredecessor.consistent I n X hcard
    coded := OrdinaryGlobalPredecessor.coded I n X hcard
    original := OrdinaryGlobalPredecessor.original I n X hcard
    index := OrdinaryGlobalPredecessor.original_index I n X hcard
    row := OrdinaryGlobalPredecessor.original_row I n X hcard
    leftFace := OrdinaryGlobalPredecessor.leftFace I n X hcard hBA
    rightFace := OrdinaryGlobalPredecessor.rightFace I n X hcard hCA
    left_map := fun _ => rfl
    right_map := fun _ => rfl
    left_order := OrdinaryGlobalPredecessor.left_order I n X hcard hBA
    right_order := OrdinaryGlobalPredecessor.right_order I n X hcard hCA
    grade_bound := OrdinaryGlobalPredecessor.grade_bound I n X hcard
    full_below := ?_
    complete := fun J hJ hs => OrdinaryGlobalPredecessor.complete I n X hcard hJ
      (hs.imp id (by omega))
    proper_lift := fun _ _ => OrdinaryGlobalPredecessor.proper_lift I n X hcard
    lower_lift := fun _ _ hi hj h hg => OrdinaryGlobalPredecessor.lower_lift I n X hcard
      hi hj h (by omega)
    mute := OrdinaryGlobalPredecessor.nonprivate_mute I n X hcard hB hC
    classification := OrdinaryGlobalPredecessor.classification I n X hcard
    render := OrdinaryGlobalPredecessor.render I n X hcard htθ
    readback := OrdinaryGlobalPredecessor.readback I n X hcard hG hθ htθ
    lawful := OrdinaryGlobalPredecessor.lawful I n X hcard hG hθ htθ
    bound := OrdinaryGlobalPredecessor.bound I n X hcard hθ htθ
    support := OrdinaryGlobalPredecessor.supported I n X hcard hG htθ hθG
    agreement := ?_ }
  · intro d hd
    rcases OrdinaryGlobalPredecessor.coverage I n X hcard d with ⟨c, rfl⟩ | ⟨_, hg⟩
    · have hs : X.state.carrier.scope c = A := by
        simpa only [CellScheme.scope, CanonicalRecursiveInventory.boundary_cell] using hd
      exact (OrdinaryProperPredecessor.proper I X c hs).elim
    · omega
  · intro p q hp hb hq hqb γ hγ hγθ he
    exact OrdinaryGlobalPredecessor.agreement I n X hcard hG hθ htθ hp hb hq hqb hγ hγθ he

namespace Output
variable (O : Output I N G θ)

end Output
end
end VaughtConjecture.Knight.OrdinaryPredecessorSupply
