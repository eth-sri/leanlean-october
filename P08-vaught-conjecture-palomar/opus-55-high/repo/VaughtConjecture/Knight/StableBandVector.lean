/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.JumpClosedCore
public import VaughtConjecture.Knight.StableBand

/-! # Finite band vectors and their decoding

This is the algebraic interface for provisional and stable band vectors.
Definitions and declarations are shared by the finite-jump and topological
proofs of stable lawfulness. No band-closedness proof is imported here.
Stable values are decoded from suprema in the completed band, not ordinal
suprema. Proper source labels remain literal.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd StageType

universe w

namespace StageType

variable {β : Ordinal.{0}} {n : ℕ}

section
variable (p : S β n)

/-- The source-top cells of a stage type: the coordinates of its band vectors. -/
abbrev TopCell  := {Xi : Cell p.scheme.scheme // p.label Xi = ⊤}

/-- The labelling decoded from a band vector: a source-top cell reads `bandValue β` of its
coordinate; every other cell keeps its literal label, bottom included. -/
noncomputable def bandLabel (r : p.TopCell → ℕ∞) (Xi : Cell p.scheme.scheme) :
    ExtOrd :=
  if h : p.label Xi = ⊤ then bandValue β (r ⟨Xi, h⟩) else p.label Xi

/-- The lawful band vectors: those whose decoded labelling respects the rows. -/
def LawfulBand  : Set (p.TopCell → ℕ∞) :=
  {r | RespectsSemantics p.scheme.rows (p.bandLabel r)}

end

section
variable (p : S β n)

/-- The band jump at `K` decodes to the label jump at `β + K`. -/
theorem bandLabel_jump (K : ℕ) r :
    p.bandLabel (JumpClosed.jump K r) =
      fun Xi => ExtOrd.jump (ofOrd (β + K)) (p.bandLabel r Xi) := by
  funext Xi
  unfold bandLabel
  by_cases h : p.label Xi = ⊤
  · rw [dite_eq_left h, dite_eq_left h]
    change bandValue β (if r ⟨Xi, h⟩ ≤ K then r ⟨Xi, h⟩ else ⊤) = _
    induction r ⟨Xi, h⟩ using ENat.recTopCoe with
    | top => simp [ExtOrd.jump]
    | coe k =>
      by_cases hk : k ≤ K
      · rw [ite_eq_left (Nat.cast_le.mpr hk), bandValue_natCast,
          jump_of_le (ofOrd_le_ofOrd.mpr ((add_le_add_iff_left β).mpr (Nat.cast_le.mpr hk)))]
      · rw [ite_eq_right (fun h' => hk (Nat.cast_le.mp h')), bandValue_top, bandValue_natCast,
          jump_of_not_le fun h' =>
            hk (Nat.cast_le.mp (le_of_add_le_add_left (ofOrd_le_ofOrd.mp h')))]
  · rw [dite_eq_right h, dite_eq_right h, jump_of_le]
    exact (((p.label_bound Xi).resolve_right h).trans_le
      (ofOrd_le_ofOrd.mpr le_self_add)).le

/-- Once the threshold bounds the grades, jumping a lawful band vector remains
lawful. This finite closure fact is shared by both stable-lawfulness proofs. -/
theorem jump_mem_lawfulBand (hβ : Order.IsSuccLimit β) (K : ℕ)
    (hK : ∀ d, p.scheme.scheme.grade d ≤ K)
    {r} (hr : r ∈ p.LawfulBand) :
    JumpClosed.jump K r ∈ p.LawfulBand := by
  change RespectsSemantics p.scheme.rows (p.bandLabel (JumpClosed.jump K r))
  rw [bandLabel_jump]
  exact RespectsSemantics.jump hr hβ K hK

end

end StageType

/-- The provisional labelling restricted along an actual face is lawful. -/
theorem respects_someProvisionalValue_mapCell {β} (hβ : Order.IsSuccLimit β)
    {m n} {p} {q : S β m} {f : Fin n ↪ Fin m} (hpq : typeMap f q = some p) :
    RespectsSemantics p.scheme.rows (fun Xi => q.someProvisionalValue (mapCell hpq Xi)) := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some hpq, restrictFace_eq_of_typeMap_eq_some hpq⟩
  exact (provisionalLift_respects q hβ).restrictFace f hr

namespace KnightRealization

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

namespace RootedCover

variable {x : R.LabelledExt}

/-- The provisional band vector at a rooted cover: the offsets of the source tops. -/
noncomputable def provisionalBand (y : RootedCover x) : x.type.TopCell → ℕ∞ :=
  fun i => offset i.1 i.2 y

/-- The stable band vector: the suprema of the offsets, in the completed band. -/
noncomputable def stableBand (x : R.LabelledExt) : x.type.TopCell → ℕ∞ :=
  fun i => ⨆ y : RootedCover x, (offset i.1 i.2 y : ℕ∞)

section
variable (y : RootedCover x)

/-- The provisional band vector decodes to the provisional values along the rooted cover. -/
theorem bandLabel_provisionalBand  :
    x.type.bandLabel (provisionalBand y) = fun Xi => value y Xi := by
  funext Xi
  unfold StageType.bandLabel
  by_cases h : x.type.label Xi = ⊤
  · rw [dite_eq_left h, value_eq_offset Xi h y]
    exact bandValue_natCast α.1 (offset Xi h y)
  · rw [dite_eq_right h]
    change x.type.label Xi = y.1.type.someProvisionalValue (cell y Xi)
    rw [someProvisionalValue_of_ne_top (by rw [label_cell]; exact h), label_cell]

/-- Provisional band vectors are lawful. -/
theorem provisionalBand_mem_lawfulBand  :
    provisionalBand y ∈ x.type.LawfulBand := by
  change RespectsSemantics _ _
  rw [bandLabel_provisionalBand]
  exact respects_someProvisionalValue_mapCell α.2 (emb_typeMap y)

end

variable (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering)

include hcons hcov in
/-- The stable band vector decodes to the stable labelling (`StableBand` for source tops,
`stableValue_of_ne_top` for the other cells). -/
theorem bandLabel_stableBand :
    x.type.bandLabel (stableBand x) = fun Xi => R.stableValue x.tuple x.type Xi := by
  funext Xi
  unfold StageType.bandLabel
  by_cases h : x.type.label Xi = ⊤
  · rw [dite_eq_left h, stableValue_eq_bandValue_iSup Xi h hcons hcov]
    rfl
  · rw [dite_eq_right h, stableValue_of_ne_top hcons hcov x.eval_eq h]

end RootedCover

end KnightRealization

end VaughtConjecture.Knight
