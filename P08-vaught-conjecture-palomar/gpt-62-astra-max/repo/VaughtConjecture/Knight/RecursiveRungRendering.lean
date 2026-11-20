/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RungTableRendering
public import VaughtConjecture.Knight.CanonicalFieldLayer

/-! # Recursive raw rows and rendered prefixes over the long rung base

Stage `n` retains the entire rung base and the leaf catalogues of grades
2 through `n + 1`. The catalogue and every occurrence are fixed before an
input is rendered. Raw rows use the previous renderer at the new native grid;
rendered vectors apply one outer paired-slot decoder to the normalized row.

The prefix theorem is proved by grade induction, not carried as a field of
an invariant. Support follows from the outer decoder. The exact base formula
includes every unused rung and follows from whole-table decoding.

These are numerical master vectors, including complete original fields. No
admission, geometric installation, consistency, or bountifulness is asserted.
In particular, retaining the occurrence type does not assert equality of
independently selected renderings at different construction grades.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.RecursiveRungRendering
open Transform Value ExtOrd SourcePrefixRows
open PairedSlotEncoding PairedSlotComparison
noncomputable section

universe u v
variable {X : Type u} {B : Type v} [Fintype X] {Q : ℕ → Type v}

abbrev height (X : Type*) [Fintype X] : ℕ := Fintype.card X + 1
abbrev Base (X B : Type*) [Fintype X] := RungOnlyLadder.Point (height X) B

/-- Every earlier leaf and every base rung stays a separate coordinate. -/
def Aux (X : Type u) (B : Type v) [Fintype X] (Q : ℕ → Type v) : ℕ → Type v
  | 0 => Base X B
  | n + 1 => Aux X B Q n ⊕ Q (n + 2)

instance [Fintype B] [∀ j, Fintype (Q j)] (n : ℕ) : Fintype (Aux X B Q n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Base X B))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Aux X B Q n ⊕ Q (n + 2)))

abbrev grid (X : Type*) [Fintype X] (j : ℕ) := sourceGrid j (Fintype.card X)
abbrev ceiling (X : Type*) [Fintype X] (j : ℕ) := CanonicalFieldLayer.ceiling j X

def baseAt : (n : ℕ) → Base X B → Aux X B Q n
  | 0, v => v
  | n + 1, v => .inl (baseAt n v)

variable (ranks : B → X → ℕ) (fields : (j : ℕ) → Q j → X → ExtOrd)

/-- Native lower calls use the upper profile's own numerical values. -/
def renderAux : (n : ℕ) → (X → ExtOrd) → Finset ExtOrd → ExtOrd → Aux X B Q n → ExtOrd
  | 0, p, _, C, v => RungTableRendering.render ranks p C v
  | n + 1, p, G, C, v =>
    PairedSlotDecoder.decode (n + 2) (values p) G C
      (Sum.elim
        (renderAux n (normalize (n + 2) p) (grid X (n + 2)) (ceiling X (n + 2)))
        (fun q => cut (grid X (n + 2)) (normalize (n + 2) p) (fields (n + 2) q)) v)

private theorem normalized_bound (j : ℕ) {p : X → ExtOrd} (hp : ∀ d, p d ≠ ⊤) (d : X) :
    normalize j p d ≤ ceiling X j := by
  apply (PairedSlotProfiles.normalize_le_ceiling hp d).trans
  apply ofOrd_le_ofOrd.mpr
  exact add_le_add (by gcongr; omega) le_rfl

private theorem normalized_proper (j : ℕ) {p : X → ExtOrd} (hp : ∀ d, p d ≠ ⊤) :
    ∀ d, normalize j p d ≠ ⊤ :=
  (CanonicalPairedProfiles.normalize_mem_inventory X j hp).2

/-- BASE-FORM: the entire base restriction is the original ceiling-filled
table. No cross-grade identity on the higher leaves is used or asserted. -/
theorem render_base (n : ℕ) {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis (n + 1) z)
    (hC : SelfVis (n + 1) C) (hpC : ∀ d, p d ≤ C) (v : Base X B) :
    renderAux ranks fields n p G C (baseAt n v) = RungTableRendering.render ranks p C v := by
  induction n generalizing p G C with
  | zero => rfl
  | succ n ih =>
    change PairedSlotDecoder.decode (n + 2) (values p) G C
      (renderAux ranks fields n (normalize (n + 2) p)
        (grid X (n + 2)) (ceiling X (n + 2)) (baseAt n v)) = _
    rw [ih (p := normalize (n + 2) p) (G := grid X (n + 2))
      (C := ceiling X (n + 2)) (normalized_proper _ hp)
      (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
      (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega))
      (normalized_bound _ hp)]
    exact RungTableRendering.decode_normalized ranks (n + 2) p hp hG hC
      (decode_reserved_ceiling hC hpC) v

end
end VaughtConjecture.Knight.RecursiveRungRendering
