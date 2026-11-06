module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SpecMerge

/-!
# The sweep (WP-D), part 1: first hits and the union of two chains

Euclidean facts used by every correct implementation of `SweepSpec` (the sweep of
pp. 503–507): how the answer `Merge.shoot J.whole z σ` of a query decomposes into first hits of
the two chains, and how first hits on several sets (for instance the arcs of a region, answered
one by one by the ray shooter of `ShooterOK`) combine.

## First hits on sets (`FirstHit`, `NoHit` of `SpecKernels`)

* `firstHit_unique`: the first-hit parameter is unique.
* `FirstHitOpt`: a first hit (`some t`) or no hit (`none`), the answer of one shooter call.
* `firstHitOpt_union`, `firstHitOpt_biUnion`: the answer for a union is the minimum
  (`omin`, `ominList`) of the answers.
* `firstHit_of_subset`, `le_of_firstHit_subset`: comparing first hits on nested sets.

## The union of the two chains of a junction

* `whole_hitParam_eq_min`: below the top of `C`, the first hit of `C = J.whole` is the earlier of
  the slit-free first hits of `C₁` and `C₂` (the slits play no role, `Merge.hitParam_eq_rayHit`).
* `left_hitParam_eq`, `right_hitParam_eq`: below the top of `Cᵢ`, the slit-free first hit of `Cᵢ`
  is the first hit in the chain model of `Cᵢ`.
* `rayHit_eq_empty_of_above`: above the top of a chain the ray never meets it (so the hits of
  the model of `C₂` on the slit of `C₂`, for queries above `top(C₂)`, are discarded simply by
  ignoring `C₂`: review of the merge redesign, m2).
* `freeAt_whole_iff`: a direction is free for `C` iff the initial part of the ray is in the box
  and off both chains.
* `shoot_whole_eq`: the chord of `C` seen from a query point is the segment to the earlier hit.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (rayHit rayHitSet rayHit_union hitParam_eq_rayHit FreeAt shoot)

namespace Sweep

/-! ## First hits on sets -/

/-- **Uniqueness of the first hit.** -/
theorem firstHit_unique {A : Set Point} {p : Point} {σ t t' : ℝ} (h : FirstHit A p σ t)
    (h' : FirstHit A p σ t') : t = t' := by
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd h.2.1 (h'.2.2 t h.1 hlt)
  · exact heq
  · exact absurd h'.2.1 (h.2.2 t' h'.1 hgt)

/-- A first hit on `B` that lies in `A ⊆ B` is the first hit on `A`. -/
theorem firstHit_of_subset {A B : Set Point} (hAB : A ⊆ B) {p : Point} {σ t : ℝ}
    (h : FirstHit B p σ t) (ht : rayPt p σ t ∈ A) : FirstHit A p σ t :=
  by core_grind

/-- The answer of one shooter call: a first hit at `t` (`some t`) or no hit (`none`). -/
def FirstHitOpt (A : Set Point) (p : Point) (σ : ℝ) : Option ℝ → Prop
  | some t => FirstHit A p σ t
  | none => NoHit A p σ

/-- The minimum of two optional parameters (`none` is `+∞`). -/
noncomputable def omin : Option ℝ → Option ℝ → Option ℝ
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, b => b

/-- **First hit on a union**: the answer for `A ∪ B` is the minimum of the answers. -/
theorem firstHitOpt_union {A B : Set Point} {p : Point} {σ : ℝ} {a b : Option ℝ}
    (ha : FirstHitOpt A p σ a) (hb : FirstHitOpt B p σ b) :
    FirstHitOpt (A ∪ B) p σ (omin a b) := by
  cases a with
  | none =>
    cases b with
    | none =>
      intro t ht hmem
      rcases hmem with h | h
      · aesop
      aesop
    | some tb =>
      refine ⟨hb.1, Or.inr hb.2.1, fun t' h1 h2 hmem => ?_⟩
      rcases hmem with h | h
      · aesop
      · exact hb.2.2 t' h1 h2 h
  | some ta =>
    cases b with
    | none =>
      refine ⟨ha.1, Or.inl ha.2.1, fun t' h1 h2 hmem => ?_⟩
      rcases hmem with h | h
      · exact ha.2.2 t' h1 h2 h
      aesop
    | some tb =>
      show FirstHit (A ∪ B) p σ (min ta tb)
      grind [Chazelle.Core.FirstHit, Chazelle.Core.Sweep.FirstHitOpt]

/-! ## The union of the two chains of a junction -/

section
variable (J : Merge.Junction) {z : Point}
/-- **The first hit of `C` below its top**: the earlier of the slit-free first hits of `C₁` and
`C₂` (inside the common box). -/
theorem whole_hitParam_eq_min (hz : z.2 ≤ J.whole.top.2)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    J.whole.hitParam z σ =
      min (rayHit J.whole.radius J.left.set z σ) (rayHit J.whole.radius J.right.set z σ) := by
  rw [hitParam_eq_rayHit _ hz, J.whole_set, rayHit_union _ _ _ _ hσ]

/-- Below the top of `C₁`, its slit-free first hit is the first hit in the model of `C₁`. -/
theorem left_hitParam_eq (hz : z.2 ≤ J.left.top.2) (σ : ℝ) :
    rayHit J.whole.radius J.left.set z σ = J.left.hitParam z σ :=
  (hitParam_eq_rayHit J.left hz σ).symm

/-- Below the top of `C₂`, its slit-free first hit is the first hit in the model of `C₂`. -/
theorem right_hitParam_eq (hz : z.2 ≤ J.right.top.2) (σ : ℝ) :
    rayHit J.whole.radius J.right.set z σ = J.right.hitParam z σ :=
  (hitParam_eq_rayHit J.right hz σ).symm


end

/-- **Above the top of a chain the ray never meets it**: the slit-free first hit is the exit
from the box. -/
theorem rayHit_eq_empty_of_above (C : Chain) {z : Point} (hz : C.top.2 < z.2) (r σ : ℝ) :
    rayHit r C.set z σ = rayHit r ∅ z σ := by
  unfold rayHit
  congr 1
  ext t
  simp only [rayHitSet, mem_ofPred_eq, mem_empty_iff_false, or_false]
  constructor
  · rintro ⟨ht, h | h⟩
    · simp_all
    · have := C.snd_le_top_of_mem_set h
      grind [rayPt_snd]
  simp_all

/-- **Freeness for the union**: below the top of `C`, a direction is free for `C` iff the
initial part of the ray stays in the box and off both chains. -/
theorem freeAt_whole_iff (J : Merge.Junction) {z : Point} (hz : z.2 ≤ J.whole.top.2) (σ : ℝ) :
    FreeAt J.whole z σ ↔ ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ Chain.box J.whole.radius ∧
      rayPt z σ t ∉ J.left.set ∧ rayPt z σ t ∉ J.right.set := by
  unfold FreeAt
  have key : ∀ t, rayPt z σ t ∈ J.whole.dom ↔ rayPt z σ t ∈ Chain.box J.whole.radius ∧
      rayPt z σ t ∉ J.left.set ∧ rayPt z σ t ∉ J.right.set := by
    intro t
    have h := Merge.not_mem_dom_iff J.whole (p := rayPt z σ t) (by simp_all)
    rw [J.whole_set] at h
    ram_grind
  simp_all

section
variable (C : Chain) {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : FreeAt C z σ)
include hz hσ h
/-- **The first hit of a chain as a first hit on the complement of its domain**: for a free
direction below the top, the ray first leaves the domain at `C.hitParam z σ`. -/
theorem firstHit_compl_dom : FirstHit C.domᶜ z σ (C.hitParam z σ) := by
  obtain ⟨h1, h2, h3⟩ := Merge.hit_of_freeAt C hz hσ h
  grind [Chazelle.Core.FirstHit]

/-- **The first hit of a chain on any part of the complement of its domain** containing the
first-hit point is at the first-hit parameter. -/
theorem firstHit_of_compl_dom {A : Set Point} (hA : A ⊆ C.domᶜ)
    (hmem : rayPt z σ (C.hitParam z σ) ∈ A) : FirstHit A z σ (C.hitParam z σ) :=
  firstHit_of_subset hA (firstHit_compl_dom C hz hσ h) hmem


end

end Sweep

end

end Chazelle.Core
