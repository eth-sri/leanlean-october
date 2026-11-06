/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowRef

/-! # Uniform top retargeting and exact old-face restoration (audit16 §2, note §3.1)

The first of the two original-row operations of the two-threshold family: on the **unchanged
request scheme `P`**, using only its original rows and the original donor.

**Vertical gluing** (`RespectsSemanticsBelow.glue`): a lawful section on a lower grade set and a
lawful section on the full set with the same scope glue to a lawful section when, at every owner
above the lower grade, the lower section reads like the full one below the owner's own value.

**Uniform retargeting** (`retargetTops`, `retargetTops_respects`): let `u` be lawful at a cutoff
`j ≥ K`,
let `b` be positive and `K`-visible with every donor non-top value strictly below `b` and every
donor-top value at least `b`, and let `η ≥ b` be `K`-visible.  Replacing every designated
donor-top value by `η` and retaining every other value is lawful.  At a donor non-top owner the
capped target is unchanged.  At a donor-top owner `o` (grade `k ≤ K`) the original donor gives
`R_k(E_o d) < E_o t` between donor non-top and donor-top sources (`srcP_nonTop_lt_top`, from
the donor's exact witness at `o`); with `a_o` the maximum of the rounded non-top sources, the
new shifter is the exact normalized witness of `u` at `o` below `a_o`, constantly `η` above, and
bottom wherever the old witness is bottom — monotone, replacement-compatible through `k`, and
bottom-closed above `k` (`retargetShifter_witness`).  Availability uses the donor's witnesses at
designated tops and `u`'s witnesses elsewhere.  This is per-owner surgery, not one scalar
function of the values.

**Exact old-face restoration, arbitrary root** (`exists_retarget_restore`; newapproach2 §4):
given further a lawful private section whose present face values agree with `u` at every donor
non-top face cell and are at least `η` at every donor-top face cell, there is a lawful section
at the cutoff with the whole present face literally that section's, every donor non-top value
literally `u`'s, and every donor-top value at least `η`: restore only the **grade-`≤ K` part of
the face** inside the retargeted section through the effective grade `min K (arity P)` by old
`P`-bountifulness at cap `η`, then attach the unchanged higher-grade values by gluing — every
higher owner is donor non-top and lies below `b ≤ η`, so its whole locality target is unchanged.
The higher-grade face cells are donor non-top, so their prescribed values are `u`'s and the
gluing restores them too.  No bound `KA ≤ K` on the root arity is needed; an empty low part
needs no extension call.  The cap `η` is used as a bountifulness cap only through `K`, never at
a higher grade. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

/-! ## Vertical gluing -/

section Glue

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

open Classical in
/-- The glued section: the lower section on the lower set, the full section above. -/
noncomputable def glueSection {CI BJ : Finset ι × ℕ} (w : D.below CI → ExtOrd)
    (q : D.below BJ → ExtOrd) (d : D.below BJ) : ExtOrd :=
  if hd : GradedLe (D.cell d.1) CI then w ⟨d.1, hd⟩ else q d

theorem glueSection_of_le {CI BJ : Finset ι × ℕ} (w : D.below CI → ExtOrd)
    (q : D.below BJ → ExtOrd) {d : D.below BJ} (hd : GradedLe (D.cell d.1) CI) :
    glueSection w q d = w ⟨d.1, hd⟩ := by
  unfold glueSection; rw [dite_eq_left hd]

theorem glueSection_of_not_le {CI BJ : Finset ι × ℕ} (w : D.below CI → ExtOrd)
    (q : D.below BJ → ExtOrd) {d : D.below BJ} (hd : ¬ GradedLe (D.cell d.1) CI) :
    glueSection w q d = q d := by
  unfold glueSection; rw [dite_eq_right hd]

/-- **Vertical gluing**: with `CI` of the same scope as `BJ` and lower grade, a lawful section
`w` on `CI` and a lawful section `q` on `BJ` glue to a lawful section on `BJ` provided that, at
every owner `Sig` of `BJ` above `CI`, `w` reads like `q` below `Sig` capped at `q Sig`. -/
theorem RespectsSemanticsBelow.glue {CI BJ : Finset ι × ℕ} (h : GradedLe CI BJ)
    (hscope : CI.1 = BJ.1) {q : D.below BJ → ExtOrd} (hq : RespectsSemanticsBelow sem BJ q)
    {w : D.below CI → ExtOrd} (hw : RespectsSemanticsBelow sem CI w)
    (hcompat : ∀ Sig : D.below BJ, ¬ GradedLe (D.cell Sig.1) CI →
      ∀ (d : D.below (D.cell Sig.1)) (hd : GradedLe (D.cell d.1) CI),
        min (w ⟨d.1, hd⟩) (q Sig) = min (q (CellScheme.below.incl Sig d)) (q Sig)) :
    RespectsSemanticsBelow sem BJ (glueSection w q) where
  orderly d := by
    by_cases hd : GradedLe (D.cell d.1) CI
    · rw [glueSection_of_le w q hd]; exact hw.orderly ⟨d.1, hd⟩
    · rw [glueSection_of_not_le w q hd]; exact hq.orderly d
  locality Sig := by
    by_cases hS : GradedLe (D.cell Sig.1) CI
    · have key := hw.locality ⟨Sig.1, hS⟩
      have heq : (fun d : D.below (D.cell Sig.1) =>
          min (glueSection w q (CellScheme.below.incl Sig d)) (glueSection w q Sig)) =
          fun d => min (w (CellScheme.below.incl ⟨Sig.1, hS⟩ d)) (w ⟨Sig.1, hS⟩) := by
        funext d
        rw [glueSection_of_le w q hS, glueSection_of_le w q (d.2.trans hS)]
        rfl
      rw [heq]; exact key
    · have key := hq.locality Sig
      have heq : (fun d : D.below (D.cell Sig.1) =>
          min (glueSection w q (CellScheme.below.incl Sig d)) (glueSection w q Sig)) =
          fun d => min (q (CellScheme.below.incl Sig d)) (q Sig) := by
        funext d
        rw [glueSection_of_not_le w q hS]
        by_cases hd : GradedLe (D.cell d.1) CI
        · rw [glueSection_of_le w q (d := CellScheme.below.incl Sig d) hd]
          exact hcompat Sig hS d hd
        · rw [glueSection_of_not_le w q (d := CellScheme.below.incl Sig d) hd]
      rw [heq]; exact key
  availability Sig Xi₀ hs hg := by
    by_cases hS : GradedLe (D.cell Sig.1) CI
    · have hX : GradedLe (D.cell Xi₀.1) CI :=
        ⟨by rw [hscope]; exact Xi₀.2.1, by
          change D.grade Xi₀.1 ≤ CI.2
          rw [← hg]; exact hS.2⟩
      obtain ⟨Xi, hcell, hle⟩ := hw.availability ⟨Sig.1, hS⟩ ⟨Xi₀.1, hX⟩ hs hg
      refine ⟨⟨Xi.1, Xi.2.trans h⟩, hcell, ?_⟩
      rw [glueSection_of_le w q hS, glueSection_of_le w q (d := ⟨Xi.1, Xi.2.trans h⟩) Xi.2]
      exact hle
    · obtain ⟨Xi, hcell, hle⟩ := hq.availability Sig Xi₀ hs hg
      have hX : ¬ GradedLe (D.cell Xi.1) CI := by
        intro hX
        apply hS
        refine ⟨by rw [hscope]; exact Sig.2.1, ?_⟩
        have h1 : D.grade Xi.1 = D.grade Xi₀.1 := congrArg Prod.snd hcell
        change D.grade Sig.1 ≤ CI.2
        rw [hg, ← h1]; exact hX.2
      refine ⟨Xi, hcell, ?_⟩
      rw [glueSection_of_not_le w q hS, glueSection_of_not_le w q hX]
      exact hle

end Glue

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-! ## The donor's source separation at a donor-top owner -/

/-! ## Uniform retargeting -/

section Retarget

variable {K : ℕ} (L : R.LowRef K) {j : ℕ} {u : P.scheme.below (effP nP j) → ExtOrd}
  {b η : ExtOrd}

/-- The hypotheses of the retargeting lemma: a lawful section whose donor non-top values lie
strictly below a positive `K`-visible `b` and whose donor-top values are at least `b`, and a
`K`-visible target `η ≥ b`. -/
structure RetargetData (u : P.scheme.below (effP nP j) → ExtOrd) (b η : ExtOrd) : Prop where
  respects : RespectsSemanticsBelow P.rows (effP nP j) u
  b_vis : SelfVis K b
  b_pos : ⊥ < b
  nonTop_lt : ∀ d, R.p d.1 ≠ ⊤ → u d < b
  top_ge : ∀ d, R.p d.1 = ⊤ → b ≤ u d
  η_vis : SelfVis K η
  b_le_η : b ≤ η

variable (hj : K ≤ j) (hu : RetargetData (R := R) (K := K) u b η)

include L hj hu

/-- The shifter at a donor-top owner: the old witness where it is bottom or below the rounded
non-top sources, constantly `η` above. -/
noncomputable def retargetShifter (τ : ExtOrd → ExtOrd) (a η : ExtOrd) (x : ExtOrd) : ExtOrd :=
  if τ x = ⊥ then ⊥ else if x ≤ a then τ x else η

omit L hj hu in
theorem retargetShifter_of_bot {τ : ExtOrd → ExtOrd} {a η x : ExtOrd} (h : τ x = ⊥) :
    retargetShifter τ a η x = ⊥ := by
  unfold retargetShifter; rw [ite_eq_left h]

omit L hj hu in
theorem retargetShifter_of_le {τ : ExtOrd → ExtOrd} {a η x : ExtOrd} (hx : x ≤ a) :
    retargetShifter τ a η x = τ x := by
  unfold retargetShifter
  by_cases h : τ x = ⊥
  · rw [ite_eq_left h, h]
  · rw [ite_eq_right h, ite_eq_left hx]

omit L hj hu in
theorem retargetShifter_of_lt {τ : ExtOrd → ExtOrd} {a η x : ExtOrd} (h : τ x ≠ ⊥) (hx : a < x) :
    retargetShifter τ a η x = η := by
  unfold retargetShifter; rw [ite_eq_right h, ite_eq_right (not_le.mpr hx)]

omit L hj hu in
/-- The retargeting shifter is a normalized witness through `k` whenever the old witness is, the
split point is `k`-visible with the old witness at most `b ≤ η` there, and `η` is `k`-visible and
positive. -/
theorem retargetShifter_witness {k : ℕ} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop k) τ)
    {a b η : ExtOrd} (ha : SelfVis k a) (hτa : τ a ≤ b) (hbη : b ≤ η) (hη : SelfVis k η)
    (hηpos : ⊥ < η) : Witness (gTop k) (retargetShifter τ a η) where
  anti := hτ.anti
  vis := hτ.vis
  bot := retargetShifter_of_bot hτ.bot
  mono := by
    intro x y hxy
    by_cases hx : τ x = ⊥
    · rw [retargetShifter_of_bot hx]; exact bot_le
    have hy : τ y ≠ ⊥ := fun hy => hx (le_bot_iff.mp (hy ▸ hτ.mono hxy))
    by_cases hya : y ≤ a
    · rw [retargetShifter_of_le (hxy.trans hya), retargetShifter_of_le hya]
      exact hτ.mono hxy
    · rw [retargetShifter_of_lt hy (not_le.mp hya)]
      by_cases hxa : x ≤ a
      · rw [retargetShifter_of_le hxa]
        exact (hτ.mono hxa).trans (hτa.trans hbη)
      · rw [retargetShifter_of_lt hx (not_le.mp hxa)]
  clause5 := by
    intro x kk hle i hi
    by_cases hkk : kk ≤ k
    · by_cases hx : τ x = ⊥
      · have h1 : τ (extVisibilityReplace x kk i) = ⊥ := by
          rw [hτ.clause5 x kk (by rw [gTop_of_le hkk]; exact le_top) i hi, hx,
            extVisibilityReplace_bot]
        rw [retargetShifter_of_bot hx, retargetShifter_of_bot h1, extVisibilityReplace_bot]
      · have h1 : τ (extVisibilityReplace x kk i) = extVisibilityReplace (τ x) kk i :=
          hτ.clause5 x kk (by rw [gTop_of_le hkk]; exact le_top) i hi
        by_cases hxa : x ≤ a
        · have h2 : extVisibilityReplace x kk i ≤ a := evr_le_of_le_selfVis ha hkk hi hxa
          rw [retargetShifter_of_le hxa, retargetShifter_of_le h2, h1]
        · have h2 : a < extVisibilityReplace x kk i :=
            lt_evr_of_selfVis_lt (ha.mono hkk) (not_le.mp hxa)
          have h3 : τ (extVisibilityReplace x kk i) ≠ ⊥ := by
            rw [h1]; exact extVisibilityReplace_ne_bot hx _ _
          rw [retargetShifter_of_lt hx (not_le.mp hxa), retargetShifter_of_lt h3 h2,
            evr_eq_self_of_selfVis (hη.mono hkk) i]
    · -- above `k` the suppressor is bottom: bottom is closed under replacement
      rw [gTop_of_gt (not_le.mp hkk), le_bot_iff] at hle
      have hx : τ x = ⊥ := by
        by_contra hx
        unfold retargetShifter at hle
        rw [ite_eq_right hx] at hle
        split_ifs at hle with hxa
        · exact hx hle
        · exact absurd hle (ne_bot_of_gt hηpos)
      have h1 : τ (extVisibilityReplace x kk i) = ⊥ := by
        rw [hτ.clause5 x kk (by rw [gTop_of_gt (not_le.mp hkk), hx]) i hi, hx,
          extVisibilityReplace_bot]
      rw [hle, retargetShifter_of_bot h1, extVisibilityReplace_bot]

/-! ## Exact old-face restoration -/

end Retarget

end Ref

end CappedDonor

end VaughtConjecture.Knight
