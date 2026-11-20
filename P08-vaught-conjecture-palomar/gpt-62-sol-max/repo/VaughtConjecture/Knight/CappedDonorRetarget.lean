/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowRef

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

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
    · rw [glueSection_of_le w q hd]; apply hw.orderly
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
      rwa [glueSection_of_le w q hS, glueSection_of_le w q (d := ⟨Xi.1, Xi.2.trans h⟩) Xi.2]
    · obtain ⟨Xi, hcell, hle⟩ := hq.availability Sig Xi₀ hs hg
      have hX : ¬ GradedLe (D.cell Xi.1) CI := by
        intro hX
        apply hS
        refine ⟨by rw [hscope]; exact Sig.2.1, ?_⟩
        have h1 : D.grade Xi.1 = D.grade Xi₀.1 := congrArg Prod.snd hcell
        change D.grade Sig.1 ≤ CI.2
        rw [hg, ← h1]; exact hX.2
      refine ⟨Xi, hcell, ?_⟩
      rwa [glueSection_of_not_le w q hS, glueSection_of_not_le w q hX]

end Glue

namespace CappedDonor

namespace Ref

section Retarget

/-- The shifter at a donor-top owner: the old witness where it is bottom or below the rounded
non-top sources, constantly `η` above. -/
noncomputable def retargetShifter (τ : ExtOrd → ExtOrd) (a η : ExtOrd) (x : ExtOrd) : ExtOrd :=
  if τ x = ⊥ then ⊥ else if x ≤ a then τ x else η

theorem retargetShifter_of_bot {τ : ExtOrd → ExtOrd} {a η x : ExtOrd} (h : τ x = ⊥) :
    retargetShifter τ a η x = ⊥ := by
  unfold retargetShifter; rw [ite_eq_left h]

theorem retargetShifter_of_le {τ : ExtOrd → ExtOrd} {a η x : ExtOrd} (hx : x ≤ a) :
    retargetShifter τ a η x = τ x := by
  unfold retargetShifter
  aesop

theorem retargetShifter_of_lt {τ : ExtOrd → ExtOrd} {a η x : ExtOrd} (h : τ x ≠ ⊥) (hx : a < x) :
    retargetShifter τ a η x = η := by
  unfold retargetShifter; aesop

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
      · have h1 : τ (extVisibilityReplace x kk i) = ⊥ := hτ.zero_repl x hx kk hi
        rw [retargetShifter_of_bot hx, retargetShifter_of_bot h1, extVisibilityReplace_bot]
      · have h1 : τ (extVisibilityReplace x kk i) = extVisibilityReplace (τ x) kk i :=
          hτ.comm x hkk hi
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
      have h1 : τ (extVisibilityReplace x kk i) = ⊥ := hτ.zero_repl x hx kk hi
      rw [hle, retargetShifter_of_bot h1, extVisibilityReplace_bot]

end Retarget

end Ref

end CappedDonor

end VaughtConjecture.Knight
