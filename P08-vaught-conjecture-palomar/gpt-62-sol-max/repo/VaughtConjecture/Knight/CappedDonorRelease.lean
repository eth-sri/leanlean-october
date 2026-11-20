/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowRef
public import VaughtConjecture.Knight.SourceBlockLocalityTransport

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan

namespace CappedDonor

namespace Ref

namespace LowRef

variable {K : ℕ}

/-- The release shifter: the old witness capped at `γ` up to `h`, the old witness above. -/
noncomputable def releaseShifter (τ : ExtOrd → ExtOrd) (h γ : ExtOrd) (x : ExtOrd) : ExtOrd :=
  if x ≤ h then min (τ x) γ else τ x

theorem releaseShifter_of_le {τ : ExtOrd → ExtOrd} {h γ x : ExtOrd} (hx : x ≤ h) :
    releaseShifter τ h γ x = min (τ x) γ := by
  unfold releaseShifter; rw [ite_eq_left hx]

theorem releaseShifter_of_lt {τ : ExtOrd → ExtOrd} {h γ x : ExtOrd} (hx : h < x) :
    releaseShifter τ h γ x = τ x := by
  unfold releaseShifter; simp_all

theorem releaseShifter_eq_bot_iff {τ : ExtOrd → ExtOrd} {h γ : ExtOrd} (hγ : γ ≠ ⊥) (x : ExtOrd) :
    releaseShifter τ h γ x = ⊥ ↔ τ x = ⊥ := by
  unfold releaseShifter
  grind

theorem releaseShifter_le {τ : ExtOrd → ExtOrd} (h γ x : ExtOrd) :
    releaseShifter τ h γ x ≤ τ x := by
  unfold releaseShifter
  grind

/-- The release shifter is a normalized witness through `K` whenever the old witness is, the
split point `h` and the cap `γ` are `K`-visible and `γ` is positive. -/
theorem releaseShifter_witness {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop K) τ) {h γ : ExtOrd}
    (hh : SelfVis K h) (hγ : SelfVis K γ) (hγpos : γ ≠ ⊥) :
    Witness (gTop K) (releaseShifter τ h γ) where
  anti := hτ.anti
  vis := hτ.vis
  bot := by rw [releaseShifter_of_le bot_le, hτ.bot, min_bot_left]
  mono := by
    intro x y hxy
    by_cases hy : y ≤ h
    · rw [releaseShifter_of_le (hxy.trans hy), releaseShifter_of_le hy]
      exact min_le_min_right _ (hτ.mono hxy)
    · rw [releaseShifter_of_lt (not_le.mp hy)]
      exact (releaseShifter_le h γ x).trans (hτ.mono hxy)
  clause5 := by
    intro x kk hle i hi
    by_cases hkk : kk ≤ K
    · have h1 : τ (extVisibilityReplace x kk i) = extVisibilityReplace (τ x) kk i :=
        hτ.comm x hkk hi
      by_cases hx : x ≤ h
      · rw [releaseShifter_of_le hx, releaseShifter_of_le (evr_le_of_le_selfVis hh hkk hi hx), h1,
          evr_min_of_selfVis hγ hkk hi]
      · rw [releaseShifter_of_lt (not_le.mp hx),
          releaseShifter_of_lt (lt_evr_of_selfVis_lt (hh.mono hkk) (not_le.mp hx)), h1]
    · rw [gTop_of_gt (not_le.mp hkk), le_bot_iff] at hle
      have hx : τ x = ⊥ := (releaseShifter_eq_bot_iff hγpos x).mp hle
      have h1 : τ (extVisibilityReplace x kk i) = ⊥ := hτ.zero_repl x hx kk hi
      rw [hle, extVisibilityReplace_bot]
      exact (releaseShifter_eq_bot_iff hγpos _).mpr h1

end LowRef

end Ref

end CappedDonor

end VaughtConjecture.Knight
