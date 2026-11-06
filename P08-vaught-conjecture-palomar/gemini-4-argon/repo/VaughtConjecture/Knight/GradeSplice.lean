/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Semantics

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GradeTailRestoration
open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ} {j : ℕ}

def lowerIncl (hj : j ≤ BJ.2) (d : D.below (BJ.1, j)) : D.below BJ :=
  ⟨d.1, d.2.trans ⟨Finset.Subset.refl _, hj⟩⟩

def splice (u : D.below BJ → ExtOrd) (v : D.below (BJ.1, j) → ExtOrd)
    (d : D.below BJ) : ExtOrd :=
  if h : D.grade d.1 ≤ j then v ⟨d.1, d.2.1, h⟩ else u d

theorem splice_low (u : D.below BJ → ExtOrd) (v : D.below (BJ.1, j) → ExtOrd)
    (d : D.below BJ) (h : D.grade d.1 ≤ j) :
    splice u v d = v ⟨d.1, d.2.1, h⟩ := dite_eq_left h

theorem splice_high (u : D.below BJ → ExtOrd) (v : D.below (BJ.1, j) → ExtOrd)
    (d : D.below BJ) (h : ¬ D.grade d.1 ≤ j) : splice u v d = u d := dite_eq_right h

theorem cap_below {x y M γ : ExtOrd} (h : min x M = min y M) (hγ : γ ≤ M) :
    min x γ = min y γ := by
  simpa only [min_assoc, min_eq_right hγ] using congrArg (fun z => min z γ) h

theorem splice_cap (hj : j ≤ BJ.2) {u : D.below BJ → ExtOrd}
    {v : D.below (BJ.1, j) → ExtOrd} {M : ExtOrd}
    (hag : ∀ d, min (v d) M = min (u (lowerIncl hj d)) M) :
    ∀ d, min (splice u v d) M = min (u d) M := by
  intro d
  by_cases h : D.grade d.1 ≤ j
  · rw [splice_low u v d h]; exact hag ⟨d.1, d.2.1, h⟩
  · rw [splice_high u v d h]

theorem splice_respects (hj : j ≤ BJ.2) {u : D.below BJ → ExtOrd}
    {v : D.below (BJ.1, j) → ExtOrd} {M : ExtOrd}
    (hu : RespectsSemanticsBelow sem BJ u)
    (hv : RespectsSemanticsBelow sem (BJ.1, j) v)
    (hbound : ∀ d, j < D.grade d.1 → u d ≤ M)
    (hag : ∀ d, min (v d) M = min (u (lowerIncl hj d)) M) :
    RespectsSemanticsBelow sem BJ (splice u v) where
  orderly d := by
    by_cases h : D.grade d.1 ≤ j
    · rw [splice_low u v d h]; exact hv.orderly ⟨d.1, d.2.1, h⟩
    · rw [splice_high u v d h]; exact hu.orderly d
  locality c := by
    by_cases h : D.grade c.1 ≤ j
    · have he : (fun d : D.below (D.cell c.1) =>
          min (splice u v (CellScheme.below.incl c d)) (splice u v c)) =
          (fun d => min (v (CellScheme.below.incl (⟨c.1, c.2.1, h⟩ :
            D.below (BJ.1, j)) d)) (v ⟨c.1, c.2.1, h⟩)) := by
        funext d
        rw [splice_low u v c h,
          splice_low u v (CellScheme.below.incl c d) (d.2.2.trans h)]
        rfl
      rw [he]; exact hv.locality ⟨c.1, c.2.1, h⟩
    · have he : (fun d : D.below (D.cell c.1) =>
          min (splice u v (CellScheme.below.incl c d)) (splice u v c)) =
          (fun d => min (u (CellScheme.below.incl c d)) (u c)) := by
        funext d
        rw [splice_high u v c h]
        exact cap_below (splice_cap hj hag _) (hbound c (not_le.mp h))
      rw [he]; exact hu.locality c
  availability d c hs hg := by
    by_cases h : D.grade d.1 ≤ j
    · have hc : D.grade c.1 ≤ j := hg ▸ h
      obtain ⟨w, hw, hdw⟩ := hv.availability ⟨d.1, d.2.1, h⟩ ⟨c.1, c.2.1, hc⟩ hs hg
      refine ⟨lowerIncl hj w, hw, ?_⟩
      rw [splice_low u v d h, splice_low u v (lowerIncl hj w) w.2.2]; exact hdw
    · obtain ⟨w, hw, hdw⟩ := hu.availability d c hs hg
      have hwj : ¬ D.grade w.1 ≤ j := by
        have hwg : D.grade w.1 = D.grade c.1 := congrArg Prod.snd hw
        simpa only [hwg, ← hg] using h
      refine ⟨w, hw, ?_⟩
      rw [splice_high u v d h, splice_high u v w hwj]; exact hdw
