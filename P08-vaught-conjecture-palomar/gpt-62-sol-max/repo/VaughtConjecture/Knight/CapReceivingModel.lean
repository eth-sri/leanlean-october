/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCoverReceivingCore
public import VaughtConjecture.Knight.CanonicalCoatomFiniteSupply
public import VaughtConjecture.Knight.CoatomFaceLift

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd

universe w

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

namespace FiniteCutReceiving

private theorem eq_of_cap_lt {x y δ : ExtOrd}
    (h : min x δ = min y δ) (hy : y < δ) : x = y := by
  rw [min_eq_left hy.le] at h
  rcases le_or_gt x δ with hx | hx
  · rwa [min_eq_left hx] at h
  · rw [min_eq_right hx.le] at h
    exact False.elim (hy.ne h.symm)

/-- The four original clauses, with structural assumptions retained explicitly.
The bottom-pattern source still has no stage bound. -/
theorem isModel (hFC : FiniteCutReceiving R) (hne : Nonempty M)
    (hcons : R.IsExactParentConsistent) (hcover : R.IsInitialSegmentCovering) :
    R.IsModel := by
  refine ⟨hne, hcons, hcover, ?_, ?_, ?_, ?_⟩
  · intro n t p ht D hD
    obtain ⟨q, hqD, hqp⟩ := exists_coface_of_extendsDomain α.2 p D hD
    obtain ⟨y, hy, r, hr, he, _⟩ := hFC t p ht q hqp (ofOrd 0)
      (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr α.2.bot_lt)
    exact ⟨y, hy, r, he.trans hqD, isCoface_of_consistent hcons ht hr, hr⟩
  · intro n t p ht D hD l hl hext
    obtain ⟨q, ⟨hqD, hpat⟩, hqp⟩ := bottomPatternFamily_nonempty α.2 hD l hl hext
    obtain ⟨y, hy, r, hr, he, hcap⟩ := hFC t p ht q hqp (ofOrd 0)
      (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr α.2.bot_lt)
    refine ⟨y, hy, r, ⟨he.trans hqD, ?_⟩, isCoface_of_consistent hcons ht hr, hr⟩
    intro d
    have hc := hcap (SemScheme.castCell (he.trans hqD).symm d.val)
    have hb : r.label (SemScheme.castCell (he.trans hqD).symm d.val) = ⊥ ↔
        q.label (SemScheme.castCell hqD.symm d.val) = ⊥ := by
      have hh := congrArg (fun x : ExtOrd => x = ⊥) hc
      simp only [min_eq_bot, ofOrd_ne_bot, or_false] at hh
      exact Iff.of_eq hh
    exact hb.trans (hpat d)
  · intro n t p ht γ hγ hγα
    obtain ⟨q, ⟨d, hlo, hhi⟩, hqp⟩ :=
      FixedHeight.exists_uniformity_coface (CanonicalCoatomSupply.supply α.2) p γ hγ hγα
    obtain ⟨a, ha⟩ : ∃ a : Ordinal.{0}, q.label d = ofOrd a := by
      rcases ExtOrd.cases (q.label d) with hb | ht | h
      all_goals simp_all
    have haα : a < α.1 := ofOrd_lt_ofOrd.mp
      ((q.label_bound d).resolve_right (by rw [ha]; exact ofOrd_ne_top _) |> fun h => ha ▸ h)
    obtain ⟨y, hy, r, hr, he, hcap⟩ := hFC t p ht q hqp (ofOrd (a + 1))
      (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr (α.2.succ_lt haα))
    have hd : r.label (SemScheme.castCell he.symm d) = q.label d :=
      eq_of_cap_lt (hcap _) (by rw [ha, ofOrd_lt_ofOrd]; exact Order.lt_succ a)
    refine ⟨y, hy, r, ⟨SemScheme.castCell he.symm d, ?_, ?_⟩,
      isCoface_of_consistent hcons ht hr, hr⟩
    all_goals lia
  · intro n t p ht γ hγα
    obtain ⟨q, ⟨d, hgrade, hhigh⟩, hqp⟩ :=
      FixedHeight.exists_highGrade_coface (CanonicalCoatomSupply.supply α.2) p γ hγα
    obtain ⟨y, hy, r, hr, he, hcap⟩ := hFC t p ht q hqp (ofOrd (γ + 1))
      (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr (α.2.succ_lt hγα))
    refine ⟨y, hy, r, ⟨SemScheme.castCell he.symm d, ?_, ?_⟩,
      isCoface_of_consistent hcons ht hr, hr⟩
    · have hgcast : ∀ {X Y : SemScheme (n + 1)} (e : X = Y) (d : Cell X.scheme),
          Y.scheme.grade (SemScheme.castCell e d) = X.scheme.grade d := by
        aesop
      aesop
    · have hc := hcap (SemScheme.castCell he.symm d)
      have hh : ofOrd γ < min (q.label d) (ofOrd (γ + 1)) :=
        by simp_all
      change min (r.label (SemScheme.castCell he.symm d)) (ofOrd (γ + 1)) =
        min (q.label d) (ofOrd (γ + 1)) at hc
      grind

end FiniteCutReceiving

end VaughtConjecture.Knight
