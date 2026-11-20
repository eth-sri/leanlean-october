/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.ENat.Lattice
public import VaughtConjecture.Knight.ProvisionalOffset

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd StageType Filter

universe w

namespace ExtOrd

/-- **Decoding of the completed band above `β`**: a finite offset `k` is the label `β + k`, and
the completion point `⊤` is the label `⊤`. -/
noncomputable def bandValue (β : Ordinal.{0}) (r : ℕ∞) : ExtOrd :=
  ENat.recTopCoe ⊤ (fun k : ℕ => ofOrd (β + k)) r

@[simp] theorem bandValue_natCast (β : Ordinal.{0}) (k : ℕ) :
    bandValue β k = ofOrd (β + k) :=
  ENat.recTopCoe_natCast _ _ k

@[simp] theorem bandValue_top (β : Ordinal.{0}) : bandValue β ⊤ = ⊤ :=
  ENat.recTopCoe_top _ _

end ExtOrd

namespace KnightRealization

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

namespace RootedCover

variable {x : R.LabelledExt} (Xi : Cell x.type.scheme.scheme) (htop : x.type.label Xi = ⊤)
  (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering)

include hcons hcov in
/-- **The stable value of a source top is the decoded supremum of its offsets**, the supremum
taken in the completed band `ℕ∞`.  An eventually constant offset has its plateau as supremum;
an escaping offset has supremum `⊤`. -/
theorem stableValue_eq_bandValue_iSup :
    R.stableValue x.tuple x.type Xi = bandValue α.1 (⨆ y, (offset Xi htop y : ℕ∞)) := by
  have := isDirectedOrder hcons hcov x
  rcases stableValue_dichotomy Xi htop hcons hcov with ⟨k, hk, hval⟩ | ⟨ht, hsv⟩
  · obtain ⟨i, hi⟩ := eventually_atTop.mp hk
    have hsup : (⨆ y, (offset Xi htop y : ℕ∞)) = k := by
      refine le_antisymm (iSup_le fun y => ?_) ?_
      · obtain ⟨z, hyz, hiz⟩ := exists_ge_ge y i
        exact_mod_cast (offset_mono Xi htop hyz).trans (hi z hiz).le
      · exact (hi i le_rfl).symm ▸ le_iSup (fun y => (offset Xi htop y : ℕ∞)) i
    simp_all
  · have hsup : (⨆ y, (offset Xi htop y : ℕ∞)) = ⊤ := by
      refine ENat.eq_top_iff_forall_ge.mpr fun k => ?_
      obtain ⟨y, hy⟩ := (ht.eventually (eventually_ge_atTop k)).exists
      exact (Nat.cast_le.mpr hy).trans (le_iSup (fun y => (offset Xi htop y : ℕ∞)) y)
    simp_all

end RootedCover

end KnightRealization

end VaughtConjecture.Knight
