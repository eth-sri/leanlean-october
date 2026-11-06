module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoSpec
public import Chazelle.Core.SweepEvGenM

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `1`, mathematics

* `onCB_of_right`, `onCB_of_left`: candidates of `C₂` (`C₁`) are candidates of `C`;
* `freeAt_left_of`, `freeAt_right_of`: a free direction for `C` is free for `C₁` (`C₂`) below its
  top;
* `whole_hit_cases`: below both tops the first hit of `C` is that of `C₁` or of `C₂`;
* `whole_hit_above`: above the top of `C₁` it is that of `C₂`;
* `hit_onCB`: the first hit is a point of the chain or of the box, at a positive parameter.
-/

namespace Chazelle.Core

namespace SweepIo

open Set Filter Topology
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

section M
variable (J : Merge.Junction)

theorem radius_left : J.left.radius = J.whole.radius := FuseMath.radius_of_P J rfl

theorem onCB_of_right {x : Point} (h : OnCB J.right x) : OnCB J.whole x := by
  rcases h with h | h | h
  · exact Or.inl (J.right_set_subset h)
  · exact Or.inr (Or.inl (by aesop))
  · exact Or.inr (Or.inr (by aesop))

theorem onCB_of_left {x : Point} (h : OnCB J.left x) : OnCB J.whole x := by
  rcases h with h | h | h
  · exact Or.inl (J.left_set_subset h)
  · exact Or.inr (Or.inl (by aesop))
  · exact Or.inr (Or.inr (by aesop))

section
variable {z : Point} {σ : ℝ}
theorem freeAt_left_of (hz : z.2 ≤ J.left.top.2) (h : FreeAt J.whole z σ) :
    FreeAt J.left z σ := by
  unfold FreeAt at h ⊢
  filter_upwards [h] with t ht
  exact dom_left J ht (by simp_all)

theorem freeAt_right_of (hz : z.2 ≤ J.right.top.2) (h : FreeAt J.whole z σ) :
    FreeAt J.right z σ := by
  unfold FreeAt at h ⊢
  filter_upwards [h] with t ht
  exact dom_right J ht (by simp_all)

section
variable (hσ : σ = 1 ∨ σ = -1)
include hσ
theorem whole_hit_cases (hz₁ : z.2 ≤ J.left.top.2)
    (hz₂ : z.2 ≤ J.right.top.2) :
    J.whole.hitParam z σ = J.left.hitParam z σ ∨ J.whole.hitParam z σ = J.right.hitParam z σ := by
  rw [whole_hitParam_eq_min J (hz₂.trans J.right_top_le) hσ, left_hitParam_eq J hz₁,
    right_hitParam_eq J hz₂]
  grind

theorem whole_hit_above (hz₂ : z.2 ≤ J.right.top.2)
    (hz₁ : J.left.top.2 < z.2) (hf : FreeAt J.right z σ) :
    J.whole.hitParam z σ = J.right.hitParam z σ :=
  (whole_of_genuine_above₁ J hz₂ hz₁ hσ ((genuine_iff J.right hz₂ hσ).2 ⟨hf, rfl⟩)).2



end

end

end M

/-- **The first hit is a point of the chain or of the box.** -/
theorem hit_onCB (C : Chain) {z : Point} {σ : ℝ} (hz : z.2 ≤ C.top.2) (hσ : σ = 1 ∨ σ = -1)
    (hf : FreeAt C z σ) : 0 < C.hitParam z σ ∧ OnCB C (rayPt z σ (C.hitParam z σ)) := by
  obtain ⟨hT, hout, hin⟩ := Merge.hit_of_freeAt C hz hσ hf
  set T := C.hitParam z σ with hTd
  refine ⟨hT, ?_⟩
  rcases (Merge.not_mem_dom_iff C (p := rayPt z σ T) (by simp_all)).1 hout with
    hb | hs
  · -- on the box boundary
    
    have h2 : |z.2| < C.radius := (C.dom_subset_box (hin (T / 2) (by linarith) (by linarith))).2
    have h1 : |z.1 + σ * T| ≤ C.radius := by
      by_contra hgt
      push Not at hgt
      set δ := |z.1 + σ * T| - C.radius with hδ
      
      set t := T - min (T / 2) (δ / 2) with ht
      have hm1 : min (T / 2) (δ / 2) ≤ T / 2 := min_le_left _ _
      have hm2 : min (T / 2) (δ / 2) ≤ δ / 2 := min_le_right _ _
      have hm0 : 0 < min (T / 2) (δ / 2) := lt_min (by linarith) (by linarith)
      have hd := (C.dom_subset_box (hin t (by linarith) (by linarith))).1
      simp only [rayPt_fst] at hd
      have hσa : |σ| = 1 := by grind
      have e : z.1 + σ * T = (z.1 + σ * t) + σ * (T - t) := by ring
      have h3 : |z.1 + σ * T| ≤ |z.1 + σ * t| + |σ * (T - t)| := by
        rw [e]; exact abs_add_le _ _
      have h4 : |σ * (T - t)| = T - t := by
        rw [abs_mul, hσa, one_mul, abs_of_nonneg (by linarith)]
      linarith
    have : ¬ (|z.1 + σ * T| < C.radius ∧ |z.2| < C.radius) := hb
    right; core_grind
  · exact Or.inl hs

end

end SweepIo

end Chazelle.Core
