module

public import Chazelle.Core.ShootCutShTile
public import Chazelle.Core.ShootCutSeg
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.MiscTactics

/-!
# WP-G, part 38: the first hit of a horizontal ray on a segment

The ray-shooter answers a kind-0 piece walk edge by walk edge; on one walk edge the piece is a
segment `[U, V]` (`subSeg_eq_seg`).  For an origin `z` off the segment and `σ = ±1`:

* `seg_off`: if `U` and `V` are at one height other than that of `z`, no hit;
* `seg_on`: if `U`, `V` and `z` are at one height, the hit is the nearer of `U`, `V` if `U` is
  ahead, and there is no hit otherwise;
* `seg_end`: if the heights of `U` and `V` differ and `z` is at the height of an end, the hit is
  that end if it is ahead;
* `seg_mid`: if `z` is strictly between the heights of `U` and `V`, the hit is the point of the
  segment at the height of `z` (any point `X` of the segment at that height) if it is ahead;
* `seg_out`: otherwise, no hit.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Geometry (lerp lerp_fst lerp_snd)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)

namespace ShootCut

/-- The closed segment from `U` to `V`. -/
def seg (U V : Point) : Set Point := {x | ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ x = lerp U V u}

theorem lerp_lerp (a b : Point) (α β u : ℝ) :
    lerp (lerp a b α) (lerp a b β) u = lerp a b (α + u * (β - α)) := by
  ext <;> simp only [lerp_fst, lerp_snd] <;> ring

/-- **A sub-segment of a walk edge is the segment between its ends.** -/
theorem subSeg_eq_seg (M : Model) (p : ℕ) {α β : ℝ} (hαβ : α ≤ β) :
    subSeg M p α β = seg (lerp (M.wa p) (M.wb p) α) (lerp (M.wa p) (M.wb p) β) := by
  ext x
  constructor
  · rintro ⟨s, h0, h1, rfl⟩
    rcases hαβ.lt_or_eq with hlt | heq
    · refine ⟨(s - α) / (β - α), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith), ?_⟩
      rw [lerp_lerp]; congr 1; fsr
    · subst heq
      exact ⟨0, le_rfl, zero_le_one, by rw [lerp_lerp]; congr 1; linarith⟩
  · rintro ⟨u, h0, h1, rfl⟩
    refine ⟨α + u * (β - α), by nlinarith, by nlinarith, by rw [lerp_lerp]⟩

theorem U_mem_seg (U V : Point) : U ∈ seg U V :=
  ⟨0, le_rfl, zero_le_one, by ext <;> simp⟩

theorem V_mem_seg (U V : Point) : V ∈ seg U V :=
  ⟨1, zero_le_one, le_rfl, by ext <;> simp⟩

/-- A point of the segment at the height of `U`, when the heights of the ends are equal. -/
theorem seg_snd_of_eq {U V : Point} (h : U.2 = V.2) {x : Point} (hx : x ∈ seg U V) :
    x.2 = U.2 := by
  obtain ⟨u, -, -, rfl⟩ := hx
  simp only [lerp_snd]; rwring [h]

variable {U V z : Point} {σ : ℝ}

/-- **No hit**: the segment is at another height. -/
theorem seg_off (h : U.2 = V.2) (hz : z.2 ≠ U.2) (x : ℝ) : Cand (seg U V) z σ 0 x :=
  ⟨fun h' => absurd h' (by norm_num), fun _ t _ hS => hz (by
    rwr [← seg_snd_of_eq h hS])⟩

/-- The ray point at the abscissa of a point at the height of `z`. -/
theorem rayPt_of_x (hσ : σ = 1 ∨ σ = -1) {X : Point} (hX : X.2 = z.2) :
    rayPt z σ (σ * (X.1 - z.1)) = X := by
  have := sigma_sq hσ
  ext
  · simp only [rayPt_fst]; rwring [← mul_assoc, this, one_mul]
  · simp only [rayPt_snd]; exact hX.symm

/-- **A set meeting the line of the ray in at most one point `X`.** -/
theorem cand_single {S : Set Point} (hσ : σ = 1 ∨ σ = -1) {X : Point} (hXS : X ∈ S)
    (hX : X.2 = z.2) (huniq : ∀ x ∈ S, x.2 = z.2 → x = X) :
    Cand S z σ (if 0 < σ * (X.1 - z.1) then 1 else 0) X.1 := by
  have hσ2 := sigma_sq hσ
  have key : ∀ t, rayPt z σ t ∈ S → t = σ * (X.1 - z.1) := fun t ht => by
    have := huniq _ ht rfl
    have hx := congrArg Prod.fst this
    simp only [rayPt_fst] at hx
    rw [← hx]; ring_nf; rwring [show σ ^ 2 = σ * σ by ring, hσ2]
  by_cases hpos : 0 < σ * (X.1 - z.1)
  · rw [ite_eq_left hpos]
    refine ⟨fun _ => ⟨hpos, by rwx [rayPt_of_x hσ hX], fun t' h1 h2 hS => ?_⟩,
      fun h => absurd rfl h⟩
    have := key t' hS; linarith
  · rw [ite_eq_right hpos]
    refine ⟨fun h => absurd h (by norm_num), fun _ t ht hS => ?_⟩
    have := key t hS; rw [this] at ht; exact hpos ht

/-- **Ends at different heights**: the segment meets the line of `z` at most once. -/
theorem seg_unique (h : U.2 ≠ V.2) {x x' : Point} (hx : x ∈ seg U V) (hx' : x' ∈ seg U V)
    (hy : x.2 = x'.2) : x = x' := by
  obtain ⟨u, -, -, rfl⟩ := hx
  obtain ⟨u', -, -, rfl⟩ := hx'
  simp only [lerp_snd] at hy
  have : u = u' := by
    have hne  := sub_ne_zero.2 (Ne.symm h)
    have := mul_right_cancel₀ hne (show u * (V.2 - U.2) = u' * (V.2 - U.2) by linarith)
    exact this
  rw [this]

/-- **The hit at a point `X` of a segment with ends at different heights.** -/
theorem seg_at (hσ : σ = 1 ∨ σ = -1) (h : U.2 ≠ V.2) {X : Point} (hXS : X ∈ seg U V)
    (hX : X.2 = z.2) :
    Cand (seg U V) z σ (if 0 < σ * (X.1 - z.1) then 1 else 0) X.1 :=
  cand_single hσ hXS hX fun x hx hxz => seg_unique h hx hXS (by rw [hxz, hX])

/-- **No hit**: the height of `z` is outside the heights of the ends. -/
theorem seg_out (hout : ¬ (min U.2 V.2 ≤ z.2 ∧ z.2 ≤ max U.2 V.2)) (x : ℝ) :
    Cand (seg U V) z σ 0 x := by
  refine ⟨fun h' => absurd h' (by norm_num), fun _ t _ hS => hout ?_⟩
  obtain ⟨u, h0, h1, he⟩ := hS
  have hy := congrArg Prod.snd he
  simp only [rayPt_snd, lerp_snd] at hy
  rw [hy]
  constructor
  · rcases le_total U.2 V.2 with hh | hh
    · rwnl [min_eq_left hh]
    · rwnl [min_eq_right hh]
  · rcases le_total U.2 V.2 with hh | hh
    · rwnl [max_eq_right hh]
    · rwnl [max_eq_left hh]

/-- **Ends and `z` at one height**: the nearer end if `U` is ahead, no hit otherwise. -/
theorem seg_on (hσ : σ = 1 ∨ σ = -1) (h : U.2 = V.2) (hz : z.2 = U.2) (hzS : z ∉ seg U V) :
    Cand (seg U V) z σ (if 0 < σ * (U.1 - z.1) then 1 else 0)
      (if σ * U.1 ≤ σ * V.1 then U.1 else V.1) := by
  have hσ2 := sigma_sq hσ
  -- the points of the segment on the ray line
  have hmem : ∀ t, rayPt z σ t ∈ seg U V ↔ ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
      z.1 + σ * t = U.1 + u * (V.1 - U.1) := fun t => by
    constructor
    · rintro ⟨u, h0, h1, he⟩
      exact ⟨u, h0, h1, by have := congrArg Prod.fst he; simpa using this⟩
    · rintro ⟨u, h0, h1, he⟩
      refine ⟨u, h0, h1, ?_⟩
      ext
      · simpa using he
      · simp only [rayPt_snd, lerp_snd]; rwring [hz, h]
  -- `z` is not between `U` and `V`
  have hzn : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → z.1 ≠ U.1 + u * (V.1 - U.1) := fun u h0 h1 he =>
    hzS ⟨u, h0, h1, Prod.ext (by simpa using he) (by simp only [lerp_snd]; rwring [hz, h])⟩
  have hzU : z.1 ≠ U.1 := fun he => hzn 0 le_rfl zero_le_one (by rwring [he])
  have hzV : z.1 ≠ V.1 := fun he => hzn 1 zero_le_one le_rfl (by rwring [he])
  -- both ends on the same side of `z`
  have hside : (0 < σ * (U.1 - z.1)) ↔ (0 < σ * (V.1 - z.1)) := by
    constructor
    · intro hU
      by_contra hV
      push Not at hV
      have hV' : σ * (V.1 - z.1) < 0 := lt_of_le_of_ne hV (fun h0 => by
        have : V.1 - z.1 = 0 := by
          rcases hσ with rfl | rfl <;> linarith
        exact hzV (by linarith))
      -- a point between `U` and `V` is `z`
      set u := (z.1 - U.1) / (V.1 - U.1)
      have hne : V.1 - U.1 ≠ 0 := fun h0 => by
        have : V.1 = U.1 := by linarith
        rwli [this] at hV'
      have hu : z.1 = U.1 + u * (V.1 - U.1) := by simp only [u]; fsr
      rcases hσ with rfl | rfl
      · have h1 : U.1 > z.1 := by linarith
        have h2 : V.1 < z.1 := by linarith
        exact hzn u (div_nonneg_of_nonpos (by linarith) (by linarith))
          ((div_le_one_of_neg (by linarith)).2 (by linarith)) hu
      · have h1 : U.1 < z.1 := by linarith
        have h2 : V.1 > z.1 := by linarith
        exact hzn u (div_nonneg (by linarith) (by linarith))
          ((div_le_one (by linarith)).2 (by linarith)) hu
    · intro hV
      by_contra hU
      push Not at hU
      have hU' : σ * (U.1 - z.1) < 0 := lt_of_le_of_ne hU (fun h0 => by
        have : U.1 - z.1 = 0 := by
          rcases hσ with rfl | rfl <;> linarith
        exact hzU (by linarith))
      set u := (z.1 - U.1) / (V.1 - U.1)
      have hne : V.1 - U.1 ≠ 0 := fun h0 => by
        have : V.1 = U.1 := by linarith
        rwli [this] at hV
      have hu : z.1 = U.1 + u * (V.1 - U.1) := by simp only [u]; fsr
      rcases hσ with rfl | rfl
      · have h1 : U.1 < z.1 := by linarith
        have h2 : V.1 > z.1 := by linarith
        exact hzn u (div_nonneg (by linarith) (by linarith))
          ((div_le_one (by linarith)).2 (by linarith)) hu
      · have h1 : U.1 > z.1 := by linarith
        have h2 : V.1 < z.1 := by linarith
        exact hzn u (div_nonneg_of_nonpos (by linarith) (by linarith))
          ((div_le_one_of_neg (by linarith)).2 (by linarith)) hu
  by_cases hU : 0 < σ * (U.1 - z.1)
  · rw [ite_eq_left hU]
    have hV := hside.1 hU
    -- the nearer end
    set X := if σ * U.1 ≤ σ * V.1 then U.1 else V.1 with hXd
    have hXU : X = U.1 ∨ X = V.1 := by rw [hXd]; split_ifs <;> simp
    have hXle : σ * X ≤ σ * U.1 ∧ σ * X ≤ σ * V.1 := by
      rw [hXd]; split_ifs with hh
      · exact ⟨le_rfl, hh⟩
      · push Not at hh; exact ⟨hh.le, le_rfl⟩
    have hXpos : 0 < σ * (X - z.1) := by rcases hXU with e | e <;> rw [e] <;> assumption
    refine ⟨fun _ => ⟨hXpos, ?_, fun t' h1 h2 hS => ?_⟩, fun h => absurd rfl h⟩
    · rcases hXU with e | e
      · rw [e, rayPt_of_x hσ (by rw [hz])]; exact U_mem_seg U V
      · rw [e, rayPt_of_x hσ (by rw [hz, h])]; exact V_mem_seg U V
    · obtain ⟨u, h0, h1', he⟩ := (hmem t').1 hS
      -- `σ x` of a point of the segment is at least `σ X`
      have hx : σ * (U.1 + u * (V.1 - U.1)) ≥ σ * X := by
        have : σ * (U.1 + u * (V.1 - U.1)) = (1 - u) * (σ * U.1) + u * (σ * V.1) := by ring
        rw [this]; nlinarith [hXle.1, hXle.2]
      have : σ * (z.1 + σ * t') = σ * z.1 + t' := by
        rw [mul_add, ← mul_assoc, hσ2, one_mul]
      rw [← he, this] at hx
      linarith
  · rw [ite_eq_right hU]
    have hV : ¬ 0 < σ * (V.1 - z.1) := fun h' => hU (hside.2 h')
    refine ⟨fun h => absurd h (by norm_num), fun _ t ht hS => ?_⟩
    obtain ⟨u, h0, h1, he⟩ := (hmem t).1 hS
    push Not at hU hV
    have e0 : σ * (z.1 + σ * t) = σ * z.1 + t := by rw [mul_add, ← mul_assoc, hσ2, one_mul]
    have e1 : σ * (z.1 + σ * t) = σ * (U.1 + u * (V.1 - U.1)) := by rw [he]
    have e2 : t = (1 - u) * (σ * (U.1 - z.1)) + u * (σ * (V.1 - z.1)) := by
      have : σ * z.1 + t = σ * (U.1 + u * (V.1 - U.1)) := by rw [← e0, e1]
      linarith [this]
    have p1 : (1 - u) * (σ * (U.1 - z.1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hU
    have p2  := mul_nonpos_of_nonneg_of_nonpos h0 hV
    linarith

end ShootCut

end

end Chazelle.Core
