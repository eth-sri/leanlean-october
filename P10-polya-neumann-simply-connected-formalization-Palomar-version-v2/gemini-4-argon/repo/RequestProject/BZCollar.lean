module

public import RequestProject.BZFlow
public import RequestProject.BZSigma

/-!
# Stretching a flow collar (towards External theorem BZ)

Let `Φ` be the short-time flow of a bounded Lipschitz field. A *collar* is an open set `C` with
two functions `a, b` on it such that, on the inner collar `{|a| < T}`, the flow shifts `a` by the
elapsed time and preserves `b`, with `|b| ≤ T/2`. Moving each point `x` of the collar along its
flow line by the time `b(x) θ(a(x))` realizes the stretching `σ_{b}` in the flow time `a`. The
resulting map `collarMap` is a bi-Lipschitz homeomorphism of `ℂ` with explicit inverse
`collarMapInv`, equal to the identity off the inner collar.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

noncomputable section

namespace PolyaNeumann

/-- A function vanishing off `C`, Lipschitz on `C` and bounded, whose nonzero values are taken at
a definite distance from the complement of `C`, is globally Lipschitz. -/
lemma abs_sub_le_of_piecewise {C : Set ℂ} {F : ℂ → ℝ} {L B γ : ℝ} (hγ : 0 < γ) (hL : 0 ≤ L)
    (hoff : ∀ x ∉ C, F x = 0) (hon : ∀ x ∈ C, ∀ y ∈ C, |F x - F y| ≤ L * ‖x - y‖)
    (hB : ∀ x, |F x| ≤ B) (hgap : ∀ x ∈ C, F x ≠ 0 → ∀ y ∉ C, γ ≤ ‖x - y‖) x y :
    |F x - F y| ≤ (L + B / γ) * ‖x - y‖ := by
  have hB0 := (abs_nonneg _).trans (hB x)
  have hBγ : 0 ≤ B / γ := by positivity
  have key : ∀ x y, x ∈ C → y ∉ C → |F x - F y| ≤ (L + B / γ) * ‖x - y‖ := by
    intro x y hx hy
    rw [hoff y hy, sub_zero]
    by_cases h0 : F x = 0
    · rw [h0, abs_zero]; positivity
    · have hg := hgap x hx h0 y hy
      calc _ ≤ B := hB x
        _ = B / γ * γ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hg hBγ
        _ ≤ _ := by nlinarith [norm_nonneg (x - y)]
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
  · exact (hon x hx y hy).trans (by nlinarith [norm_nonneg (x - y)])
  · exact key x y hx hy
  · rw [abs_sub_comm, norm_sub_rev]; exact key y x hy hx
  · rw [hoff x hx, hoff y hy]; simp; positivity

variable {X : ℂ → ℂ} {LX : ℝ≥0} {M : ℝ} {Φ : ℝ → ℂ → ℂ}

open Classical in
/-- The time shift of the collar map. -/
def collarShift (C : Set ℂ) (a b : ℂ → ℝ) (T : ℝ) (x : ℂ) : ℝ :=
  if x ∈ C then b x * tentθ T (a x) else 0

open Classical in
/-- The time shift of the inverse collar map. -/
def collarShiftInv (C : Set ℂ) (a b : ℂ → ℝ) (T : ℝ) (y : ℂ) : ℝ :=
  if y ∈ C then sigmaInv T (b y) (a y) - a y else 0

/-- The collar map `x ↦ Φ_{b(x) θ(a(x))}(x)`. -/
def collarMap (Φ : ℝ → ℂ → ℂ) (C : Set ℂ) (a b : ℂ → ℝ) (T : ℝ) (x : ℂ) : ℂ :=
  Φ (collarShift C a b T x) x

/-- The inverse collar map. -/
def collarMapInv (Φ : ℝ → ℂ → ℂ) (C : Set ℂ) (a b : ℂ → ℝ) (T : ℝ) (y : ℂ) : ℂ :=
  Φ (collarShiftInv C a b T y) y

/-- Hypotheses on a flow collar. -/
structure IsFlowCollar (Φ : ℝ → ℂ → ℂ) (C : Set ℂ) (a b : ℂ → ℝ) (T La Lb γ : ℝ) : Prop where
  T_pos : 0 < T
  T_lt : T < 1 / 2
  γ_pos : 0 < γ
  La_nonneg : 0 ≤ La
  Lb_nonneg : 0 ≤ Lb
  flow : ∀ x ∈ C, |a x| < T → ∀ u, |u| ≤ T →
    Φ u x ∈ C ∧ a (Φ u x) = a x + u ∧ b (Φ u x) = b x
  b_le : ∀ x ∈ C, |b x| ≤ T / 2
  a_lip : ∀ x ∈ C, ∀ y ∈ C, |a x - a y| ≤ La * ‖x - y‖
  b_lip : ∀ x ∈ C, ∀ y ∈ C, |b x - b y| ≤ Lb * ‖x - y‖
  gap : ∀ x ∈ C, |a x| < T → ∀ y ∉ C, γ ≤ ‖x - y‖

namespace IsFlowCollar

variable {C : Set ℂ} {a b : ℂ → ℝ} {T La Lb γ : ℝ}

local notation "Φ0" => IsFlowCollar Φ C a b T La Lb γ

local notation "Φ3" => collarShift C a b T

lemma collarShift_eq_zero (hc : Φ0) 
    (hx : x ∉ C ∨ T ≤ |a x|) : Φ3 x = 0 := by
  unfold collarShift
  split_ifs with h
  · rcases hx with hx | hx
    · exact absurd h hx
    · rw [tentθ_eq_zero hc.T_pos hx, mul_zero]
  · rfl

local notation "Φ1" => collarShiftInv C a b T

lemma collarShiftInv_eq_zero (hc : Φ0) 
    (hy : y ∉ C ∨ T ≤ |a y|) : Φ1 y = 0 := by
  unfold collarShiftInv
  split_ifs with h
  · rcases hy with hy | hy
    · exact absurd h hy
    · rw [sigmaInv_of_le_abs hc.T_pos (hc.b_le y h) hy, sub_self]
  · rfl

lemma abs_collarShift_le (hc : Φ0) x :
    |Φ3 x| ≤ T / 2 := by
  unfold collarShift
  split_ifs with h
  · rw [abs_mul, abs_of_nonneg (tentθ_nonneg _)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (tentθ_le_one hc.T_pos _)).trans (hc.b_le x h)
  · simp; linarith [hc.T_pos]

lemma collarShiftInv_eq (hc : Φ0)  (hy : y ∈ C) :
    Φ1 y = -(b y * tentθ T (sigmaInv T (b y) (a y))) := by
  have h := sigmaMap_sigmaInv hc.T_pos (hc.b_le y hy) (a y)
  unfold sigmaMap at h
  simp [collarShiftInv, if_pos hy]
  linarith

lemma abs_collarShiftInv_le (hc : Φ0) y :
    |Φ1 y| ≤ T / 2 := by
  by_cases hy : y ∈ C
  · rw [hc.collarShiftInv_eq hy, abs_neg, abs_mul, abs_of_nonneg (tentθ_nonneg _)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (tentθ_le_one hc.T_pos _)).trans (hc.b_le y hy)
  · simp [collarShiftInv, hy]; linarith [hc.T_pos]

lemma collarShift_lip (hc : Φ0) (x y : ℂ) :
    |Φ3 x - Φ3 y| ≤
      ((Lb + La / 2) + T / 2 / γ) * ‖x - y‖ := by
  refine abs_sub_le_of_piecewise hc.γ_pos (by have := hc.La_nonneg; have := hc.Lb_nonneg; positivity)
    (fun x hx => hc.collarShift_eq_zero (Or.inl hx)) ?_ hc.abs_collarShift_le ?_ x y
  · intro x hx y hy
    simp [collarShift, if_pos hx, if_pos hy]
    have h2 : |b x * tentθ T (a x) - b y * tentθ T (a y)| ≤
        |b x - b y| * 1 + |b y| * (|a x - a y| / T) := by
      rw [show b x * tentθ T (a x) - b y * tentθ T (a y) =
        (b x - b y) * tentθ T (a x) + b y * (tentθ T (a x) - tentθ T (a y)) by ring]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg (tentθ_nonneg _)]
        exact mul_le_mul_of_nonneg_left (tentθ_le_one hc.T_pos _) (abs_nonneg _)
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_tentθ_sub_le hc.T_pos (a x) (a y)) (abs_nonneg _)
    have h3 : |b y| * (|a x - a y| / T) ≤ La / 2 * ‖x - y‖ := by
      have hT := hc.T_pos
      calc _ ≤ _ :=
            mul_le_mul (hc.b_le y hy) (div_le_div_of_nonneg_right (hc.a_lip x hx y hy) hT.le)
              (by positivity) (by positivity)
        _ = _ := by field_simp
    have := hc.b_lip x hx y hy
    nlinarith
  · intro x hx h0 y hy
    refine hc.gap x hx ?_ y hy
    by_contra hT
    push_neg at hT
    exact h0 (hc.collarShift_eq_zero (Or.inr hT))

lemma collarShiftInv_lip (hc : Φ0) (x y : ℂ) :
    |Φ1 x - Φ1 y| ≤
      ((3 * La + 2 * Lb) + T / 2 / γ) * ‖x - y‖ := by
  refine abs_sub_le_of_piecewise hc.γ_pos (by have := hc.La_nonneg; have := hc.Lb_nonneg; positivity)
    (fun x hx => hc.collarShiftInv_eq_zero (Or.inl hx)) ?_ hc.abs_collarShiftInv_le ?_ x y
  · intro x hx y hy
    simp [collarShiftInv, if_pos hx, if_pos hy]
    have h1 := abs_sigmaInv_sub_le hc.T_pos (hc.b_le x hx) (hc.b_le y hy) (a x) (a y)
    have h2 := hc.a_lip x hx y hy
    have h3 := hc.b_lip x hx y hy
    calc _
        ≤ |sigmaInv T (b x) (a x) - sigmaInv T (b y) (a y)| + |a x - a y| := by
          rw [show sigmaInv T (b x) (a x) - a x - (sigmaInv T (b y) (a y) - a y) =
            sigmaInv T (b x) (a x) - sigmaInv T (b y) (a y) - (a x - a y) by ring]
          exact abs_sub _ _
      _ ≤ 3 * |a x - a y| + 2 * |b x - b y| := by linarith
      _ ≤ (3 * La + 2 * Lb) * ‖x - y‖ := by nlinarith
  · intro x hx h0 y hy
    refine hc.gap x hx ?_ y hy
    by_contra hT
    push_neg at hT
    exact h0 (hc.collarShiftInv_eq_zero (Or.inr hT))

variable (hΦ : IsShortFlow X Φ) (hX : LipschitzWith LX X) (hM : ∀ z, ‖X z‖ ≤ M)
include hΦ hX

local notation "Φ2" => collarMapInv Φ C a b T

local notation "Φ4" => collarMap Φ C a b T

lemma collarMapInv_collarMap (hc : Φ0) x :
    Φ2 (Φ4 x) = x := by
  have hT := hc.T_pos
  have hT1 := hc.T_lt
  by_cases hx : x ∈ C ∧ |a x| < T
  · obtain ⟨hxC, hax⟩ := hx
    set u := Φ3 x
    have hu := hc.abs_collarShift_le x
    have hueq : u = b x * tentθ T (a x) := by simp [u, collarShift, hxC]
    obtain ⟨hyC, hya, hyb⟩ := hc.flow x hxC hax u (by linarith)
    simp only [collarMapInv, collarMap]
    rw [show Φ1 (Φ u x) = -u by
      simp [collarShiftInv, if_pos hyC]
      rw [hyb, show a (Φ u x) = sigmaMap T (b x) (a x) by rw [hya, hueq]; rfl, sigmaInv_sigmaMap hT (hc.b_le x hxC)]
      simp only [sigmaMap]
      rw [hueq]; ring, hΦ.add hX x ⟨by linarith [abs_le.mp hu], by linarith [abs_le.mp hu]⟩
      ⟨by linarith [(abs_le.mp hu).1], by linarith [(abs_le.mp hu).2]⟩, neg_add_cancel,
      hΦ.zero]
  · have h0 : Φ3 x = 0 := hc.collarShift_eq_zero (by
      by_cases h : x ∈ C
      · exact Or.inr (by push_neg at hx; exact hx h)
      · exact Or.inl h)
    have h0' : Φ1 x = 0 := hc.collarShiftInv_eq_zero (by
      by_cases h : x ∈ C
      · exact Or.inr (by push_neg at hx; exact hx h)
      · exact Or.inl h)
    simp [collarMapInv, collarMap, h0, hΦ.zero, h0']

lemma collarMap_collarMapInv (hc : Φ0) y :
    Φ4 (Φ2 y) = y := by
  have hT := hc.T_pos
  have hT1 := hc.T_lt
  by_cases hy : y ∈ C ∧ |a y| < T
  · obtain ⟨hyC, hay⟩ := hy
    set u := Φ1 y
    have hu := hc.abs_collarShiftInv_le y
    have hueq : u = sigmaInv T (b y) (a y) - a y := by simp [u, collarShiftInv, hyC]
    obtain ⟨hxC, hxa, hxb⟩ := hc.flow y hyC hay u (by linarith)
    simp [collarMapInv, collarMap]
    rw [show Φ3 (Φ u y) = -u by
      have h := sigmaMap_sigmaInv hT (hc.b_le y hyC) (a y)
      unfold sigmaMap at h
      simp [collarShift, if_pos hxC]
      rw [hxb, show a (Φ u y) = sigmaInv T (b y) (a y) by rw [hxa, hueq]; ring, hueq]
      linarith, hΦ.add hX y ⟨by linarith [abs_le.mp hu], by linarith [abs_le.mp hu]⟩
      ⟨by linarith [(abs_le.mp hu).1], by linarith [(abs_le.mp hu).2]⟩, neg_add_cancel,
      hΦ.zero]
  · have hc0 : y ∉ C ∨ T ≤ |a y| := by
      by_cases h : y ∈ C
      · exact Or.inr (by push_neg at hy; exact hy h)
      · exact Or.inl h
    simp [collarMapInv, collarMap, hc.collarShiftInv_eq_zero hc0, hΦ.zero, hc.collarShift_eq_zero hc0]

include hM in
/-- Lipschitz bound for a map of the form `x ↦ Φ_{g(x)}(x)`. -/
lemma dist_flow_shift_le {g : ℂ → ℝ} {Lg} (hg : ∀ x y, |g x - g y| ≤ Lg * ‖x - y‖)
    (hgb : ∀ x, |g x| ≤ 1) x y :
    dist (Φ (g x) x) (Φ (g y) y) ≤ (M * Lg + Real.exp LX) * dist x y := by
  calc _ ≤ _ :=
        dist_triangle _ _ _
    _ ≤ M * (Lg * ‖x - y‖) + dist x y * Real.exp LX := add_le_add (by
      rw [dist_eq_norm]
      refine (hΦ.norm_sub_le hM x ⟨by linarith [(abs_le.mp (hgb y)).1], by
        linarith [(abs_le.mp (hgb y)).2]⟩ ⟨by linarith [(abs_le.mp (hgb x)).1], by
        linarith [(abs_le.mp (hgb x)).2]⟩).trans ?_
      exact mul_le_mul_of_nonneg_left (hg x y) ((norm_nonneg _).trans (hM 0))) (by
      refine (hΦ.dist_le hX x y ⟨by linarith [(abs_le.mp (hgb y)).1], by
        linarith [(abs_le.mp (hgb y)).2]⟩).trans ?_
      gcongr
      exact mul_le_of_le_one_right LX.2 (hgb y))
    _ = (M * Lg + Real.exp LX) * dist x y := by rw [dist_eq_norm]; ring

include hM in
lemma collarMap_lipschitz (hc : Φ0) (x y : ℂ) :
    dist (Φ4 x) (Φ4 y) ≤
      (M * ((Lb + La / 2) + (T / 2) / γ) + Real.exp LX) * dist x y :=
  dist_flow_shift_le hΦ hX hM hc.collarShift_lip
    (fun x => (hc.abs_collarShift_le x).trans (by linarith [hc.T_lt])) x y

include hM in
lemma collarMapInv_lipschitz (hc : Φ0) (x y : ℂ) :
    dist (Φ2 x) (Φ2 y) ≤
      (M * ((3 * La + 2 * Lb) + (T / 2) / γ) + Real.exp LX) * dist x y :=
  dist_flow_shift_le hΦ hX hM hc.collarShiftInv_lip
    (fun x => (hc.abs_collarShiftInv_le x).trans (by linarith [hc.T_lt])) x y

omit hΦ hX in
lemma a_collarMapInv (hc : Φ0)  (hyC : y ∈ C)
    (hay : |a y| < T) : Φ2 y ∈ C ∧
      a (Φ2 y) = sigmaInv T (b y) (a y) := by
  have hT1 := hc.T_lt
  have hT0 := hc.T_pos
  have hu := hc.abs_collarShiftInv_le y
  obtain ⟨hxC, hxa, -⟩ := hc.flow y hyC hay (Φ1 y) (by linarith)
  refine ⟨hxC, ?_⟩
  simp [collarMapInv]
  rw [hxa]; simp [collarShiftInv, hyC]

end IsFlowCollar

end PolyaNeumann

end
