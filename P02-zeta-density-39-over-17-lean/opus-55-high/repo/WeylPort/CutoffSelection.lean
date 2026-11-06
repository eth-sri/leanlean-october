module
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic
import WeylPort.Analytic.RealLaplace

public section

namespace WeylPort

/-- A half-integer first cutoff and an unrestricted dual cutoff exist at every
large scale. The dual cutoff stays away from both adjacent integers. -/
theorem exists_balanced_half_cutoff (R : ℝ) (hR : 10 ≤ R) :
    ∃ A M : ℕ, let x : ℝ := A + 1/2; let y : ℝ := R^2/x
      R ≤ x ∧ x ≤ (12/5)*R ∧ (2/5)*R ≤ y ∧ y ≤ R ∧
      (M:ℝ)+1/8 ≤ y ∧ y ≤ (M:ℝ)+1/2 ∧ ⌊y⌋₊ = M := by
  let M : ℕ := ⌊R/2⌋₊
  pm_8822 b M u
  let A : ℕ := ⌊u+1/2⌋₊
  pm_8822 x A y
  have hR0 : 0 < R := by linarith
  have hMlo : R/2 < (M:ℝ)+1 := Nat.lt_floor_add_one (R/2)
  have hMhi : (M:ℝ) ≤ R/2 := Nat.floor_le (by positivity)
  have hM5 : (5:ℝ) ≤ M := by
    have hm : 5 ≤ M := Nat.le_floor (by grind)
    exact_mod_cast hm
  pm_1604
  have hbR : b ≤ R := by dsimp [b]; linarith
  have hbRlo : (9/20)*R ≤ b := by dsimp [b]; linarith
  have hub : u*b = R^2 := by dsimp [u]; field_simp
  have huR : R ≤ u := by
    pm_8668 le_div_iff₀ hbR
  have huM : 3*(M:ℝ) ≤ u := by
    have hs : (2*(M:ℝ))^2 ≤ R^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    dsimp [u]
    apply (le_div_iff₀ hb).mpr
    dsimp [b]
    nlinarith
  have huhi : u ≤ (20/9)*R := by
    pm_8668 div_le_iff₀ hbRlo
  have hu0 : 0 < u := hR0.trans_le huR
  have hux : u < x := by
    have := Nat.lt_floor_add_one (u+1/2)
    change u+1/2 < (A:ℝ)+1 at this
    dsimp [x]
    linarith
  have hxu : x ≤ u+1 := by
    have := Nat.floor_le (by positivity : 0 ≤ u+1/2)
    change (A:ℝ) ≤ u+1/2 at this
    dsimp [x]
    linarith
  have hx : 0 < x := hu0.trans hux
  have hxR : x ≤ (12/5)*R := by linarith
  have hyb : y ≤ b := by
    dsimp [y]
    apply (div_le_iff₀ hx).mpr
    nlinarith
  have hylo : (M:ℝ)+1/8 ≤ y := by
    dsimp [y]
    apply (le_div_iff₀ hx).mpr
    have hm : 0 ≤ (M:ℝ)+1/8 := by positivity
    have hh := mul_le_mul_of_nonneg_left hxu hm
    have hbu : ((M:ℝ)+1/2)*u = R^2 := by grind
    nlinarith
  have hyR : (2/5)*R ≤ y := by linarith
  have hyM : y ≤ (M:ℝ)+1/2 := hyb
  have hfloor : ⌊y⌋₊ = M := by
    apply Nat.floor_eq_iff (by positivity : 0 ≤ y) |>.mpr
    grind
  grind

/-- At every sufficiently large physical height, the first cutoff is a
half-integer, the dual cutoff obeys both required gap conditions, and both
natural polynomial lengths lie in the verified square-root range. -/
theorem exists_afe_cutoffs_all_heights (t : ℝ) (ht : 200*Real.pi ≤ t) :
    ∃ A M : ℕ, let x : ℝ := A + 1/2; let y : ℝ := t/(2*Real.pi*x)
      1 ≤ x ∧ 1 ≤ y ∧ 2*Real.pi*x*y = t ∧ ⌊x⌋₊ = A ∧ ⌊y⌋₊ = M ∧
      (M:ℝ)+1/8 ≤ y ∧ y ≤ (M:ℝ)+1/2 ∧
      (A:ℝ)^2 ≤ t ∧ (M:ℝ)^2 ≤ t ∧
      Real.sqrt (t/(2*Real.pi)) ≤ x ∧ x ≤ (12/5)*Real.sqrt (t/(2*Real.pi)) ∧
      (2/5)*Real.sqrt (t/(2*Real.pi)) ≤ y ∧ y ≤ Real.sqrt (t/(2*Real.pi)) := by
  have hp : 0 < 2*Real.pi := by positivity
  have ht0 : 0 < t := (by positivity : 0 < 200*Real.pi).trans_le ht
  have hc : 100 ≤ t/(2*Real.pi) := (le_div_iff₀ hp).mpr (by nlinarith)
  let R : ℝ := Real.sqrt (t/(2*Real.pi))
  have hR : 10 ≤ R := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; exact hc)
  have hRsq : R^2 = t/(2*Real.pi) := Real.sq_sqrt (by positivity)
  have htR : t = 2*Real.pi*R^2 := by rw [hRsq]; field_simp
  obtain ⟨A,M,hxlo,hxhi,hylo,hyhi,hgaplo,hgaphi,hfloor⟩ := exists_balanced_half_cutoff R hR
  let x : ℝ := A+1/2
  pm_7156
  pm_64 hx0 x
  have hydef : y = R^2/x := by dsimp [y]; rw [hRsq, div_div]
  change R ≤ x at hxlo
  change x ≤ (12/5)*R at hxhi
  change (2/5)*R ≤ R^2/x at hylo
  change R^2/x ≤ R at hyhi
  rw [← hydef] at hylo hyhi hgaplo hgaphi hfloor
  have hy0 : 0 < y := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hxA : (A:ℝ) ≤ x := by dsimp [x]; linarith
  have hAsq : (A:ℝ)^2 ≤ x^2 := pow_le_pow_left₀ (by positivity) hxA 2
  have hxsq : x^2 ≤ ((12/5)*R)^2 := pow_le_pow_left₀ hx0.le hxhi 2
  have htbig : 6*R^2 ≤ t := by
    rw [htR]
    nlinarith [Real.pi_gt_three, sq_nonneg R]
  pm_7926 hA A
  have hMy : (M:ℝ) ≤ y := by linarith
  have hMsq : (M:ℝ)^2 ≤ R^2 :=
    pow_le_pow_left₀ (by positivity) (hMy.trans hyhi) 2
  pm_7926 hM M
  have hxFloor : ⌊x⌋₊ = A := by
    apply (Nat.floor_eq_iff hx0.le).mpr
    dsimp [x]
    constructor <;> linarith
  have hscale : 2*Real.pi*x*y = t := by
    dsimp [y]
    field_simp
  exact ⟨A,M,hx1,hy1,hscale,hxFloor,hfloor,hgaplo,hgaphi,hA,hM,hxlo,hxhi,hylo,hyhi⟩

end WeylPort
