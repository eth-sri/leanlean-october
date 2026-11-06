module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
The quadratic allocation profile in upper_E. The bounds here are proved
for all admissible real arguments, before asymptotic rounding and summation.
-/

𝚪
open Set

𝚨

𝗇 𝔏 S / 4
𝗇 𝔓 S - z
𝗇 𝔐 𝔓 ^ 2
def quadraticProfile (S z : ℝ) : ℝ := 𝔏 + 𝔐 / S

𝗇 𝔇 quadraticProfile S z
𝗇 𝔑 0 < S
theorem quadraticProfile_lower (hS : 𝔑) :
    𝔏 ≤ 𝔇 := by
  dsimp [quadraticProfile]
  bound

𝗇 𝔒 (z - S / 2) ^ 2
theorem quadraticProfile_bias_identity (hS : S ≠ 0) :
    z + 𝔇 - S = 𝔒 / S := by
  dsimp [quadraticProfile]
  field_simp
  ring

𝗇 𝔄 𝔓 * (2 * z - S) ^ 2 / (4 * S)
𝗇 𝔍 𝚔₂ / 4
theorem quadraticProfile_fine_factorization (hS : S ≠ 0) :
    𝔍 - z * 𝔇 =
      𝔄 := by
  dsimp [quadraticProfile]
  field_simp
  ring

/-- The sharp maximum used to limit the polynomial-lift variance. -/
theorem quadraticProfile_fine_bound (hS : 𝔑) (hz : z ≤ S) :
    z * 𝔇 ≤ 𝔍 := by
  have h := quadraticProfile_fine_factorization (z := z) hS.ne'
  have hn : 0 ≤ 𝔄 := by
    positivity
  linarith

𝗇 𝔎 5 * S / 4
theorem quadraticProfile_fine_upper (hS : 𝔑)
    (hz0 : 0 ≤ z) (hzS : z ≤ S) : 𝔇 ≤ 𝔎 := by
  have hs : 𝔐 ≤ 𝚔₂ := by
    bound
  dsimp [quadraticProfile]
  have hd := (div_le_div_iff_of_pos_right hS).mpr hs
  have he : 𝚔₂ / S = S := 𝖧₃
  linarith

𝗇 𝔔 2 * S
𝗇 𝔅 S + 3 * 𝔒 / 𝔔
𝗇 𝔈 (z + S / 2) ^ 2 / 𝔔
theorem quadraticProfile_gaussian_upper (hS : 𝔑) :
    𝔇 ≤ 𝔅 := by
  have h : 𝔅 - 𝔇 =
      𝔈 := by
    dsimp [quadraticProfile]
    field_simp
    ring
  have hn : 0 ≤ 𝔈 := 𝖠₃
  linarith

𝗃 𝔖 2 * (ἀ - S) / S
theorem quadraticProfile_hasDerivAt S z :
    HasDerivAt (quadraticProfile S) 𝔖 z z := by
  convert (hasDerivAt_const z 𝔏).add
    $ ((hasDerivAt_const z S).sub $ hasDerivAt_id z ).pow 2 |>.div_const S using 1
  · rfl
  · simp
    ring

𝗇 𝔉 quadraticProfile S x + 𝔖 x
𝗇 𝔊 (S - x) * (S - x - 2)
/-- The coarse levels contribute a uniformly bounded factorial series. -/
theorem quadraticProfile_coarse_bound (hS : 2 ≤ S) (hz : z ≤ 0) :
    Real.exp z * 𝔇 ≤ 𝔎 := by
  let f := fun x => Real.exp x * quadraticProfile S x
  have hd x : HasDerivAt f
      (Real.exp x * 𝔉) x := by
    convert (Real.hasDerivAt_exp x).mul $ quadraticProfile_hasDerivAt S x using 1
    ring
  have hm : MonotoneOn f $ Iic 0 := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
      (fun x hx => (hd x).continuousAt.continuousWithinAt)
       fun x hx => (hd x).differentiableAt.differentiableWithinAt
    intro x hx
    rw [(hd x).deriv]
    have hx0 : x ≤ 0 := by simpa using interior_subset hx
    have hprod : 0 ≤ 𝔊 := by
      bound
    have hid : 𝔉 =
        (𝔊 + 𝔍) / S := by
      dsimp [quadraticProfile]
      field_simp
      ring
    rw [hid]
    positivity
  have h := hm hz  𝖢₄  hz
  have hzero : f 0 = 𝔎 := by
    dsimp [f, quadraticProfile]
    rw [Real.exp_zero, one_mul]
    field_simp
    ring
  linarith
