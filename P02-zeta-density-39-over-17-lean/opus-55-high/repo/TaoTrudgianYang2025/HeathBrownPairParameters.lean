module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaUniformityFull
public import TaoTrudgianYang2025.HeathBrownExponentAlgebra
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-! Exact secants used in Heath--Brown 2017, Theorem 2. -/

noncomputable section

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

def heathBrownPairK (r : ℝ) : ℝ := 2/((r-1)^2*(r+2))
def heathBrownPairL (r : ℝ) : ℝ := 1-(3*r-2)/(r*(r-1)*(r+2))
def heathBrownPairIntercept (r : ℝ) : ℝ :=
  -(3*r^2-3*r+2)/(r*(r-1)^2*(r+2))
def heathBrownPairLeft (r : ℝ) : ℝ := ((r-1)^2+1)/r
def heathBrownPairRight (r : ℝ) : ℝ := (r^2+1)/(r+1)
def heathBrownPairSecant (r τ : ℝ) : ℝ :=
  heathBrownPairK r*τ+heathBrownPairIntercept r

theorem heathBrownPairK_pos {r : ℝ} (hr : 3 ≤ r) : 0 < heathBrownPairK r := by
  unfold heathBrownPairK
  pm_1074 hm hp
  positivity

section
variable {r : ℝ}
include r
theorem heathBrownPairIntercept_eq (hr : 3 ≤ r) :
    heathBrownPairIntercept r = heathBrownPairL r-heathBrownPairK r-1 := by
  pm_1614
  unfold heathBrownPairIntercept heathBrownPairL heathBrownPairK
  field_simp
  ring

theorem heathBrownPairLeft_succ :
    heathBrownPairLeft (r+1) = heathBrownPairRight r := by
  unfold heathBrownPairLeft heathBrownPairRight
  congr 1
  ring

theorem heathBrownPairSecant_left (hr : 3 ≤ r) :
    heathBrownPairSecant r (heathBrownPairLeft r) = -1/(r*(r-1)) := by
  pm_1614
  unfold heathBrownPairSecant heathBrownPairK heathBrownPairIntercept heathBrownPairLeft
  field_simp
  ring

theorem heathBrownPairSecant_right (hr : 3 ≤ r) :
    heathBrownPairSecant r (heathBrownPairRight r) = -1/(r*(r+1)) := by
  pm_1614
  have hp : r+1 ≠ 0 := by linarith
  unfold heathBrownPairSecant heathBrownPairK heathBrownPairIntercept heathBrownPairRight
  field_simp
  ring

theorem heathBrownPairSecant_join (hr : 3 ≤ r) :
    heathBrownPairSecant (r+1) (heathBrownPairRight r) =
      heathBrownPairSecant r (heathBrownPairRight r) := by
  rw [← heathBrownPairLeft_succ,heathBrownPairSecant_left (by linarith : 3 ≤ r+1),
    heathBrownPairLeft_succ,heathBrownPairSecant_right hr]
  congr 1
  ring
end

section
variable {r s : ℝ}
include r s
theorem heathBrownPairK_antitone (hr : 3 ≤ r) (hrs : r ≤ s) :
    heathBrownPairK s ≤ heathBrownPairK r := by
  pm_1074 hm hp
  have hsq : (r-1)^2 ≤ (s-1)^2 := by nlinarith
  have hden : (r-1)^2*(r+2) ≤ (s-1)^2*(s+2) :=
    mul_le_mul hsq (by linarith) hp.le (sq_nonneg _)
  unfold heathBrownPairK
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden

theorem heathBrownPairRight_mono (hr : 2 ≤ r) (hrs : r ≤ s) :
    heathBrownPairRight r ≤ heathBrownPairRight s := by
  have hp : 0 < r+1 := by linarith
  have hq : 0 < s+1 := by linarith
  unfold heathBrownPairRight
  apply (div_le_div_iff₀ hp hq).mpr
  have hprod : 0 ≤ (s-r)*(r*s+r+s-1) := by
    have hrs0 : 0 ≤ r*s := mul_nonneg (by linarith) (by linarith)
    exact mul_nonneg (by linarith) (by linarith)
  nlinarith only [hprod]

theorem heathBrownPairLeft_mono (hr : 3 ≤ r) (hrs : r ≤ s) :
    heathBrownPairLeft r ≤ heathBrownPairLeft s := by
  have h := heathBrownPairRight_mono (r:=r-1) (s:=s-1) (by linarith) (by linarith)
  have hrw : heathBrownPairLeft r = heathBrownPairRight (r-1) := by
    simpa only [sub_add_cancel] using heathBrownPairLeft_succ (r:=r-1)
  have hsw : heathBrownPairLeft s = heathBrownPairRight (s-1) := by
    simpa only [sub_add_cancel] using heathBrownPairLeft_succ (r:=s-1)
  rwa [hrw,hsw]
end

section
variable {r : ℝ} (hr : 3 ≤ r)
include r hr
theorem heathBrownPairLeft_half :
    r/2 ≤ heathBrownPairLeft r := by
  unfold heathBrownPairLeft
  apply (le_div_iff₀ (show 0 < r by linarith)).mpr
  nlinarith [sq_nonneg (r-2)]

theorem heathBrownPairRight_lower :
    r-1 ≤ heathBrownPairRight r := by
  unfold heathBrownPairRight
  apply (le_div_iff₀ (show 0 < r+1 by linarith)).mpr
  nlinarith
end

end TaoTrudgianYang2025
