module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform
public import OAI.NumberTheory.DirichletL.Descent.WindowFourier
public import OAI.NumberTheory.DirichletL.Descent.DescentHeight
public import OAI.NumberTheory.DirichletL.Descent.FullProfile

@[expose] public section

namespace OAI

namespace SevenEighths.InverseAmbientProfileTower
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open SevenEighths.InverseMoment
noncomputable section

abbrev Ambient (ι : Type*) := Frequency × (ι → ℝ)

def ambientWeight {ι } [Fintype ι] (J : ℕ) (p : Ambient ι)  :=
  ((1 + ‖p.1.1‖)^J * (1 + ‖p.1.2.1‖)^J * (1 + ‖p.1.2.2‖)^J) *
    ∏ i, (1 + ‖p.2 i‖)^J

section
variable {ι : Type*} [Fintype ι]
include ι

section
variable (J : ℕ) (p : Ambient ι)
include J p

theorem ambientWeight_eq_pow         :
    ambientWeight J p = (ambientWeight 1 p)^J := by
  simp [ambientWeight, mul_pow, Finset.prod_pow]

theorem ambientWeight_one_le         :
    1 ≤ ambientWeight J p := by
  unfold ambientWeight
  exact one_le_mul_of_one_le_of_one_le
    ((by bound))
    (Finset.one_le_prod₀ (fun i _ => one_le_pow₀ (by linarith [norm_nonneg (p.2 i)])))

end

theorem ambientWeight_add     (J K : ℕ) (p : Ambient ι) :
    ambientWeight (J + K) p = ambientWeight J p * ambientWeight K p := by
  grind [ambientWeight_eq_pow]

end

def inheritedLeft {ι } (i : ι) (p : Ambient ι)  :=
  p.2 i + p.1.1 - p.1.2.2

def inheritedRight {ι } (i : ι) (p : Ambient ι)  :=
  -(p.2 i + p.1.2.1 - p.1.2.2)

private theorem one_add_norm_add_le (x y : ℝ) :
    1 + ‖x + y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
  have h := norm_add_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  nlinarith [mul_nonneg hx hy]

section
variable {ι : Type*} [Fintype ι]
include ι

section
variable (i : ι)
include i

private theorem coordinate_factor_le    
      (u : ι → ℝ) :
    1 + ‖u i‖ ≤ ∏ j, (1 + ‖u j‖) :=
  by
  have hm (j : ι) : max (1 + ‖u j‖) 1 = 1 + ‖u j‖ :=
    max_eq_left (by linarith [norm_nonneg (u j)])
  simpa only [hm] using
    Finset.le_prod_max_one (Finset.mem_univ i) (fun j => 1 + ‖u j‖)

section
variable (p : Ambient ι)
include p

theorem inheritedLeft_bound         :
    1 + ‖inheritedLeft i p‖ ≤ ambientWeight 1 p := by
  have h := (one_add_norm_add_le (p.2 i + p.1.1) (-p.1.2.2)).trans
    (mul_le_mul_of_nonneg_right (one_add_norm_add_le (p.2 i) p.1.1) (by positivity))
  simp only [norm_neg, ← sub_eq_add_neg] at h
  have hc := coordinate_factor_le i p.2
  have ht : (1 + ‖p.1.1‖) * (1 + ‖p.1.2.2‖) ≤
      (1 + ‖p.1.1‖) * (1 + ‖p.1.2.1‖) * (1 + ‖p.1.2.2‖) := by
    nlinarith [norm_nonneg p.1.1, norm_nonneg p.1.2.1, norm_nonneg p.1.2.2,
      mul_nonneg (mul_nonneg (show 0 ≤ 1 + ‖p.1.1‖ by positivity)
        (norm_nonneg p.1.2.1)) (show 0 ≤ 1 + ‖p.1.2.2‖ by positivity)]
  have hh := mul_le_mul hc ht (by positivity)
    (Finset.prod_nonneg (fun j _ => by positivity))
  change _ ≤ (∏ j, (1 + ‖p.2 j‖)) * _ at hh
  exact h.trans (by simpa [ambientWeight, inheritedLeft, mul_comm, mul_left_comm, mul_assoc] using hh)

theorem inheritedRight_bound         :
    1 + ‖inheritedRight i p‖ ≤ ambientWeight 1 p := by
  have h := inheritedLeft_bound i ((p.1.2.1, p.1.1, p.1.2.2), p.2)
  change 1 + ‖-(p.2 i + p.1.2.1 - p.1.2.2)‖ ≤ _
  rw [norm_neg]
  grind [inheritedLeft, ambientWeight]

end

end

theorem inherited_pair_weight_bound    
    (i j : ι)  J K   p  :
    ambientWeight J p * ((1 + ‖inheritedLeft i p‖)^K *
      (1 + ‖inheritedRight j p‖)^K) ≤ ambientWeight (J + 2*K) p := by
  have h₁ := pow_le_pow_left₀ (by positivity) (inheritedLeft_bound i p) K
  have h₂ := pow_le_pow_left₀ (by positivity) (inheritedRight_bound j p) K
  have hh := mul_le_mul h₁ h₂ (by positivity)
    (pow_nonneg (le_trans zero_le_one (ambientWeight_one_le 1 p)) K)
  rw [← pow_add] at hh
  rw [ambientWeight_add, ambientWeight_eq_pow (2*K)]
  exact mul_le_mul_of_nonneg_left (by simpa [two_mul] using hh)
    (le_trans zero_le_one (ambientWeight_one_le J p))

end

def twistedFullDensity {ι } [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (θ : ℝ × ℝ) (p : Ambient ι)  :=
  fullProfileDensity g (𝓕 (frequencyTwist g₁ θ.1))
    (𝓕 (frequencyTwist g₂ θ.2)) b₃ p

theorem fullProfileDensity_weighted_integrable  {ι}  [Fintype ι]
     g   b₁ b₂ b₃   J  :
    Integrable (fun p : Ambient ι =>
      ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖) := by
  convert (tripleCoefficient_weighted_integrable b₁ b₂ b₃ J).mul_prod
    (coordinate_density_weighted_integrable g J) using 1
  funext p
  simp only [ambientWeight, fullProfileDensity, norm_mul]
  ring

section
variable (p : Ambient (Fin 9))
include p

theorem first_inherited_left_eq   :
    inheritedLeft 7 p = profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 7 := by
  simp [inheritedLeft, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

theorem first_inherited_right_eq   :
    inheritedRight 8 p = -profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 8 := by
  simp [inheritedRight, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

end

section
variable (p : Ambient (Fin 6))
include p

theorem second_inherited_left_eq   :
    inheritedLeft 4 p = profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 4 := by
  simp [inheritedLeft, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

theorem second_inherited_right_eq   :
    inheritedRight 5 p = -profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 5 := by
  simp [inheritedRight, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

end

end
end SevenEighths.InverseAmbientProfileTower

end OAI
