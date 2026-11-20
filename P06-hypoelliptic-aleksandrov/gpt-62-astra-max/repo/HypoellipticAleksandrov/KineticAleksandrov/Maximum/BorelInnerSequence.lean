module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # A concrete reflected inner-cylinder exhaustion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology

variable {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (n : ℕ)

include R n in
/-- A valid inner error scale for every natural index, starting at zero. -/
def borelInnerDelta : ℝ := R ^ 2 / (4 * ((n : ℝ) + 1))

include hR in
/-- Every scale is positive and below half the original time depth. -/
theorem borelInnerDelta_valid :
    0 < borelInnerDelta R n ∧ borelInnerDelta R n < R ^ 2 / 2 := by
  have hn : 0 ≤ n := Nat.cast_nonneg n
  have hd : 0 < 4 * ((n : ℝ) + 1) := by positivity
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  refine ⟨div_pos hR2 hd,?_⟩
  rw [borelInnerDelta,div_lt_iff₀ hd]
  nlinarith only [hn,hR2]

/-- The scale tends to zero with the centre and original radius fixed. -/
theorem borelInnerDelta_tendsto :
    Tendsto (borelInnerDelta R) atTop (𝓝 0) := by
  have heq : borelInnerDelta R = fun (n : ℕ) => R ^ 2 / 4 * (1 / (n + 1)) := by
    funext n
    simp only [borelInnerDelta]
    field_simp
  rw [heq]
  convert! tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (R ^ 2 / 4) using 1
  simp

include hR n in
/-- Radius of the concrete reflected inner cylinder. -/
def borelInnerRadius : ℝ :=
  innerRatio R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2 * R

/-- Positivity holds at every index, without discarding the first cylinder. -/
theorem borelInnerRadius_pos :
    0 < borelInnerRadius R hR n :=
  mul_pos (innerRatio_spec R hR _ (borelInnerDelta_valid R hR n).1
    (borelInnerDelta_valid R hR n).2).1 hR

/-- The inner radii tend to the original radius, including arbitrary real powers later. -/
theorem borelInnerRadius_tendsto :
    Tendsto (borelInnerRadius R hR) atTop (𝓝 R) := by
  have ht := ((tendsto_const_nhds (x := 1)).sub
    (((borelInnerDelta_tendsto R).const_mul 2).div_const (R ^ 2)))
  have ht' : Tendsto (fun n => 1 - 2 * borelInnerDelta R n / R ^ 2)
      atTop (𝓝 1) := by simpa using ht
  have hs := (Real.continuous_sqrt.tendsto 1).comp ht'
  change Tendsto (fun n => Real.sqrt (1 - 2 * borelInnerDelta R n / R ^ 2) * R)
    atTop (𝓝 R)
  simpa using hs.mul_const R

include P₀ R n in
/-- The source shifted backward centre for the concrete sequence. -/
def borelInnerCentre : KineticPoint d :=
  ⟨P₀.time - borelInnerDelta R n,
    P₀.position - borelInnerDelta R n • P₀.velocity,P₀.velocity⟩

/-- Every backward interior point eventually lies in the shifted inner cylinders. -/
theorem borel_inner_exhaustion
    (P : KineticPoint d) (hP : P ∈ backwardCylinder P₀ R) :
    ∀ᶠ n in atTop, P ∈ backwardCylinder (borelInnerCentre P₀ R n) (borelInnerRadius R hR n) := by
  have hP' : kineticReflection P ∈ forwardCylinder (kineticReflection P₀) R hR := by
    rw [← kineticReflection_image_backwardCylinder P₀ R hR]
    exact mem_image_of_mem _ hP
  obtain ⟨η,hη,hmem⟩ := innerCylinder_exhaustion (kineticReflection P₀) R hR
    (kineticReflection P) hP'
  filter_upwards [((tendsto_order.mp (borelInnerDelta_tendsto R)).2 η hη)] with n hn
  have hm := hmem (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2 hn
  change P ∈ backwardCylinder
    ⟨P₀.time - borelInnerDelta R n,P₀.position - borelInnerDelta R n • P₀.velocity,
      P₀.velocity⟩ (borelInnerRadius R hR n)
  unfold borelInnerRadius
  rw [← kineticReflection_image_innerCylinder P₀ R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2]
  exact ⟨kineticReflection P,hm,kineticReflection_involutive P⟩

end HypoellipticAleksandrov.KineticAleksandrov
