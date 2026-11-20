module

public import RequestProject.NeumannH1Multiplier

/-!
# Affine multiplication in the actual weak-gradient H¹ space

Multiplication by `z-p` is constructed from the genuine L² multiplier and
the weak product rule. Testing against `(z-p)φ` proves gradient membership
for arbitrary H¹ inputs. A supplied physical bound gives an explicit H¹
operator norm; boundedness of the domain supplies such a bound at every p.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real Filter
open scoped ComplexConjugate InnerProductSpace Topology

private theorem affine_derivative (p z : ℂ) (i : Fin 2) :
    fderiv ℝ (fun w : ℂ => w - p) z (coordDir i) = coordDir i :=
  congrFun (congrArg DFunLike.coe ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const p).fderiv) _

def affineCoefficient {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) : H1Coefficient Ω where
  toFun z := z - p
  smooth := contDiff_id.sub contDiff_const
  bound := max B 1
  bound_nonneg := le_trans zero_le_one (le_max_right _ _)
  value_bound z hz := (hB z hz).trans (le_max_left _ _)
  derivative_bound i z _ := by simp_all [affine_derivative, norm_coordDir]

/-- The actual affine coefficient multiplier in physical L². -/
def neumannAffineL2Multiplier {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) : L2 Ω →L[ℂ] L2 Ω :=
  h1CoefficientL2 Ω (affineCoefficient p hB)

theorem neumannAffineL2Multiplier_ae {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : L2 Ω) :
    (neumannAffineL2Multiplier p hB u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => (z - p) * u z :=
  h1CoefficientL2_ae Ω (affineCoefficient p hB) u

/-- Every bounded actual domain has a genuine affine coefficient bound. -/
theorem exists_neumannAffine_bound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (p : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ Ω, ‖z - p‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := hb.subset_ball_lt 0 p
  refine ⟨B, hB0.le, fun z hz => ?_⟩
  have h : ‖z - p‖ < B := by
    grind [mem_ball, dist_eq_norm]
  gcongr

def neumannH1AffineBound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (p : ℂ) : ℝ :=
  Classical.choose (exists_neumannAffine_bound hb p)

theorem neumannH1AffineBound_spec {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (p : ℂ) :
    ∀ z ∈ Ω, ‖z - p‖ ≤ neumannH1AffineBound hb p :=
  (Classical.choose_spec (exists_neumannAffine_bound hb p)).2

/-- Multiplication by `z-p` on the actual H¹ space of any bounded domain. -/
def neumannH1AffineMultiplier {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (p : ℂ) :
    NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  neumannH1CoefficientMultiplier Ω (affineCoefficient p (neumannH1AffineBound_spec hb p))

theorem h1Value_neumannH1AffineMultiplier {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) :
    h1Value Ω (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Value Ω u) :=
  h1Value_neumannH1CoefficientMultiplier Ω _ u

theorem h1Gradient_neumannH1AffineMultiplier {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Gradient Ω i u) +
        coordDir i • h1Value Ω u :=
  by
    rw [neumannH1AffineMultiplier, h1Gradient_neumannH1CoefficientMultiplier]
    congr 1
    apply Lp.ext
    filter_upwards [h1CoefficientDerivativeL2_ae Ω
      (affineCoefficient p (neumannH1AffineBound_spec hb p)) i (h1Value Ω u),
      Lp.coeFn_smul (coordDir i) (h1Value Ω u)] with z ha hs
    rw [ha, hs]
    exact congrArg (· * h1Value Ω u z) (affine_derivative p z i)

theorem h1Gradient_neumannH1AffineMultiplier_x {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) :
    h1Gradient Ω 0 (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Gradient Ω 0 u) +
        h1Value Ω u := by
  simpa only [show coordDir 0 = (1 : ℂ) from rfl, one_smul] using
    h1Gradient_neumannH1AffineMultiplier hb p u 0

theorem h1Gradient_neumannH1AffineMultiplier_y {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) :
    h1Gradient Ω 1 (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Gradient Ω 1 u) +
        Complex.I • h1Value Ω u := by
  simpa only [show coordDir 1 = Complex.I from rfl] using
    h1Gradient_neumannH1AffineMultiplier hb p u 1

end PolyaNeumann
