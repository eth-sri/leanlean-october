module

public import HypoellipticAleksandrov.Parabolic.Transposition.Integration
public import HypoellipticAleksandrov.Parabolic.Transposition.Modulus
import Mathlib

/-! # Smooth minima of barriers

The second-order chain rule shows that the smooth minimum inherits the generator
inequality, without differentiating the meeting surface of the two barriers.
-/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity Set
open scoped ContDiff
variable {d k : ℕ}

def blend (a b : ℝ) (f g : TimeVelocity d → ℝ) (z) := a * f z + b * g z

private theorem blend_sm (a b : ℝ) {f g : TimeVelocity d → ℝ} (hf : Sm f) (hg : Sm g) : Sm (blend a b f g) :=
  (contDiff_const.mul hf).add (contDiff_const.mul hg)

private theorem along_blend (v : Vector d) (a b : ℝ) {f g : TimeVelocity d → ℝ} (hf : Sm f) (hg : Sm g) :
    along v (blend a b f g) = blend a b (along v f) (along v g) := by
  funext z; unfold blend
  rw [along_add _ (contDiff_const.mul hf) (contDiff_const.mul hg)]
  have h (a : ℝ) (f : TimeVelocity d → ℝ) (hf : Sm f) : along v (fun y => a * f y) z = a * along v f z := by
    simp only [along,pd,fderiv_const_mul (hf.differentiable (by simp) _),smul_apply,smul_eq_mul,mul_left_comm,Finset.mul_sum]
  rw [h _ _ hf,h _ _ hg]

variable (X : Fin (k+1) → Vector d)

theorem generator_sm {f : TimeVelocity d → ℝ} (hf : Sm f) : Sm (generator X f) :=
  (along_sm _ hf).add (ContDiff.sum fun i _ => along_sm _ (along_sm _ hf))

private theorem generator_blend (a b : ℝ) {f g : TimeVelocity d → ℝ} (hf : Sm f) (hg : Sm g) (z) :
    generator X (blend a b f g) z = a * generator X f z + b * generator X g z := by
  simp only [generator,along_blend _ _ _ hf hg,along_blend _ _ _ (along_sm _ hf) (along_sm _ hg),blend,
    Finset.sum_add_distrib,← Finset.mul_sum]; ring

private theorem generator_comp {f : TimeVelocity d → ℝ} {P : ℝ → ℝ} (hf : Sm f) (hP : Sm P) (z) :
    generator X (P ∘ f) z = deriv P (f z) * generator X f z +
      deriv (deriv P) (f z) * ∑ i : Fin k, (along (X i.succ) f z)^2 := by
  have sq (v : Vector d) : along v (along v (P ∘ f)) z = deriv P (f z)*along v (along v f) z +
      deriv (deriv P) (f z) * (along v f z)^2 := by
    have hd := (contDiff_infty_iff_deriv.mp hP).2
    rw [show along v (P ∘ f) = _ from funext (along_comp v hf hP)]
    erw [along_mul v (hd.comp hf) (along_sm _ hf),along_comp v hf hd]; dsimp; ring
  simp only [generator,sq, along_comp _ hf hP,Finset.sum_add_distrib,← Finset.mul_sum]; ring

def lowerEnvelope (ε : ℝ) (f g : TimeVelocity d → ℝ) := blend (1/2) (-(1/2)) (blend 1 1 f g)
  (modulus ε ∘ blend 1 (-1) f g)

theorem envelope_sm {ε : ℝ} (he : 0 < ε) {f g : TimeVelocity d → ℝ} (hf : Sm f) (hg : Sm g) :
    Sm (lowerEnvelope ε f g) := blend_sm _ _ (blend_sm _ _ hf hg) ((sm_modulus he).comp (blend_sm _ _ hf hg))

theorem envelope_bounds {ε : ℝ} (he : 0 < ε) (f g : TimeVelocity d → ℝ) (z) :
    min (f z) (g z) ≤ lowerEnvelope ε f g z ∧ lowerEnvelope ε f g z ≤ min (f z) (g z) + ε := by
  have h := (modulus_bounds he (f z-g z)).2
  simp only [lowerEnvelope,blend,one_mul,neg_mul,Function.comp_apply,← sub_eq_add_neg]
  rcases le_total (f z) (g z) with H | H
  · rw [min_eq_left H]; rw [abs_of_nonpos (sub_nonpos.mpr H)] at h; constructor <;> linarith
  · rw [min_eq_right H]; rw [abs_of_nonneg (sub_nonneg.mpr H)] at h; constructor <;> linarith

theorem generator_envelope {ε : ℝ} (he : 0 < ε) {f g : TimeVelocity d → ℝ} (hf : Sm f) (hg : Sm g)
    {M : ℝ} (z) (h1 : generator X f z ≤ M) (h2 : generator X g z ≤ M) :
    generator X (lowerEnvelope ε f g) z ≤ M := by
  let w := blend 1 (-1) f g
  have hnn : 0 ≤ deriv (deriv (modulus ε)) (w z) * ∑ i : Fin k, (along (X i.succ) w z)^2 :=
    mul_nonneg (modulus_convex he _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hs := abs_le.mp (slope_bound he (w z))
  change generator X (blend _ _ _ (modulus ε ∘ w)) z ≤ _
  rw [generator_blend _ _ _ (blend_sm _ _ hf hg) ((sm_modulus he).comp (blend_sm _ _ hf hg)),
    generator_comp _ (blend_sm _ _ hf hg) (sm_modulus he),generator_blend _ _ _ hf hg,
    show generator X w z = _ from generator_blend X 1 (-1) hf hg z]
  nlinarith only [hnn, mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hs.2),
    mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ 1 + deriv (modulus ε) (w z) by linarith only [hs.1])]

end HypoellipticAleksandrov.Parabolic.Transposition
