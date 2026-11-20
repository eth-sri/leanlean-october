module
public import Glennie.ObservationData
public import Glennie.Compact.ReadoutRobustnessR01
public import Glennie.Compact.NativeNormKernelR01
public import Glennie.Compact.MultiplicationDefectR01
public import Glennie.Compact.NormCompatibleNullTargetR01
public import Glennie.Theorems.Frames

/-! Specialize the transport estimate once, then use the common frame radius
and readout error for both special targets. -/
@[expose] public section
namespace Glennie.SubmissionR03
open Compact.MultiplicationDefectR01 Compact.CyclicTraceNullR01 Compact.NativeNormKernel
open Compact.NormCompatibleNullTargetR01 Compact.ReadoutRobustnessR01
open Compact.Affine20
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
theorem nA_eq (x : Albert) : nA x = ‖x‖ := by rw [nA, ← native_norm_sq, Real.sqrt_sq (norm_nonneg x)]
private abbrev Eucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
private def diagJ (n : ℕ) : Product (Eucl n) := LinearMap.mk₂ ℝ diagonalNProduct
  (by intros; ext; apply add_mul) (by intros; ext; apply mul_assoc)
  (by intros; ext; apply mul_add) (by intros; ext; apply mul_left_comm)
private theorem diagQ {n} (a b : Eucl n) : Q (diagJ n) a b = diagJ n a (diagJ n a b) := by
  ext i; change 2*(a i*(a i*b i)) - (a i*a i)*b i = _; change _ = a i*(a i*b i); ring
private theorem diagNull {n} (a b c : Eucl n) : response (diagJ n) a b c = 0 := by
  have h : Q (diagJ n) a (Q (diagJ n) b c) = Q (diagJ n) b (Q (diagJ n) a c) := by
    simp only [diagQ]; ext i; change a i*(a i*(b i*(b i*c i))) = b i*(b i*(a i*(a i*c i))); ring
  change Inner.inner ℝ (Q (diagJ n) a (Q (diagJ n) b c) - Q (diagJ n) b (Q (diagJ n) a c)) _ = 0; simp only [h,sub_self,_root_.inner_zero_left]
private theorem diagNorm {n : ℕ} (a b : Eucl n) :
    ‖diagonalNProduct a b‖ ≤ ‖a‖ * ‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq (diagonalNProduct a b),
    EuclideanSpace.real_norm_sq_eq b, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have ha : (a i)^2 ≤ ‖a‖^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg (a i)) (norm_nonneg a)).mpr
      (PiLp.norm_apply_le a i)
    simp_all
  change (a i*b i)^2 ≤ ‖a‖^2 * (b i)^2
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)

private theorem diagQnorm {n} (a b : Eucl n) : ‖Q (diagJ n) a b‖ ≤ ‖a‖^2 * ‖b‖ := by
  rw [diagQ]; change ‖diagonalNProduct a (diagonalNProduct a b)‖ ≤ _
  grw [diagNorm,diagNorm]; exact le_of_eq (by ring)

private def RadiusBound (μ R : ℝ) := ∀ x y z : Albert, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖z‖ ≤ R → |phi x y z| ≤ 38*μ*R^9
private theorem natQ (a b : Albert) : Q jordanLinear a b = U a b := rfl
private theorem natPhi (x y z : Albert) : response jordanLinear x y z = phi x y z := by
  simp [response,phiWith,phi,U,quadraticWith,hilbert_inner_eq_native]

private theorem radius {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (j : Product E) (f : Albert →ₗᵢ[ℝ] E) (hj : ∀ a b, ‖j a b‖ ≤ ‖a‖*‖b‖)
    (hq : ∀ a b, ‖Q j a b‖ ≤ ‖a‖^2*‖b‖) (hn : ∀ x y z, response j x y z = 0)
    {μ R : ℝ} (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hd : ∀ a b : Albert, ‖f (jordan a b) - j (f a) (f b)‖ ≤ μ*‖a‖*‖b‖) : RadiusBound μ R := by
  intro x y z hx hy hz
  have hA : ∀ a b : Albert, ‖jordanLinear a b‖ ≤ ‖a‖*‖b‖ := jordan_norm
  have hU : ∀ a b : Albert, ‖Q jordanLinear a b‖ ≤ ‖a‖^2*‖b‖ := by simpa only [natQ] using U_norm
  have h := response_discrepancy_radius jordanLinear j f hA hj hU hq μ hμ hd R hR x y z hx hy hz
  simpa only [natPhi,hn,sub_zero] using h

private theorem measured {μ ε : ℝ} (hb : RadiusBound μ (Real.sqrt 2)) (T : Triple)
    (hT : ∀ a, Frame (T a)) (noisy : Readouts) (he : ErrorsAtMost noisy (exactReadouts T) ε) :
    (|weightedScore noisy| - 12*ε)/(1216*Real.sqrt 2) ≤ μ := by
  have rad (a) : ‖encoder (T a)‖ ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by rw [native_norm_sq,frame_encoder_norm _ (hT a)])
  have h : |phiOf T| ≤ 38*μ*(Real.sqrt 2)^9 := hb _ _ _ (rad f0) (rad f1) (rad f2)
  have err := weightedScore_error noisy _ ε he
  rw [weightedScore_eq_two_phi] at err
  rw [show (Real.sqrt (2:ℝ))^9 = 16 * Real.sqrt 2 by grind] at h
  apply (div_le_iff₀ (by positivity : 0 < 1216*Real.sqrt (2:ℝ))).mpr; grind

/-- A uniform all-input defect bounds the degree-nine scalar on any
radius-bounded triple for every finite coordinatewise Euclidean target. -/
theorem diagonalN_defect_response_radius {n : ℕ}
    (f : Albert →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x : Albert, ‖f x‖ = nA x)
    (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤
        μ * nA a * nA b)
    (x y z : Albert) (hx : nA x ≤ R) (hy : nA y ≤ R)
    (hz : nA z ≤ R) :
    |phi x y z| ≤ 38 * μ * R^9 := by
  simp only [nA_eq] at hf hdef hx hy hz
  exact radius (diagJ n) ⟨f,hf⟩ diagNorm diagQnorm diagNull hμ hR hdef x y z hx hy hz

/-- An actual-frame noisy score forces a uniform multiplication defect for
any norm-preserving linear map into a coordinatewise Euclidean target. -/
theorem frame_noisy_diagonalN_defect_lower {n : ℕ}
    (f : Albert →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x : Albert, ‖f x‖ = nA x)
    (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤
        μ * nA a * nA b) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  simp only [nA_eq] at hf hdef
  exact measured (radius (diagJ n) ⟨f,hf⟩ diagNorm diagQnorm diagNull hμ (Real.sqrt_nonneg 2) hdef) T hT noisy hreadout

/-- A noisy actual-frame score also forces a defect for an associative
cyclic-trace represented target with its exact product and metric adapters. -/
theorem frame_noisy_represented_defect_lower
    {E N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedRing N] [NormedAlgebra ℝ N]
    (jE : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (f : Albert →ₗ[ℝ] E) (hf : ∀ x : Albert, ‖f x‖ = nA x)
    (ρ : E →ₗᵢ[ℝ] N) (τ : N →ₗ[ℝ] ℝ)
    (hj : ∀ a b : E, ρ (jE a b) =
      (1 / 2 : ℝ) • (ρ a * ρ b + ρ b * ρ a))
    (hB : ∀ a b : E, Inner.inner ℝ a b = τ (ρ a * ρ b))
    (hcyclic : ∀ a b : N, τ (a * b) = τ (b * a))
    (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - jE (f a) (f b)‖ ≤ μ * nA a * nA b) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  simp only [nA_eq] at hf hdef
  let j := fun a b => jE a b
  exact measured (radius jE ⟨f,hf⟩ (represented_product_norm j ρ hj) (represented_quadratic_norm j ρ hj)
    (phiWith_eq_zero_of_compatible_trace j _ ρ.toLinearMap τ hj hB hcyclic) hμ (Real.sqrt_nonneg 2) hdef) T hT noisy hreadout

end
end Glennie.SubmissionR03
