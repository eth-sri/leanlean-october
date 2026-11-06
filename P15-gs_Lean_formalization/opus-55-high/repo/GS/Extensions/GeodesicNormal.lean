module

public import GS.Extensions.MatrixCalculus
public import GS.Extensions.TwoFactorProjection

@[expose] public section


/-!
# Extrinsic geodesic certificates without a covering-space theorem

The conclusions below are actual second
velocity identities and Frobenius normality, not a redefinition of intrinsic
geodesics. The bridge from the derivative image to the tangent bundle of a
smooth embedded orbit remains a separate obligation.

The two coordinate block relations must intersect only on the diagonal.
No such claim is made for the singular general three-factor family.
-/

noncomputable section
open Matrix
namespace GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

 def OffDiagonalDisjoint (a b : Fin n → ℕ) : Prop :=
  ∀ i j, a i = a j → b i = b j → i = j

 theorem frobInner_disjoint_supported_skew {a b : Fin n → ℕ}
    (hab : OffDiagonalDisjoint a b) (A K : Mat n)
    (hA : Supported a A) (hK : Supported b K) (hk : IsSkew K) :
    frobInner A K = 0 := by
  refine frobInner_eq_zero_of_disjoint _ _ fun i j => ?_
  by_cases ha : a i = a j <;> by_cases hb : b i = b j
  · exact .inr (hab i j ha hb ▸ isSkew_diagonal_zero hk i)
  all_goals simp_all [Supported]

 theorem symmetric_skew_inner_zero {S K : Mat n}
    (hS : Sᵀ = S) (hK : IsSkew K) : frobInner S K = 0 := by
  have ht := frobInner_transpose S K
  rw [hS, hK, frobInner_comm, frobInner_neg_left, frobInner_comm] at ht
  linarith

 def accelerationCore (C K : Mat n) : Mat n := C*C + (2:ℝ) • (C*K) + K*K

 theorem lifted_acceleration_normal {a b : Fin n → ℕ}
    (hab : OffDiagonalDisjoint a b) (L R C K D E : Mat n)
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hCa : Supported a C) (hKb : Supported b K)
    (hDa : Supported a D) (hEb : Supported b E)
    (hC : IsSkew C) (hK : IsSkew K) (hD : IsSkew D) (hE : IsSkew E) :
    frobInner (lift L R (accelerationCore C K)) (lift L R (D+E)) = 0 := by
  have hDE := isSkew_add hD hE
  have hsq {C : Mat n} (hC : IsSkew C) : (C*C)ᵀ = C*C := by
    change Cᵀ = -C at hC
    simp_all
  rw [lift_frobInner L R _ _ hL hR, accelerationCore, frobInner_add_left, frobInner_add_left, frobInner_smul_left,
    symmetric_skew_inner_zero (hsq hC) hDE, symmetric_skew_inner_zero (hsq hK) hDE, frobInner_add_right,
    frobInner_mul_left, frobInner_comm, frobInner_disjoint_supported_skew hab _ K (hCa.transpose.mul hDa) hKb hK,
    frobInner_mul_right, frobInner_comm, frobInner_disjoint_supported_skew (fun i j h h' => hab i j h' h) _ C (hEb.mul hKb.transpose) hCa hC]
  ring

/-- The product curve satisfies the expected velocity formula whenever the
factors satisfy the usual constant-generator ODEs. -/
 theorem product_curve_velocity (L R : ℝ → Mat n) (C K : Mat n) (t : ℝ)
    (hL : HasDerivAt L (L t*C) t) (hR : HasDerivAt R (K*R t) t) :
    HasDerivAt (fun s => L s*R s) (lift (L t) (R t) (C+K)) t := by
  simpa only [lift, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using Shared.hasDerivAt_matrix_mul hL hR

/-- Differentiating that velocity gives a genuine HasDerivAt certificate for
acceleration. This lemma does not assume or assert a manifold structure. -/
 theorem product_curve_acceleration (L R : ℝ → Mat n) (C K : Mat n) (t : ℝ)
    (hL : HasDerivAt L (L t*C) t) (hR : HasDerivAt R (K*R t) t) :
    HasDerivAt (fun s => lift (L s) (R s) (C+K))
      (lift (L t) (R t) (accelerationCore C K)) t := by
  convert Shared.hasDerivAt_matrix_mul (Shared.hasDerivAt_matrix_mul hL (hasDerivAt_const t (C+K))) hR using 1
  · rfl
  ext i j
  simp [lift, accelerationCore, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  ring

end GS.Extensions
