module

public import GS.Shared.Directions

public import GS.Shared.Frobenius

public import GS.Shared.Permutation

public import GS.GlobalGeometry.ExactSharing

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

public import Mathlib.Analysis.SpecialFunctions.Exponential

public import Mathlib.Tactic.NoncommRing

@[expose] public section

noncomputable section
open Matrix NormedSpace
open scoped BigOperators
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open GS in
/-- Exact real tangent directions with the prescribed layer supports and ties. -/
def GSPalomar.RealDirections {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (X Z : Mat n) : Prop :=
  ∃ C Ω : Mat n,
    (BlockDiagonal b₂ C ∧ Cᵀ = -C ∧ GS.GlobalGeometry.TiedEntries b₂ τ₂ C) ∧
    (BlockDiagonal b₁ Ω ∧ Ωᵀ = -Ω ∧ GS.GlobalGeometry.TiedEntries b₁ τ₁ Ω) ∧
    Z = C * X + X * Ω

namespace GS.Shared

variable {n b : ℕ} {τ : ℕ → ℕ}

/-- Shared block algebras are closed under the convergent exponential series. -/
private theorem exp_shared (hd : b ∣ n) {A : Mat n}
    (hA : A ∈ sharedSkewSpace b τ) : SharedUnitaryFactor b τ (exp A) := by
  let : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℚ (Mat n) := Matrix.linftyOpNormedAlgebra
  let S := sharedAlgebra (𝕜 := ℝ) hd τ
  have he : exp A ∈ S :=
    exp_mem (R := ℝ) (s := S) S.toSubmodule.closed_of_finiteDimensional ⟨hA.1,hA.2.2⟩
  exact ⟨he.1, _root_.Unitary.mem_iff.mp (exp_mem_unitary_of_mem_skewAdjoint hA.2.1), he.2⟩

private theorem expSandwich_deriv (L R C Ω S : Mat n) (t : ℝ) :
    HasDerivAt (fun s => L * exp (s • C) * S * (exp (s • Ω) * R))
      (L * exp (t • C) * (C * S + S * Ω) * (exp (t • Ω) * R)) t := by
  have aux (L R C Ω S : OpMatrix ℝ n) :
      HasDerivAt (fun s => L * exp (s • C) * S * (exp (s • Ω) * R))
        (L * exp (t • C) * (C * S + S * Ω) * (exp (t • Ω) * R)) t := by
    have hL := (hasDerivAt_exp_smul_const C t).const_mul L
    have hR := (hasDerivAt_exp_smul_const' Ω t).mul_const R
    exact ((hL.mul_const S).mul hR).congr_deriv (by noncomm_ring)
  exact (asOp (𝕜 := ℝ) (n := n)).symm.hasFDerivAt.comp_hasDerivAt t (aux L R C Ω S)

private theorem frob_comm (A B : Mat n) : frobInner A B = frobInner B A := real_inner_comm _ _

private theorem frob_disjoint {f g : Fin n → ℕ} {A B : Mat n}
    (hfg : ∀ i j, f i = f j → g i = g j → i = j)
    (hA : CSupported f A) (hB : CSupported g B) (hsk : Bᴴ = -B) : frobInner A B = 0 := by
  rw [frobInner_eq_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases hf : f i = f j; swap
  · simp [hA i j hf]
  by_cases hg : g i = g j; swap
  · simp [hB i j hg]
  have := hfg i j hf hg
  subst j
  have h := congrFun (congrFun hsk i) i
  change B i i = -B i i at h
  simp [show B i i = 0 by linarith]

private theorem frob_sym_skew {A B : Mat n} (hA : Aᴴ = A) (hB : Bᴴ = -B) :
    frobInner A B = 0 := by
  have h := Matrix.trace_conjTranspose (Aᴴ * B)
  simp only [Matrix.conjTranspose_mul, star_trivial,
    hA, hB, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm B A] at h
  change -(A * B).trace = (A * B).trace at h
  rw [frobInner_eq_trace, hA]
  exact (show (A * B).trace = 0 by linarith)

private theorem frob_square_skew {A B : Mat n} (hA : Aᴴ = -A) (hB : Bᴴ = -B) :
    frobInner (A*A) B = 0 :=
  frob_sym_skew (by simp only [Matrix.conjTranspose_mul, hA, Matrix.neg_mul, Matrix.mul_neg, neg_neg]) hB

private theorem frob_mixed {f g : Fin n → ℕ} {C K D E : Mat n}
    (hfg : ∀ i j, f i = f j → g i = g j → i = j)
    (hC : CSupported f C) (hK : CSupported g K)
    (hD : CSupported f D) (hE : CSupported g E) (hc : Cᴴ = -C) (hk : Kᴴ = -K) :
    frobInner (C*K) (D+E) = 0 := by
  rw [frobInner_add_right, frobInner_mul_left C, frobInner_mul_right K, frob_comm K, frob_comm C]
  simp only [frob_disjoint hfg (hC.conjTranspose.mul hD) hK hk,
    frob_disjoint (fun i j hg hf => hfg i j hf hg) (hE.mul hK.conjTranspose) hC hc, add_zero]

open GS in
/-- The entire tangent image is normal to the acceleration, and the speed is
constant, for the actual tied exponential factors. -/
theorem _root_.GSPalomar.orthogonal_shared_block_geodesic {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (σ : Equiv.Perm (Fin n))
    (hno : Function.Injective (fun i : Fin n => (i.val / b₁, (σ i).val / b₂)))
    (L R C Ω : Mat n)
    (hL : GS.GlobalGeometry.SharedOrthogonalFactor b₂ τ₂ L)
    (hR : GS.GlobalGeometry.SharedOrthogonalFactor b₁ τ₁ R)
    (hC : GS.BlockDiagonal b₂ C ∧ Cᵀ = -C ∧ GS.GlobalGeometry.TiedEntries b₂ τ₂ C)
    (hΩ : GS.BlockDiagonal b₁ Ω ∧ Ωᵀ = -Ω ∧ GS.GlobalGeometry.TiedEntries b₁ τ₁ Ω) :
    let γ : ℝ → Mat n := fun t =>
      L * NormedSpace.exp (t • C) * GS.permMatrix σ * (NormedSpace.exp (t • Ω) * R)
    ∀ t : ℝ,
      GS.GlobalGeometry.InSharedA2Orth b₁ b₂ τ₁ τ₂ (GS.permMatrix σ) (γ t) ∧
      HasDerivAt γ (deriv γ t) t ∧
      HasDerivAt (deriv γ) (deriv (deriv γ) t) t ∧
      (∀ Z : Mat n, GSPalomar.RealDirections b₁ b₂ τ₁ τ₂ (γ t) Z →
        (∑ i, ∑ j, deriv (deriv γ) t i j * Z i j) = 0) ∧
      (∑ i, ∑ j, (deriv γ t i j)^2) =
        (∑ i, ∑ j, (C i j)^2) + (∑ i, ∑ j, (Ω i j)^2) := by
  intro γ
  let P := permMatrix (𝕜 := ℝ) σ
  let K := P * Ω * Pᴴ
  let l (t : ℝ) := L * exp (t • C)
  let r (t : ℝ) := exp (t • Ω) * R
  let V := C*P + P*Ω
  let M := C*V + V*Ω
  let v (t : ℝ) := l t * V * r t
  let a (t : ℝ) := l t * M * r t
  have hp : Unitary P := perm_unitary σ
  have hv t : HasDerivAt γ (v t) t := expSandwich_deriv L R C Ω P t
  have ha t : HasDerivAt v (a t) t := expSandwich_deriv L R C Ω V t
  have hKP : K*P = P*Ω := by simp only [K, Matrix.mul_assoc, hp.1, Matrix.mul_one]
  have hV : V = (C+K)*P := by rw [Matrix.add_mul, hKP]
  have hM : M = (C*(C+K)+(C+K)*K)*P := by
    simp only [M, hV, Matrix.add_mul, Matrix.mul_assoc, hKP]
    rw [← Matrix.mul_assoc K, hKP, Matrix.mul_assoc]
  rw [show deriv γ = v from funext fun t => (hv t).deriv,
      show deriv v = a from funext fun t => (ha t).deriv]
  have hfg (i j : Fin n) (hf : i.val / b₂ = j.val / b₂)
      (hg : (σ.symm i).val / b₁ = (σ.symm j).val / b₁) : i = j :=
    σ.symm.injective (hno (Prod.ext hg (by simpa using hf)))
  have hc : Cᴴ = -C := hC.2.1
  have hk : Kᴴ = -K := IsSkewHermitian.conjugate hΩ.2.1 P
  have hs {X : Mat n} (h : BlockDiagonal b₁ X) :
      CSupported (fun i => (σ.symm i).val / b₁) (P * X * Pᴴ) :=
    fun i j hij => (perm_conjugate_apply σ X i j).trans (h _ _ hij)
  have hks := hs hΩ.1
  have hk_sq : frobInner K K = frobInner Ω Ω := by
    rw [show K = P * Ω * Pᴴ from rfl, frobInner_right_unitary _ hp.conjTranspose,
      frobInner_left_unitary _ hp]
  have hck : frobInner C K = 0 := frob_disjoint hfg hC.1 hks hk
  intro t
  have hlt : SharedUnitaryFactor b₂ τ₂ (l t) := shared_factor_mul hd₂ hL
    (exp_shared hd₂ ((sharedSkewSpace b₂ τ₂).smul_mem t hC))
  have hrt : SharedUnitaryFactor b₁ τ₁ (r t) := shared_factor_mul hd₁
    (exp_shared hd₁ ((sharedSkewSpace b₁ τ₁).smul_mem t hΩ)) hR
  have hfr (U V : Mat n) : frobInner (l t * U * (P*r t)) (l t * V * (P*r t)) = frobInner U V := by
    rw [frobInner_right_unitary _ (hp.mul hrt.2.1), frobInner_left_unitary _ hlt.2.1]
  refine ⟨⟨l t,r t,hlt,hrt,rfl⟩,hv t,ha t,?_,?_⟩
  · rintro Z ⟨A,B,hA,hB,rfl⟩
    suffices frobInner (a t) (A * γ t + γ t * B) = 0 by simpa only [frobInner_eq_sum, star_trivial, RCLike.re_to_real] using this
    let D := (l t)ᴴ * A * (l t)ᴴᴴ
    let Y := r t * B * (r t)ᴴ
    let E := P * Y * Pᴴ
    have hd := sharedSkew_conjugate hd₂ (shared_factor_conjTranspose hlt) hA
    have hy := sharedSkew_conjugate hd₁ hrt hB
    have hde : (D+E)ᴴ = -(D+E) := skewHermitian_add hd.2.1 (IsSkewHermitian.conjugate hy.2.1 P)
    have hz : A * γ t + γ t * B = l t * (D+E) * (P*r t) := by
      change A * (l t * P * r t) + (l t * P * r t) * B = _
      simp only [D, E, Y, conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_assoc, hlt.2.1.mul_adjoint_cancel, hrt.2.1.1, Matrix.mul_one, hp.adjoint_mul_cancel]
    rw [hz, show a t = l t * (C*(C+K)+(C+K)*K) * (P*r t) by simp only [a, hM, Matrix.mul_assoc], hfr]
    have hmix : frobInner (C*K) (D+E) = 0 := frob_mixed hfg hC.1 hks hd.1 (hs hy.1) hc hk
    simp only [Matrix.mul_add, Matrix.add_mul, frobInner_add_left, frob_square_skew hc hde,
      frob_square_skew hk hde, hmix, add_zero]
  · suffices frobSq (v t) = frobSq C + frobSq Ω by simpa only [frobInner_eq_sum, star_trivial, RCLike.re_to_real, sq] using this
    rw [show v t = l t * (C+K) * (P*r t) by simp only [v, hV, Matrix.mul_assoc]]
    simp only [frobSq, hfr, frobInner_add_left, frobInner_add_right, hck,
      (frob_comm K C).trans hck, add_zero, zero_add, hk_sq]

end GS.Shared
