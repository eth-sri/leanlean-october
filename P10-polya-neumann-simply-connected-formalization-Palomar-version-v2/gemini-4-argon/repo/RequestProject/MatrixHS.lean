module

public import RequestProject.SobolevCircle

/-!
# Hilbert–Schmidt matrices on `ℓ²(ℤ)`

A square-summable matrix `a : ℤ × ℤ → ℂ` (`∑ |a_{m n}|² < ∞`) defines a bounded operator
`(T f)_m = ∑_n a_{m n} f_n` on `ℓ²(ℤ)` (`hsMatrixOp`), with `‖T‖² ≤ ∑ |a_{m n}|²`, and this operator
is compact (`isCompactOperator_hsMatrixOp`). This is the form in which the proof of Lemma 6.7
uses the weighted bound on the Fourier matrix of the corrected kernel: the normalized remainder
`Λ^{t+δ} (Λ^{1/2} R_E Λ^{1/2}) Λ^{-t}` has matrix entries
`λ_m^{1/2+t+δ} λ_n^{1/2-t} r_{m n}`, which are square summable for `0 ≤ t ≤ 1/2`, `0 ≤ δ < 1/2`
(`summable_mixed_correctedKernelCoeff`), so it is compact on `L²`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

variable (a : ℤ × ℤ → ℂ) (ha : Summable fun p => ‖a p‖ ^ 2)
include ha

/-- The (conjugated) `m`-th row of a square-summable matrix, as a vector of `ℓ²(ℤ)`. -/
def hsRow (m : ℤ) : L2Z :=
  ⟨fun n => conj (a (m, n)), memℓp_two_iff_summable.mpr (by
    simpa [Complex.norm_conj] using ha.prod_factor m)⟩

local notation "Φ0" => hsRow a ha

lemma hsRow_apply m n : (Φ0 m : ℤ → ℂ) n = conj (a (m, n)) := rfl

lemma norm_hsRow_sq m : ‖Φ0 m‖ ^ 2 = ∑' n, ‖a (m, n)‖ ^ 2 := by
  rw [norm_sq_L2Z]
  simp [hsRow_apply]

lemma summable_norm_hsRow_sq : Summable fun m => ‖Φ0 m‖ ^ 2 := by
  simp_rw [norm_hsRow_sq a ha]
  exact ha.prod

def hsMatrixLin : L2Z →ₗ[ℂ] L2Z where
  toFun f := ⟨fun m => ⟪Φ0 m, f⟫_ℂ, (show Memℓp (fun m => ⟪Φ0 m, f⟫_ℂ) 2 by
    refine memℓp_two_iff_summable.mpr ?_
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((summable_norm_hsRow_sq a ha).mul_right (‖f‖ ^ 2))
    rw [← mul_pow]
    gcongr
    exact norm_inner_le_norm _ _)⟩
  map_add' f g := by
    ext m
    simp [inner_add_right]
    rfl
  map_smul' c f := by
    ext m
    simp [inner_smul_right]

lemma hsMatrixLin_apply f m :
    (hsMatrixLin a ha f : ℤ → ℂ) m = ⟪Φ0 m, f⟫_ℂ := rfl

lemma norm_hsMatrixLin_le f :
    ‖hsMatrixLin a ha f‖ ≤ Real.sqrt (∑' p, ‖a p‖ ^ 2) * ‖f‖ := by
  have hS : 0 ≤ ∑' p, ‖a p‖ ^ 2 := tsum_nonneg fun _ => by positivity
  have := Real.sqrt_le_sqrt (show ‖hsMatrixLin a ha f‖ ^ 2 ≤ (∑' p, ‖a p‖ ^ 2) * ‖f‖ ^ 2 by
    have h_inl : ∑' m, ‖Φ0 m‖ ^ 2 = ∑' p, ‖a p‖ ^ 2 := by
      simp_rw [norm_hsRow_sq a ha]
      exact ha.tsum_prod.symm
    rw [norm_sq_L2Z, ← h_inl, ← tsum_mul_right]
    refine (summable_norm_sq_L2Z _).tsum_le_tsum (fun m => ?_)
      ((summable_norm_hsRow_sq a ha).mul_right _)
    rw [hsMatrixLin_apply, ← mul_pow]
    gcongr
    exact norm_inner_le_norm _ _)
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg _)] at this

/-- **The Hilbert–Schmidt matrix operator** `(T f)_m = ∑_n a_{m n} f_n` on `ℓ²(ℤ)`. -/
def hsMatrixOp : L2Z →L[ℂ] L2Z :=
  (hsMatrixLin a ha).mkContinuous _ (norm_hsMatrixLin_le a ha)

lemma hsMatrixOp_apply f m :
    (hsMatrixOp a ha f : ℤ → ℂ) m = ∑' n, a (m, n) * f n := by
  change ⟪Φ0 m, f⟫_ℂ = _
  rw [lp.inner_eq_tsum]
  simp [hsRow_apply, mul_comm]

/-- `‖T‖ ≤ (∑ |a_{m n}|²)^{1/2}`. -/
theorem norm_hsMatrixOp_le : ‖hsMatrixOp a ha‖ ≤ Real.sqrt (∑' p, ‖a p‖ ^ 2) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

lemma hsMatrixOp_stdBasisZ n :
    (hsMatrixOp a ha (stdBasisZ n) : ℤ → ℂ) = fun m => a (m, n) := by
  funext m
  rw [hsMatrixOp_apply, stdBasisZ_apply, tsum_eq_single n]
  · simp
  · intro k hk
    simp [hk]

/-- **Hilbert–Schmidt matrices are compact.** -/
theorem isCompactOperator_hsMatrixOp : IsCompactOperator (hsMatrixOp a ha) := by
  refine isCompactOperator_of_summable_norm_sq stdBasisZ _ ?_
  simp_rw [show ∀ n, ‖hsMatrixOp a ha (stdBasisZ n)‖ ^ 2 = ∑' m, ‖a (m, n)‖ ^ 2 by
    intro n
    rw [norm_sq_L2Z, hsMatrixOp_stdBasisZ]]
  exact ((Equiv.prodComm ℤ ℤ).summable_iff.mpr ha).prod

end PolyaNeumann
