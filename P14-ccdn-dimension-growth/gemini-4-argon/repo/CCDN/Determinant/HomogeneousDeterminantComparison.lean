/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import ArithmeticHeights.BombieriVaaler
public import CCDN.Algebra.HomogeneousMonomials
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import CCDN.Algebra.HomogeneousEvaluation
import CCDN.Algebra.RowSelection
import CCDN.Determinant.GramDeterminant
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.HomogeneousHilbert
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Matrix.Block

/-!
The exact-rank determinant comparison when no integral auxiliary polynomial exists.
-/

@[expose] public section

namespace CCDN
noncomputable section
open MvPolynomial Matrix Finset Module Submodule exteriorPower
open scoped MonomialOrder

/-- The coefficient vector of `f * X^(α_i)` in the basis of degree-`M` monomials. -/
def multipleBasisVec (d M : ℕ) {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (i : Fin ((n + (M - d)).choose (M - d))) (j : Fin ((n + M).choose M)) : ℤ :=
  (f * monomial (homogeneousMonomials n (M - d) i) 1).coeff (homogeneousMonomials n M j)

/-- The leading-monomial submatrix of `multipleBasisVec` is triangular with determinant
`(order.leadingCoeff f) ^ k`. -/
theorem det_multipleBasisVec_leading {n d M : ℕ}
    (order : MonomialOrder (Fin (n + 1)))
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M) :
    ∃ (col : Fin ((n + (M - d)).choose (M - d)) → Fin ((n + M).choose M))
      (π : Equiv.Perm (Fin ((n + (M - d)).choose (M - d)))),
      Function.Injective col ∧
      ((Matrix.of fun i j => multipleBasisVec d M f i (col j)).submatrix π π).det =
        (order.leadingCoeff f) ^ (n + (M - d)).choose (M - d) := by
  classical
  have hdeg_f : (order.degree f).degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp (order.degree_mem_support hf0))
  let α := homogeneousMonomials n (M - d)
  have hdeg_add (i : Fin ((n + (M - d)).choose (M - d))) : (order.degree f + α i).degree = M := by
    rw [map_add, hdeg_f, homogeneousMonomials_degree, Nat.add_sub_of_le hdM]
  let col (i : Fin ((n + (M - d)).choose (M - d))) : Fin ((n + M).choose M) :=
    (homogeneousExponentEquiv n M).symm ⟨order.degree f + α i, hdeg_add i⟩
  have hcol_eq (i) : homogeneousMonomials n M (col i) = order.degree f + α i :=
    congrArg Subtype.val ((homogeneousExponentEquiv n M).apply_symm_apply ⟨_, hdeg_add i⟩)
  have hcol_inj : Function.Injective col := fun i j hij =>
    homogeneousMonomials_injective n (M - d)
      (add_left_cancel ((hcol_eq i).symm.trans (by rw [hij, hcol_eq j])))
  let π := Tuple.sort (fun i => order.toSyn (α i))
  refine ⟨col, π, hcol_inj, ?_⟩
  let B := (Matrix.of fun i j => multipleBasisVec d M f i (col j)).submatrix π π
  have hdeg_mul (i) : order.degree (f * monomial (α i) (1 : ℤ)) = order.degree f + α i := by
    rw [order.degree_mul hf0 (monomial_eq_zero.not.mpr one_ne_zero),
      order.degree_monomial, ite_eq_right one_ne_zero]
  have hlow : B.BlockTriangular OrderDual.toDual := by
    intro i j (hij : i < j)
    dsimp [B, multipleBasisVec]
    rw [hcol_eq]
    apply order.coeff_eq_zero_of_lt
    rw [hdeg_mul]
    have hle := Tuple.monotone_sort (fun i => order.toSyn (α i)) hij.le
    have hne : order.toSyn (α (π i)) ≠ order.toSyn (α (π j)) :=
      (order.toSyn.injective.comp ((homogeneousMonomials_injective n (M - d)).comp π.injective)).ne
        hij.ne
    have hlt : order.toSyn (α (π i)) < order.toSyn (α (π j)) := lt_of_le_of_ne hle hne
    change order.toSyn (order.degree f + α (π i)) < order.toSyn (order.degree f + α (π j))
    rw [map_add, map_add]
    exact add_lt_add_right hlt _
  rw [Matrix.det_of_isLowerTriangular B hlow]
  have hdiag (i) : B i i = order.leadingCoeff f := by
    dsimp [B, multipleBasisVec]
    rw [hcol_eq, ← hdeg_mul, ← MonomialOrder.leadingCoeff, MonomialOrder.leadingCoeff_mul,
      MonomialOrder.leadingCoeff_monomial, mul_one]
  simp [hdiag]

/-- At `M = d`, the `1 × 1` minor of `multipleBasisVec` at column `j` is the `j`-th coefficient
of `f`. -/
theorem det_multipleBasisVec_same_degree {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (j : Fin ((n + d).choose d)) :
    ∃ (col : Fin ((n + (d - d)).choose (d - d)) → Fin ((n + d).choose d))
      (π : Equiv.Perm (Fin ((n + (d - d)).choose (d - d)))),
      Function.Injective col ∧
      ((Matrix.of fun i l => multipleBasisVec d d f i (col l)).submatrix π π).det =
        (f.coeff (homogeneousMonomials n d j)) ^ (n + (d - d)).choose (d - d) := by
  have hk : (n + (d - d)).choose (d - d) = 1 := by simp
  have : Subsingleton (Fin ((n + (d - d)).choose (d - d))) := (finCongr hk).subsingleton
  refine ⟨fun _ => j, Equiv.refl _, fun _ _ _ => Subsingleton.elim _ _, ?_⟩
  let e := finCongr hk
  rw [← Matrix.det_submatrix_equiv_self e.symm]
  simp only [Matrix.det_unique, Fin.default_eq_zero, Matrix.submatrix_apply, Equiv.refl_apply,
    Matrix.of_apply, multipleBasisVec, hk, pow_one]
  have h0 : homogeneousMonomials n (d - d) (e.symm 0) = 0 :=
    (Finsupp.degree_eq_zero_iff _).mp
      ((homogeneousMonomials_degree n (d - d) (e.symm 0)).trans (Nat.sub_self d))
  rw [h0, monomial_zero', map_one, mul_one]

/-- General archimedean determinant-method inequality from a minor of `multipleBasisVec`. -/
theorem homogeneous_no_auxiliary_box_comparison_of_minor {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hp : ∀ i, InBox (points i) B)
    (hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (points i) g = 0) → f ∣ g)
    {L : ℝ} (hL0 : 0 < L)
    (hminor : ∃ (col : Fin ((n + (M - d)).choose (M - d)) → Fin ((n + M).choose M))
      (π : Equiv.Perm (Fin ((n + (M - d)).choose (M - d)))),
      Function.Injective col ∧
      L ^ (n + (M - d)).choose (M - d) ≤
        |(((Matrix.of fun i j => multipleBasisVec d M f i (col j)).submatrix π π).det : ℝ)|) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧ s < (n + M).choose M ∧
      s + (n + (M - d)).choose (M - d) = (n + M).choose M ∧
      LinearIndependent ℚ
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      Real.log (Int.Matrix.minorGcd
        (evaluationMatrix (homogeneousMonomials n M) (points ∘ a)) : ℝ) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((n + M).choose M) +
          s * M * Real.log B -
          (((n + M).choose M : ℝ) - s) * Real.log L := by
  /- Archimedean logarithmic bound for an integral evaluation matrix. -/
  classical
  obtain ⟨s, a, ha, hli_rows, hspan_rows, hs⟩ :=
    homogeneous_independent_evaluation_rows f hf hf0 hdM points hzero
  let mon := homogeneousMonomials n M
  let α := homogeneousMonomials n (M - d)
  let A := evaluationMatrix mon (points ∘ a)
  let V := LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin
  let y := multipleBasisVec d M f
  have hli : LinearIndependent ℚ (fun i => Rat.piIntCast _ (y i)) := by
    obtain ⟨col0, π0, _, hdet0⟩ := det_multipleBasisVec_leading MonomialOrder.lex f hf hf0 hdM
    let M_int := (Matrix.of fun i j => y i (col0 j)).submatrix π0 π0
    have hdetQ : (M_int.map ((↑) : ℤ → ℚ)).det ≠ 0 := by
      change ((Int.castRingHom ℚ).mapMatrix M_int).det ≠ 0
      rw [← RingHom.map_det (Int.castRingHom ℚ), hdet0]
      exact (map_ne_zero_iff _ Int.cast_injective).mpr
        (pow_ne_zero _ (MonomialOrder.lex.leadingCoeff_ne_zero_iff.mpr hf0))
    exact (linearIndependent_equiv π0).mp
      (LinearIndependent.of_comp (LinearMap.funLeft ℚ ℚ (col0 ∘ π0))
        (Matrix.linearIndependent_row_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hdetQ.isUnit)))
  have hsat : Submodule.span ℤ (Set.range y) = V.intPoints := by
    refine le_antisymm (Submodule.span_le.mpr ?_) fun z hz => ?_
    · rintro _ ⟨i, rfl⟩
      let gi := f * monomial (α i) 1
      have hgi : gi.IsHomogeneous M := by
        simpa only [Nat.add_sub_of_le hdM] using
          hf.mul (isHomogeneous_monomial _ (homogeneousMonomials_degree n (M - d) i))
      rw [SetLike.mem_coe, Submodule.mem_intPoints, LinearMap.mem_ker, Matrix.mulVecLin_apply]
      ext l
      have hval : (A *ᵥ y i) l = 0 := by
        rw [← eval_polynomialOfCoefficients,
          show polynomialOfCoefficients mon (y i) = gi from (homogeneous_eq_sum_coeff gi hgi).symm]
        simp [gi, hzero (a l)]
      have hcast : ((A.map ((↑) : ℤ → ℚ)) *ᵥ Rat.piIntCast _ (y i)) l = ((A *ᵥ y i) l : ℚ) := by
        simp [Matrix.mulVec, dotProduct]
      rw [hcast, hval, Int.cast_zero, Pi.zero_apply]
    · rw [Submodule.mem_intPoints, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz
      have hAz : A *ᵥ z = 0 := by
        ext l; have hl := congrFun hz l
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Rat.piIntCast_apply,
          Pi.zero_apply] at hl ⊢
        exact_mod_cast hl
      let g := polynomialOfCoefficients mon z
      have hghom : g.IsHomogeneous M := polynomialOfCoefficients_homogeneous n M z
      obtain ⟨u, hu⟩ := hrel g hghom fun l =>
        vanishes_of_evaluation_row_mem_span mon (points ∘ a) z hAz (points l)
          (hspan_rows ▸ Submodule.subset_span ⟨l, rfl⟩)
      have huhom : u.IsHomogeneous (M - d) := homogeneous_multiplier hf hf0 (hu ▸ hghom) hdM
      rw [show z = ∑ i, u.coeff (α i) • y i by
        ext j
        rw [← coefficient_polynomialOfCoefficients mon (homogeneousMonomials_injective n M) z j]
        change g.coeff (mon j) = _
        rw [hu]; conv_lhs => rw [homogeneous_eq_sum_coeff u huhom]
        rw [Finset.mul_sum, coeff_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_eq_mul,
          show monomial (α i) (u.coeff (α i)) = C (u.coeff (α i)) * monomial (α i) 1 by
            rw [C_mul_monomial, mul_one],
          ← mul_assoc, mul_comm f (C _), mul_assoc, C_mul', coeff_smul, smul_eq_mul]
        rfl]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdim1 : finrank ℚ ↥V = (n + M).choose M - s := by
    simpa [V, A] using Int.Matrix.finrank_ker A hli_rows
  have hdim2 : finrank ℚ ↥V = (n + (M - d)).choose (M - d) := by
    rw [← V.span_rat_of_span_intPoints hsat, finrank_span_eq_card hli, Fintype.card_fin]
  have hr : s + (n + (M - d)).choose (M - d) = (n + M).choose M := by omega
  obtain ⟨col, π, hcol, hdet⟩ := hminor
  have hD : 1 ≤ Int.Matrix.minorGcd A := Int.Matrix.one_le_minorGcd hli_rows
  have hD0 : (0 : ℝ) < (Int.Matrix.minorGcd A : ℝ) := mod_cast (show (0 : ℤ) < _ by omega)
  have hpl : ((Int.Matrix.minorGcd A : ℤ) : ℝ) *
      |(((Matrix.of fun i j => y i (col j)).submatrix π π).det : ℝ)| ≤
        Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) := by
    have hgcd : (univ : Finset (Set.powersetCard (Fin ((n + M).choose M))
        ((n + (M - d)).choose (M - d)))).gcd (plucker _ y) = 1 :=
      V.gcd_plucker_eq_one hli hsat
    have hAY : A * (Matrix.of y)ᵀ = 0 := by
      ext r i
      have hyi : y i ∈ V.intPoints := hsat ▸ Submodule.subset_span ⟨i, rfl⟩
      rw [Submodule.mem_intPoints, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hyi
      have hri := congrFun hyi r
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Rat.piIntCast_apply,
        Pi.zero_apply] at hri
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
      exact_mod_cast hri
    let σ := Tuple.sort col
    let φ := OrderEmbedding.ofStrictMono (col ∘ σ)
      ((Tuple.monotone_sort col).strictMono_of_injective (hcol.comp σ.injective))
    let S := Set.powersetCard.ofFinEmbEquiv φ
    let M_sub := Matrix.of fun i j => y i (φ j)
    let τ : Equiv.Perm (Fin ((n + (M - d)).choose (M - d))) := π.trans σ.symm
    have hdet' : ((Matrix.of fun i j => y i (col j)).submatrix π π).det =
        ((M_sub.submatrix (τ.symm.trans π) id).submatrix τ τ).det := by
      congr 1; ext i j; simp [M_sub, τ, φ]
    have hpl_eq : M_sub.det = plucker _ y S := by
      rw [plucker_apply, Set.powersetCard.ofFinEmbEquiv.symm_apply_apply]
    rw [hdet', Matrix.det_submatrix_equiv_self τ, Matrix.det_permute, hpl_eq,
      Int.cast_mul, abs_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (τ.symm.trans π)) with h | h <;>
      simp only [h, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, abs_neg, abs_one, one_mul] <;>
      rw [← Real.sqrt_sq (mul_nonneg hD0.le (abs_nonneg _)), mul_pow, sq_abs] <;>
      exact Real.sqrt_le_sqrt
        (mod_cast Int.Matrix.minorGcd_sq_mul_plucker_sq_le hr A hli_rows y hAY hgcd S)
  have hbound : (Int.Matrix.minorGcd A : ℝ) * L ^ (n + (M - d)).choose (M - d) ≤
      Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) :=
    (mul_le_mul_of_nonneg_left hdet hD0.le).trans hpl
  have hDL : 0 < (Int.Matrix.minorGcd A : ℝ) * L ^ (n + (M - d)).choose (M - d) :=
    mul_pos hD0 (pow_pos hL0 _)
  have hG : 0 < (((A * Aᵀ).det : ℤ) : ℝ) := Real.sqrt_pos.mp (hDL.trans_le hbound)
  have hlog := Real.log_le_log hDL hbound
  rw [Real.log_mul hD0.ne' (pow_pos hL0 _).ne', Real.log_pow, Real.log_sqrt hG.le,
    show (((n + (M - d)).choose (M - d) : ℕ) : ℝ) = ((n + M).choose M : ℝ) - s by
      rw [← hr]; push_cast; ring] at hlog
  have he : (((A * Aᵀ).det : ℤ) : ℝ) = ((A.map ((↑) : ℤ → ℝ)) * (A.map ((↑) : ℤ → ℝ))ᵀ).det := by
    change (Int.castRingHom ℝ) (A * Aᵀ).det = _
    rw [RingHom.map_det]; congr 1; ext i j; simp [Matrix.mul_apply]
  have hgram := evaluation_gram_det_le mon (points ∘ a) hB
    (fun i j => hp (a i) j) (fun j => (homogeneousMonomials_degree n M j).le)
  change |((A.map ((↑) : ℤ → ℝ)) * (A.map ((↑) : ℤ → ℝ))ᵀ).det| ≤ _ at hgram
  rw [← he, abs_of_pos hG] at hgram
  have hlogG := Real.log_le_log hG hgram
  have hB0 : 0 < B := by linarith
  have hN0 : (0 : ℝ) < (n + M).choose M := mod_cast (show 0 < (n + M).choose M by omega)
  have hfact : (0 : ℝ) < s.factorial := mod_cast Nat.factorial_pos s
  rw [Real.log_mul hfact.ne' (pow_pos (mul_pos hN0 (sq_pos_of_pos (pow_pos hB0 M))) s).ne',
    Real.log_pow, Real.log_mul hN0.ne' (sq_pos_of_pos (pow_pos hB0 M)).ne',
    Real.log_pow, Real.log_pow] at hlogG
  norm_num at hlogG
  exact ⟨s, a, ha, hs, hr, hli_rows, by nlinarith⟩

/-- The archimedean half of the determinant-method inequality, for
bounded integer points and exact Hilbert rank. -/
theorem homogeneous_no_auxiliary_box_comparison {n d M t : ℕ}
    (order : MonomialOrder (Fin (n + 1)))
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hp : ∀ i, InBox (points i) B)
    (hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (points i) g = 0) → f ∣ g) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧ s < (n + M).choose M ∧
      s + (n + (M - d)).choose (M - d) = (n + M).choose M ∧
      LinearIndependent ℚ
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      Real.log (Int.Matrix.minorGcd
        (evaluationMatrix (homogeneousMonomials n M) (points ∘ a)) : ℝ) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((n + M).choose M) +
          s * M * Real.log B -
          (((n + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨col, π, hcol, hdet⟩ := det_multipleBasisVec_leading order f hf hf0 hdM
  refine homogeneous_no_auxiliary_box_comparison_of_minor f hf hf0 hdM points hzero hB hp hrel
    (abs_pos.mpr (by exact_mod_cast order.leadingCoeff_ne_zero_iff.mpr hf0)) ⟨col, π, hcol, ?_⟩
  rw [hdet]
  push_cast
  rw [abs_pow]

end
end CCDN
