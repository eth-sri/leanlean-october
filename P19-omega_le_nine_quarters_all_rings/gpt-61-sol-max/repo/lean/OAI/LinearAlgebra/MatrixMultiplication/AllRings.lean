module

public import Mathlib
public import OAI.LinearAlgebra.MatrixMultiplication.Proof

/-
Copyright c 2026. Released under Apache-2.0 as described in LICENSE.
Integral extension of OpenAI's matrix-multiplication proof and its all-fields
extension. See UPSTREAM.md for provenance and attribution.
-/

@[expose] public section

/-!
# Matrix multiplication over every ring

Exact integer coefficient schemes give the bound `9/4` over every associative
unital ring, including noncommutative rings. The arithmetic exponent uses the
same program semantics, gate costs, positive slack, and infimum as the prior
all-fields theorem. For nontrivial rings its admissible-exponent set is bounded
below. For trivial rings multiplication has zero arithmetic cost, and the
real-valued infimum is zero by Mathlib's convention for an unbounded-below set.

The direct operation-count theorem also includes the zero ring. Its exponent
is `9/4 + ε` for every positive `ε`; it does not assert an exact `O(n^(9/4))`
operation bound or a uniform circuit-generation algorithm.
-/

namespace OAI.MatrixMultiplication

universe u

namespace AuxiliarySeparation.Integral

set_option maxHeartbeats 1000000 in
/-- The exact integer coefficient rank exponent is at most `9/4`.
Both finite separation and convolution bounds are supplied by proved integral
constructions, with no field or algebraic-closure hypothesis. -/
theorem exactRankExponent_int_le_nine_quarters :
    exactRankExponent ≤ (9 : ℝ) / 4 := by
  apply rpow_exponent_le_of_nat_bound (C := 2)
  intro d hd
  by_cases hd2 : 2 ≤ d
  · let x := (d : ℝ) ^ exactRankExponent
    let k := ⌈x - 1⌉₊
    have hk := Nat.le_ceil (x - 1)
    have hx : 0 < x := by positivity
    have hk' : (k : ℝ) < x := by
      have := Nat.ceil_lt_add_one_of_gt_neg_one (show -1 < x - 1 by linarith)
      simpa only [k, sub_add_cancel] using this
    obtain ⟨χ, hχ⟩ := exists_detecting_character hd2 hk'
    have hb : χ.value (matrixMultiplicationTensor d d d) ≤ (d : ℝ) ^ (9 / 4 : ℝ) := by
      rw [χ.value_matrixMultiplication (by omega)]
      apply Real.rpow_le_rpow_of_exponent_le (by exact?)
      apply χ.exponent_sum_le_nine_quarters_of_separation_and_convolution
      · intro ψ M X Y Z _ _ _ hM B
        let degree := 2 * M ^ 2
        let L := 5 * M
        let ι (L : ℕ) := Fin (Polynomial.cyclotomic L ℤ).natDegree
        let source (L n : ℕ) :=
          Foundation.Tensor.directSum fun _ : ι L × ι L =>
            Foundation.Tensor.directSum fun _ : Fin (degree * n + 1) × Fin (degree * n + 1) =>
              Foundation.Tensor.power (Foundation.Tensor.directSum fun _ : Fin L => sharedFirstTensor B) n
        have hperiod (L : ℕ) (hL : 5 * M ≤ L) : ∀ n : ℕ,
            TensorSemiring.IsRestriction
              (fun x y z => (L : ℤ) ^ n * Foundation.Tensor.power (separationTarget B) n x y z)
              (source L n) := by
          classical
          letI : NeZero L := ⟨by omega⟩
          let E := CyclotomicAlgebra L
          let BE  := fun i x y z => algebraMap ℤ E (B i x y z)
          let ζ := cyclotomicUnit L
          let phase (g h u v : ℤ) := u - v + 2 * (g - h)
          let leftDegree (g : ℤ) := (g ^ 2).toNat
          let middleDegree (h u : ℤ) := ((M : ℤ) ^ 2 + h * u - h ^ 2).toNat
          let rightDegree (h v : ℤ) := ((M : ℤ) ^ 2 - h * v).toNat
          let weightedBranch (g h u v : ℤ) (c : E) :=
            Polynomial.monomial (leftDegree g + middleDegree h u + rightDegree h v)
              ((∑ r : Fin L, (↑(ζ ^ (r.val * phase g h u v)) : E)) * c)
          have hcoeff {g h u v : ℤ}
              (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
              (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M)
              {j : ℕ} (hj : j ≤ degree) (c : E) :
              (weightedBranch g h u v c).coeff j =
                if j = degree ∧ g = h ∧ u = v then (L : E) * c else 0 := by
            have he : |phase g h u v| < L := by unfold phase; grind
            unfold weightedBranch
            rw [sum_unit_zpow_primitive_root_of_abs_lt (cyclotomicUnit_primitive L) he]
            by_cases hp : phase g h u v = 0
            · have hc : ((leftDegree g + middleDegree h u + rightDegree h v : ℕ) : ℤ) =
                  2 * (M : ℤ) ^ 2 + (g - h) ^ 2 := by
                unfold leftDegree middleDegree rightDegree
                push_cast
                repeat' rw [Int.toNat_of_nonneg (by first | positivity | nlinarith)]
                unfold phase at hp
                linear_combination h * hp
              have hdeg : leftDegree g + middleDegree h u + rightDegree h v = j ↔
                  j = degree ∧ g = h := by
                dsimp only [degree] at hj ⊢
                zify at hj ⊢
                grind [sq_nonneg (g - h), sq_eq_zero_iff]
              simp  [hp, ↓reduceIte, Polynomial.coeff_monomial, hdeg]
              by_cases hg : g = h <;> simp_all [phase, sub_eq_zero]
            aesop (add simp [phase])
          let leftPolynomialMap  : Fin M × X × Unit → Fin L × X → Polynomial E := fun x r => if r.2 = x.2.1 then
              Polynomial.monomial (leftDegree (sectorNumber x.1))
                (↑(ζ ^ (r.1.val * (2 * sectorNumber x.1)))  ) else 0

          let middlePolynomialMap  :
              Fin M × Y × Fin M → Fin L × Fin M × Y → Polynomial E := fun y r => if r.2 = (y.1, y.2.1) then
              Polynomial.monomial (middleDegree (sectorNumber y.1) (sectorNumber y.2.2))
                (↑(ζ ^ (r.1.val * (sectorNumber y.2.2 - sectorNumber y.1)))  ) else 0

          let rightPolynomialMap  :
              Fin M × Z × Fin M → Fin L × Fin M × Z → Polynomial E := fun z r => if r.2 = (z.1, z.2.1) then
              Polynomial.monomial (rightDegree (sectorNumber z.1) (sectorNumber z.2.2))
                (↑(ζ ^ (r.1.val * (-sectorNumber z.2.2 - sectorNumber z.1)))  ) else 0
          let D : Foundation.Tensor.PolynomialRestrictionDegeneration
              (Foundation.Tensor.directSum fun _ : Fin L => sharedFirstTensor BE)
              (fun x y z => (L : E) * separationTarget BE x y z) (degree) := by
            have hbase :
              Foundation.Tensor.restrict (leftPolynomialMap) (middlePolynomialMap) (rightPolynomialMap)
                (fun x y z => Polynomial.C (Foundation.Tensor.directSum (fun _ : Fin L => sharedFirstTensor BE) x y z)) =
                fun x y z => if y.1 = z.1 then
              weightedBranch (sectorNumber x.1) (sectorNumber y.1)
                (sectorNumber y.2.2) (sectorNumber z.2.2) (BE y.1 x.2.1 y.2.1 z.2.1) else 0 := by
              funext x y z
              by_cases hyz : y.1 = z.1
              all_goals simp [Foundation.Tensor.restrict, Fintype.sum_prod_type, leftPolynomialMap, middlePolynomialMap, rightPolynomialMap, sharedFirstTensor, hyz, apply_ite, ite_and, Prod.ext_iff, eq_comm]
              simp_rw [Polynomial.monomial_mul_monomial, Polynomial.monomial_mul_C]
              rw [← map_sum, ← Finset.sum_mul]
              unfold weightedBranch
              congr 2
              congr 1 with r
              rw [← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add]
              unfold phase
              ring
            refine {
              leftMap := leftPolynomialMap
              middleMap := middlePolynomialMap
              rightMap := rightPolynomialMap
              coeff := ?_ }
            intro x y z j hj
            rw [hbase]
            by_cases hyz : y.1 = z.1
            · aesop (add simp [ite_eq_left, hcoeff, sectorNumber_bounds, sectorNumber_injective.eq_iff, separationTarget, ite_and])
            · simp [hyz, separationTarget]; aesop

          intro n
          apply descend_restriction_basis (cyclotomicBasis L) (cyclotomicProjection L)
            (cyclotomicProjection_one L)
          convert D.extract n using 1 <;> funext x y z <;>
            simp  [Foundation.Tensor.power, Finset.prod_mul_distrib, Finset.card_univ]
          all_goals simp [BE, sharedFirstTensor, separationTarget]
        have hA := hperiod L le_rfl
        have hB := hperiod (L + 1) (by omega)
        let cA  := (Fintype.card (ι L) : ℝ) ^ 2
        let cB  := (Fintype.card (ι (L + 1)) : ℝ) ^ 2
        have hbound : ψ.value (separationTarget B) ≤ (L + 1  ) * ψ.value (sharedFirstTensor B) := by
          apply le_of_pow_le_const_sq_mul_pow
            (A := (degree : ℕ)) (C := (cA + cB))
            (mul_nonneg (by positivity) (ψ.nonneg (sharedFirstTensor B)))
          intro n
          let SA := source L n
          let SB := source (L + 1) n
          let T := Foundation.Tensor.power (separationTarget B) n
          have hc : ψ.value T ≤ ψ.value SA + ψ.value SB := by

            obtain ⟨u, v, huv⟩ := (IsCoprime.add_one_right_of_dvd (dvd_refl (L : ℤ))).pow (m := n) (n := n)
            obtain ⟨A, B, C, h₁⟩ := hA n
            obtain ⟨A', B', C', h₂⟩ := hB n
            rw [← ψ.value_sumTensor SA SB]
            convert ψ.monotone (sumTensor SA SB)
              (fun x => Sum.elim (fun w => u * A x w) fun w => v * A' x w)
              (fun y => Sum.elim (B y) (B' y)) (fun z => Sum.elim (C z) (C' z)) using 1
            congr 1
            funext x y z
            simp only [Foundation.Tensor.restrict, sumTensor, Fintype.sum_sum_type,
              Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_assoc,
              ← Finset.mul_sum]
            simp only [funext_iff, Foundation.Tensor.restrict, mul_assoc, ← Finset.mul_sum, Nat.cast_add] at h₁ h₂
            rw [← h₁, ← h₂]
            linear_combination -T x y z * huv
          have hv : 0 ≤ ψ.value (sharedFirstTensor B) := ψ.nonneg _
          have hp : (L : ℝ) ^ n ≤ (L + 1) ^ n := by gcongr <;> first | positivity | linarith
          simp only [T, SA, SB, source, ψ.value_power, ψ.map_directSum, Finset.sum_const,
            Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
            mul_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hc
          simp only [mul_pow]
          linear_combination (norm := (simp only [cA, cB, ι, Fintype.card_fin]; ring_nf)) hc +
            (cA * (n * (degree : ℕ) + 1) ^ 2 * ψ.value (sharedFirstTensor B) ^ n) * hp
          exact le_rfl
        have hL : (L + 1  ) ≤ 6 * (M : ℝ) := by
          dsimp [L]
          norm_num only [Nat.cast_mul]
          have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
          nlinarith
        have h := hbound.trans (mul_le_mul_of_nonneg_right hL (ψ.nonneg _))
        rw [separationTarget, ψ.map_directSum] at h
        simpa only [ψ.map_product, ψ.value_cyclic_cyclic_dotPairing hM, Finset.sum_mul] using h
      · intro ψ a b
        let h := a + b - 1
        by_cases hh : h = 0
        · have hz : convolution (K := ℤ) a b = 0 := by
            funext i j k
            exact Fin.elim0 (Fin.cast hh k)
          simp [hz, ψ.map_zero]
        letI : NeZero h := ⟨hh⟩
        let d L := (Polynomial.cyclotomic L ℤ).natDegree
        let size := d h ^ 2 + d (h + 1) ^ 2
        apply le_of_eventually_pow_le_const_mul_pow (C := size) (Nat.cast_nonneg _)
        apply Filter.Eventually.of_forall
        intro k
        suffices hrank : Foundation.Tensor.RankAtMost
            (Foundation.Tensor.power (convolution (K := ℤ) a b) k) (h ^ k * size) by
          simpa only [ψ.value_power, Nat.cast_mul, Nat.cast_pow, mul_comm] using ψ.value_le_rank hrank
        obtain ⟨u, v, huv⟩ := (IsCoprime.add_one_right_of_dvd (dvd_refl (h : ℤ))).pow (m := k) (n := k)
        obtain ⟨A, B, C, h0⟩ := convolution_fourier_power_rank h (Or.inl rfl) k
        obtain ⟨A', B', C', h1⟩ := convolution_fourier_power_rank (h+1) (Or.inr rfl) k
        convert Foundation.Tensor.rankAtMost_sum_rankOne
          (Sum.elim (fun q x => u * A q x) (fun q x => v * A' q x))
          (Sum.elim B B') (Sum.elim C C') using 1
        · funext x y z
          simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Foundation.Tensor.rankOne,
            mul_assoc, ← Finset.mul_sum]
          simp only [funext_iff, Foundation.Tensor.rankOne, mul_assoc] at h0 h1
          rw [← h0, ← h1]
          simp only [Nat.cast_add, Nat.cast_one]
          linear_combination -Foundation.Tensor.power (convolution (K := ℤ) a b) k x y z * huv
        · simp [size, d]
          ring
    have hp := Real.one_le_rpow (show (1 : ℝ) ≤ d by exact_mod_cast hd)
      (by norm_num : (0 : ℝ) ≤ 9 / 4)
    linarith
  · have hd1 : d = 1 := by omega
    simp [hd1]

end AuxiliarySeparation.Integral

/-- Every ring admits the positive-slack arithmetic bound at exponent `9/4`.
This statement also includes the zero ring. -/
theorem admissibleExponent_nine_quarters_all_rings (R : Type u) [Ring R] :
    Arithmetic.AdmissibleExponent R ((9 : ℝ) / 4) := by
  intro ε hε
  have h := AuxiliarySeparation.Integral.exactRankExponent_int_le_nine_quarters
  convert AuxiliarySeparation.Integral.exactRankExponent_int_admissible R
    (9 / 4 + ε - AuxiliarySeparation.exactRankExponent) (by linarith) using 1
  ring

/-- The square matrix multiplication exponent over every associative unital
ring is at most `9/4`. In the trivial case the existing infimum definition
returns zero; the substantive integer-rank argument covers nontrivial rings. -/
theorem omega_le_nine_quarters_all_rings (R : Type u) [Ring R] :
    Arithmetic.omega R ≤ (9 : ℝ) / 4 := by
  unfold Arithmetic.omega
  by_cases h : BddBelow {τ : ℝ | Arithmetic.AdmissibleExponent R τ}
  · exact csInf_le h (admissibleExponent_nine_quarters_all_rings R)
  · grind [Real.sInf_of_not_bddBelow h]

end OAI.MatrixMultiplication
