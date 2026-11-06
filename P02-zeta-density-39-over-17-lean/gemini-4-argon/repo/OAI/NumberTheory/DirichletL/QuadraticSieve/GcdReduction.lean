module
public import OAI.NumberTheory.DirichletL.Fourier.TupleWeights

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace CanonicalQuadraticSieve
open CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy

def gcdPool {n : Type*} [Fintype n] (cols : n → Ideal O) : Finset (Ideal O) :=
  Finset.univ.image (fun p : n × n => gcd (cols p.1) (cols p.2))

theorem mem_gcdPool {n : Type*} [Fintype n] (cols : n → Ideal O) (j k : n) :
    gcd (cols j) (cols k) ∈ gcdPool cols :=
  Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩

theorem gcdPool_ne_zero {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hcols : ∀ j, cols j ≠ 0) (D : Ideal O) (hD : D ∈ gcdPool cols) : D ≠ 0 := by
  obtain ⟨⟨j, k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  intro h
  have hd := gcd_dvd_left (cols j) (cols k)
  rw [h, zero_dvd_iff] at hd
  exact hcols j hd

theorem energy_eq_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    ((∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, gcdBlock D rows cols a := by
  have hp (i : m) (j k : n) : (∑ D ∈ gcdPool cols, gcdTerm D rows cols a i j k) =
      star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
        (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) := by
    rw [Finset.sum_eq_single (gcd (cols j) (cols k))]
    · simp only [gcdTerm, ite_true]
    · intro D hD hne
      exact ite_eq_right (Ne.symm hne)
    · exact fun h => (h (mem_gcdPool cols j k)).elim
  have hi (i : m) : (∑ D ∈ gcdPool cols, ∑ j, ∑ k, gcdTerm D rows cols a i j k) =
      ∑ j, ∑ k, star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
        (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => hp i j k)
  simp only [gcdBlock]
  rw [Finset.sum_comm]
  simp_rw [hi]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Complex.ofReal_pow] using CoprimeSieveOperator.square_norm_sum
    (fun j => quadraticRow (cols j) (primaryGenerator (rows i)) * a j)

end CanonicalQuadraticSieve

namespace FiniteSieveRestriction

def sectorCoefficient {n r : Type*} [DecidableEq r] (σ : n → r) (c : r) (a : n → ℂ) (j : n) : ℂ :=
  if σ j = c then a j else 0

theorem sectorCoefficient_energy {n r : Type*} [Fintype n] [Fintype r] [DecidableEq r]
    (σ : n → r) (a : n → ℂ) :
    (∑ c, ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) = ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (σ j)]
  · simp [sectorCoefficient]
  · intro c hc hne
    simp [sectorCoefficient, Ne.symm hne]
  · simp

private theorem norm_sum_square_card {r : Type*} [Fintype r] (f : r → ℂ) :
    ‖∑ c, f c‖ ^ 2 ≤ (Fintype.card r : ℝ) * ∑ c, ‖f c‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : r => (1 : ℝ)) (fun c => ‖f c‖)
  have hh : ‖∑ c, f c‖ ^ 2 ≤ (∑ c, ‖f c‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  exact hh.trans (by simpa using h)

theorem sector_energy_bound {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    (A : Matrix m n ℂ) (σ : n → r) (a : n → ℂ) :
    (∑ i, ‖∑ j, A i j * a j‖ ^ 2) ≤
      (Fintype.card r : ℝ) * ∑ c, ∑ i, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
  have hi (i : m) : (∑ j, A i j * a j) = ∑ c, ∑ j, A i j * sectorCoefficient σ c a j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, Finset.sum_eq_single (σ j)]
    · simp [sectorCoefficient]
    · intro c hc hne
      simp [sectorCoefficient, Ne.symm hne]
    · simp
  calc
    _ ≤ ∑ i, (Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [hi]
      exact norm_sum_square_card _
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
end FiniteSieveRestriction

namespace CanonicalQuadraticSieve
open CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction

def columnRay (I : Ideal O) : EisensteinEPrimaryPhase.Coord := ActualEisensteinCoordinates.residue (primaryGenerator I)

def rayGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) : ℂ :=
  gcdBlock D rows cols (sectorCoefficient (fun j => columnRay (cols j)) c a)

theorem rayGcdBlock_eq {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    rayGcdBlock D c rows cols a = ∑ i, ∑ j, ∑ k,
      if gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c then
        star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
          (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) else 0 := by
  unfold rayGcdBlock gcdBlock gcdTerm sectorCoefficient
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hg : gcd (cols j) (cols k) = D <;>
    by_cases hj : columnRay (cols j) = c <;> by_cases hk : columnRay (cols k) = c <;>
      simp only [hg, hj, hk, ↓reduceIte, true_and, false_and, and_false,
        mul_zero, zero_mul, star_zero]

end CanonicalQuadraticSieve


namespace CanonicalQuadraticSieve

open CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy


def weightedGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O) (w : m → ℂ) (a : n → ℂ) : ℂ :=
  ∑ i, w i * ∑ j, ∑ k, gcdTerm D rows cols a i j k

theorem highKernel_weightedGcdBlock_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (D : Ideal O) (hD : D ≠ 0)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) (a : n → ℂ) :
    ‖weightedGcdBlock D rows cols w a‖ ≤ W * highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K *
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := by
  let v : m → ℂ := fun i => w i *
    (star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow D (primaryGenerator (rows i)))
  have hv (i : m) : ‖v i‖ ≤ W := by
    dsimp only [v]
    simp only [norm_mul, norm_star]
    calc
      _ ≤ W * (1 * 1) := by
        apply mul_le_mul (hw i)
        · exact mul_le_mul (quadraticRow_norm_le_one D _) (quadraticRow_norm_le_one D _) (norm_nonneg _) (by norm_num)
        · positivity
        · exact hW
      _ = W := by ring
  have he : weightedGcdBlock D rows cols w a = ∑ i, v i * ∑ j, ∑ k,
      if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) *
          (quotientMatrix D rows cols i k * (if D ∣ cols k then a k else 0)) else 0 := by
    unfold weightedGcdBlock
    simp_rw [gcdTerm_eq_quotient D hD rows cols (fun j => (hcols j).1) a]
    simp only [v, ← Finset.mul_sum, mul_assoc]
  rw [he]
  have hb := ideal_coprime_gram_operator_bound ε hε (fun j => totalQuotient D (cols j))
    (fun j => totalQuotient_ne_zero D _ (hcols j).1) N (by linarith)
    (fun j => totalQuotient_norm_le D _ (hcols j).1 N hN (hcols j).2)
    (quotientMatrix D rows cols) (fun j => if D ∣ cols j then a j else 0) v W hW hv
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (highKernel_quotientMatrix_squared_norm_le D hD rows cols hr hc M N K hrows hcols) hW)
      (mul_nonneg (supportConstant_pos ε hε).le (Real.rpow_nonneg (by linarith) _)))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem highKernel_large_weighted_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O)) (G : ℝ) (hG : 0 < G)
    (hS : ∀ D ∈ S, G ≤ (Ideal.absNorm D : ℝ))
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) (a : n → ℂ) :
    (∑ D ∈ S, ‖weightedGcdBlock D rows cols w a‖) ≤
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have hfac : 0 ≤ supportConstant ε hε * N ^ ε :=
    mul_nonneg (supportConstant_pos ε hε).le (Real.rpow_nonneg (by linarith) _)
  have hB : 0 ≤ highKernelNorm M (N / G) K := highKernelNorm_nonneg _ _ _
  have hb (D : Ideal O) (hD : D ∈ S) : ‖weightedGcdBlock D rows cols w a‖ ≤
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := by
    have hn : 0 < (Ideal.absNorm D : ℝ) := hG.trans_le (hS D hD)
    have hD0 : D ≠ 0 := by intro hz; simp [hz] at hn
    have hmono := highKernelNorm_mono (M := M) (K := K) (M' := M) (K' := K) le_rfl
      (div_le_div_of_nonneg_left (by linarith : 0 ≤ N) hG (hS D hD)) le_rfl
    exact (highKernel_weightedGcdBlock_bound ε hε D hD0 rows cols hr hc M N K hN hrows hcols w W hW hw a).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hW) hfac) (by positivity))
  calc
    _ ≤ ∑ D ∈ S, W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := Finset.sum_le_sum hb
    _ = W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ D ∈ S, ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (divisor_mask_energy_small_power ε hε S cols (fun j => (hcols j).1.1) N (fun j => (hcols j).2) a)
        (mul_nonneg (mul_nonneg hW hB) hfac)
    _ = _ := by ring

end CanonicalQuadraticSieve

namespace FiniteSieveRestriction

theorem sector_weighted_energy_bound {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    (A : Matrix m n ℂ) (σ : n → r) (a : n → ℂ) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (∑ i, v i * ‖∑ j, A i j * a j‖ ^ 2) ≤
      (Fintype.card r : ℝ) * ∑ c, ∑ i, v i * ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
  have hi (i : m) : ‖∑ j, A i j * a j‖ ^ 2 ≤
      (Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
    simpa only [Fintype.sum_unique] using sector_energy_bound (fun _ : Unit => A i) σ a
  calc
    _ ≤ ∑ i, v i * ((Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hi i) (hv i))
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      ring
end FiniteSieveRestriction

namespace CanonicalQuadraticSieve

section
open CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction

theorem weighted_energy_eq_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (a : n → ℂ) :
    ((∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a := by
  have hi (i : m) : ((‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, ∑ j, ∑ k, gcdTerm D rows cols a i j k := by
    simpa only [gcdBlock, Fintype.sum_unique, gcdTerm] using energy_eq_gcd_blocks (fun _ : Unit => rows i) cols a
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, hi, Finset.mul_sum, weightedGcdBlock]
  rw [Finset.sum_comm]

theorem weighted_energy_le_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      ∑ D ∈ gcdPool cols, ‖weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a‖ := by
  have he := congrArg norm (weighted_energy_eq_gcd_blocks rows cols v a)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (sq_nonneg _)))] at he
  rw [he]
  exact norm_sum_le _ _

theorem highKernel_weighted_energy_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (v : m → ℝ) (W : ℝ) (hW : 0 ≤ W) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ W) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      (∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        ‖weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a‖) +
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have he := weighted_energy_le_gcd_blocks rows cols v (fun i => (hv i).1) a
  rw [← Finset.sum_filter_add_sum_filter_not (gcdPool cols) (fun D => (Ideal.absNorm D : ℝ) ≤ G)] at he
  exact he.trans (add_le_add le_rfl (highKernel_large_weighted_gcd_blocks ε hε _ G hG
    (fun D hD => (lt_of_not_ge (Finset.mem_filter.mp hD).2).le)
    rows cols hr hc M N K hN hrows hcols (fun i => (v i : ℂ)) W hW
    (fun i => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv i).1] using (hv i).2) a))

def weightedRayGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (a : n → ℂ) : ℂ :=
  weightedGcdBlock D rows cols (fun i => (v i : ℂ))
    (sectorCoefficient (fun j => columnRay (cols j)) c a)

theorem highKernel_weighted_energy_ray_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (v : m → ℝ) (W : ℝ) (hW : 0 ≤ W) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ W) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      16 * ((∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G), ‖weightedRayGcdBlock D c rows cols v a‖) +
        W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
          (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2) := by
  let σ : n → EisensteinEPrimaryPhase.Coord := fun j => columnRay (cols j)
  let C := W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2
  have hs := sector_weighted_energy_bound
    (fun i j => quadraticRow (cols j) (primaryGenerator (rows i))) σ a v (fun i => (hv i).1)
  have hcard : Fintype.card EisensteinEPrimaryPhase.Coord = 16 := by decide
  rw [hcard] at hs
  norm_num only [Nat.cast_ofNat] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
        ((∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖weightedRayGcdBlock D c rows cols v a‖) + C * ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      exact highKernel_weighted_energy_gcd_reduction ε hε G hG rows cols hr hc M N K hN hrows hcols v W hW hv
        (sectorCoefficient σ c a)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, sectorCoefficient_energy]

end
