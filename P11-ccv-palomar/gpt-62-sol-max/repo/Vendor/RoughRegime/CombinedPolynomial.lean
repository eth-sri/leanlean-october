module

public import RoughRegime.MatrixDeterminant


@[expose] public section

/-! The exact entry polynomials for the matrix-inverse/determinant product in
Lemma 5(a), with all matrix entries represented as independent variables. -/

noncomputable section
open scoped BigOperators

namespace RoughRegime.CombinedPolynomial

open MatrixDeterminant MatrixUpper Upper

abbrev Variables {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) :=
  (Fin n0 × Fin n0) ⊕ ((i : Fin N) × (Fin (dims i) × Fin (dims i)))

def inverseVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab : Fin n0 × Fin n0 => (Sum.inl ab : Variables n0 dims))).toRingHom
    (variableKernelSeries lo hi a b)

def determinantVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (i : Fin N) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab : Fin (dims i) × Fin (dims i) => (Sum.inr ⟨i, ab⟩ : Variables n0 dims))).toRingHom
    (variableKernelSeries lo hi (n := Fin (dims i))).det

def combinedVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  inverseVariableSeries n0 dims lo hi a b * ∏ i, determinantVariableSeries n0 dims lo hi i

def combinedCoefficientPolynomial {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (k : ℕ) : MvPolynomial (Variables n0 dims) ℝ :=
  PowerSeries.coeff k (combinedVariableSeries n0 dims lo hi a b)

section
variable {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)

lemma inverseVariableSeries_degree
    (a b : Fin n0) (k : ℕ) :
    (PowerSeries.coeff k (inverseVariableSeries n0 dims lo hi a b)).totalDegree ≤ k := by
  rw [inverseVariableSeries, PowerSeries.coeff_map]
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  simp only [variableKernelSeries, PowerSeries.coeff_mk]
  exact (matrixEntryPolynomial_degree _ a b).trans (kernelCoefficientPolynomial_natDegree lo hi k)

lemma determinantVariableSeries_degree
    (i : Fin N) (k : ℕ) :
    (PowerSeries.coeff k (determinantVariableSeries n0 dims lo hi i)).totalDegree ≤ k := by
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
      (determinantCoefficientPolynomial_totalDegree lo hi k)

theorem combinedCoefficientPolynomial_degree
    (a b : Fin n0) (k : ℕ) :
    (combinedCoefficientPolynomial n0 dims lo hi a b k).totalDegree ≤ k := by
  apply coeff_totalDegree_mul_le
  · apply inverseVariableSeries_degree
  · intro j
    exact coeff_totalDegree_prod_le Finset.univ _
      (fun i _ => determinantVariableSeries_degree n0 dims lo hi i) j

end

def truncationEntryPolynomial {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (m : ℕ) : MvPolynomial (Variables n0 dims) ℝ :=
  MvPolynomial.C ((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹) *
    ∑ k ∈ Finset.range (m + 1), combinedCoefficientPolynomial n0 dims lo hi a b k

theorem truncationEntryPolynomial_degree {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (m : ℕ) :
    (truncationEntryPolynomial n0 dims lo hi a b m).totalDegree ≤ m := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  exact (combinedCoefficientPolynomial_degree n0 dims lo hi a b k).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

def entryValuation {N n0 : ℕ} {dims : Fin N → ℕ} {K : Type*}
    (M0 : Matrix (Fin n0) (Fin n0) K)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) K) : Variables n0 dims → K
  | Sum.inl ab => M0 ab.1 ab.2
  | Sum.inr ⟨i, ab⟩ => M i ab.1 ab.2

lemma eval_renamed_series {V W K : Type*} [CommRing K] (f : V → W) (g : ℝ →+* K) (values : W → K)
    (P : PowerSeries (MvPolynomial V ℝ)) :
    PowerSeries.map (MvPolynomial.eval₂Hom g values) (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
    PowerSeries.map (MvPolynomial.eval₂Hom g (values ∘ f)) P := by
  ext k
  simp [MvPolynomial.eval₂_rename]

section
variable {N : ℕ} {K : Type*} [CommRing K] [Algebra ℝ K]
    (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) K)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) K)

local notation "evalPS" => PowerSeries.map (MvPolynomial.eval₂Hom (algebraMap ℝ K) (entryValuation M0 M))

lemma inverseVariableSeries_eval (a b : Fin n0) :
    evalPS (inverseVariableSeries n0 dims lo hi a b) = kernelSeries lo hi M0 a b := by
  rw [inverseVariableSeries, eval_renamed_series]
  exact congrArg (fun A => A a b) (variableKernelSeries_map_eval lo hi M0)

lemma determinantVariableSeries_eval (i : Fin N) :
    evalPS (determinantVariableSeries n0 dims lo hi i) = (kernelSeries lo hi (M i)).det := by
  rw [determinantVariableSeries, eval_renamed_series]
  change PowerSeries.map (MvPolynomial.eval₂Hom (algebraMap ℝ K) (fun ab => M i ab.1 ab.2))
    (variableKernelSeries lo hi).det = _
  rw [RingHom.map_det, variableKernelSeries_map_eval]

section
variable (a b : Fin n0)

theorem combinedVariableSeries_eval :
    evalPS (combinedVariableSeries n0 dims lo hi a b) =
      kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det := by
  simp only [combinedVariableSeries, map_mul, map_prod, inverseVariableSeries_eval, determinantVariableSeries_eval]

theorem combinedCoefficientPolynomial_eval (k : ℕ) :
    MvPolynomial.eval₂ (algebraMap ℝ K) (entryValuation M0 M) (combinedCoefficientPolynomial n0 dims lo hi a b k) =
      PowerSeries.coeff k (kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det) :=
  congrArg (PowerSeries.coeff k) (combinedVariableSeries_eval n0 dims lo hi M0 M a b)

theorem truncationEntryPolynomial_eval (m : ℕ) :
    MvPolynomial.eval₂ (algebraMap ℝ K) (entryValuation M0 M) (truncationEntryPolynomial n0 dims lo hi a b m) =
      algebraMap ℝ K ((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹) *
        ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff k (kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det) := by
  simp only [truncationEntryPolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_sum, combinedCoefficientPolynomial_eval]

end

end

end RoughRegime.CombinedPolynomial
