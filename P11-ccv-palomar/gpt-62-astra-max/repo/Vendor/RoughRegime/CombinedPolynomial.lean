module

public import RoughRegime.MatrixDeterminant


@[expose] public section

/-! The exact entry polynomials for the matrix-inverse/determinant product in
Lemma 5(a), with all matrix entries represented as independent variables. -/

noncomputable section
open scoped BigOperators

namespace RoughRegime.CombinedPolynomial

open MatrixDeterminant MatrixUpper Upper

section
variable {N n0 : ℕ} (dims : Fin N → ℕ) (lo hi : ℝ) (a b : Fin n0)

abbrev Variables (n0 : ℕ) (dims : Fin N → ℕ) :=
  (Fin n0 × Fin n0) ⊕ ((i : Fin N) × (Fin (dims i) × Fin (dims i)))

def inverseVariableSeries : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab => (Sum.inl ab))).toRingHom
    (variableKernelSeries lo hi a b)

def determinantVariableSeries (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (i : Fin N) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab => (Sum.inr ⟨i, ab⟩))).toRingHom
    (variableKernelSeries lo hi).det

def combinedVariableSeries : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  inverseVariableSeries dims lo hi a b * ∏ i, determinantVariableSeries n0 dims lo hi i

def combinedCoefficientPolynomial (k : ℕ) : MvPolynomial (Variables n0 dims) ℝ :=
  PowerSeries.coeff k (combinedVariableSeries dims lo hi a b)

end

lemma inverseVariableSeries_degree {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (k : ℕ) :
    (PowerSeries.coeff k (inverseVariableSeries dims lo hi a b)).totalDegree ≤ k := by
  rw [inverseVariableSeries, PowerSeries.coeff_map]
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  simp only [variableKernelSeries, PowerSeries.coeff_mk]
  exact (matrixEntryPolynomial_degree _ a b).trans (kernelCoefficientPolynomial_natDegree ..)

lemma determinantVariableSeries_degree {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (i : Fin N) (k : ℕ) :
    (PowerSeries.coeff k (determinantVariableSeries n0 dims lo hi i)).totalDegree ≤ k := (MvPolynomial.totalDegree_rename_le _ _).trans
    (determinantCoefficientPolynomial_totalDegree lo hi k)

section
variable {N n0 : ℕ} (dims : Fin N → ℕ) (lo hi : ℝ) (a b : Fin n0) (m : ℕ)

theorem combinedCoefficientPolynomial_degree (k : ℕ) :
    (combinedCoefficientPolynomial dims lo hi a b k).totalDegree ≤ k := by
  apply coeff_totalDegree_mul_le
  · exact inverseVariableSeries_degree n0 dims lo hi a b
  · intro j
    grind [coeff_totalDegree_prod_le, determinantVariableSeries_degree]

def truncationEntryPolynomial : MvPolynomial (Variables n0 dims) ℝ :=
  MvPolynomial.C ((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹) *
    ∑ k ∈ Finset.range (m + 1), combinedCoefficientPolynomial dims lo hi a b k

theorem truncationEntryPolynomial_degree :
    (truncationEntryPolynomial dims lo hi a b m).totalDegree ≤ m := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  exact (combinedCoefficientPolynomial_degree dims lo hi a b k).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

def entryValuation {dims : Fin N → ℕ}
    (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) : Variables n0 dims → ℝ
  | Sum.inl ab => M0 ab.1 ab.2
  | Sum.inr ⟨i, ab⟩ => M i ab.1 ab.2

end

lemma eval_renamed_series {V W : Type*} (f : V → W) (values : W → ℝ)
    (P : PowerSeries (MvPolynomial V ℝ)) :
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) values)
      (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (values ∘ f)) P := by
  ext k
  exact MvPolynomial.eval_rename ..

lemma inverseVariableSeries_eval {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (a b : Fin n0) :
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation M0 M))
      (inverseVariableSeries dims lo hi a b) = kernelSeries lo hi M0 a b := by
  rw [inverseVariableSeries, eval_renamed_series]
  exact congrArg (fun A => A a b) (variableKernelSeries_map_eval ..)

lemma determinantVariableSeries_eval {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (i : Fin N) :
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation M0 M))
      (determinantVariableSeries n0 dims lo hi i) = (kernelSeries lo hi (M i)).det := by
  rw [determinantVariableSeries, eval_renamed_series]
  ext k
  apply determinantCoefficientPolynomial_eval

variable {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (a b : Fin n0)

theorem combinedCoefficientPolynomial_eval (k : ℕ) :
    MvPolynomial.eval (entryValuation M0 M)
      (combinedCoefficientPolynomial dims lo hi a b k) =
      PowerSeries.coeff k (kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det) := by
  have he := congrArg (fun P => PowerSeries.coeff k P)
    ((by simp [combinedVariableSeries, map_mul, map_prod, inverseVariableSeries_eval, determinantVariableSeries_eval] : (PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation M0 M))) (combinedVariableSeries dims lo hi a b) = kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det))
  assumption

theorem truncationEntryPolynomial_eval (m : ℕ) :
    MvPolynomial.eval (entryValuation M0 M) (truncationEntryPolynomial dims lo hi a b m) =
      (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ *
        ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff k (kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det) := by
  simp [truncationEntryPolynomial, combinedCoefficientPolynomial_eval]

end RoughRegime.CombinedPolynomial
