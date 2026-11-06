module

public import RoughRegime.MatrixDeterminant
public import RoughRegime.Macro


𝗌

/-! The exact entry polynomials for the matrix-inverse/determinant product in
Lemma 5(a), with all matrix entries represented as independent variables. -/

𝚪

namespace RoughRegime.CombinedPolynomial

open MatrixDeterminant MatrixUpper Upper

𝗇 𝔅 Fin N → ℕ
𝗇 𝔈 Fin $ dims i
𝗇 𝔓 Fin n0 × Fin n0
abbrev Variables (n0 : ℕ) (dims : 𝔅) :=
  𝔓 ⊕ (i : Fin N) × 𝔈 × 𝔈

𝗇 𝔘 Variables n0 dims
𝗇 𝔇 MvPolynomial 𝔘 ℝ
def inverseVariableSeries (n0 : ℕ) (dims : 𝔅) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries 𝔇 :=
  PowerSeries.map (MvPolynomial.rename
     fun ab : 𝔓 => (Sum.inl ab : 𝔘) ).toRingHom
    $ variableKernelSeries lo hi a b

def determinantVariableSeries (n0 : ℕ) (dims : 𝔅) (lo hi : ℝ)
    (i : Fin N) : PowerSeries 𝔇 :=
  PowerSeries.map (MvPolynomial.rename
     fun ab : 𝔈 × 𝔈 => (Sum.inr ⟨i, ab⟩ : 𝔘) ).toRingHom
    (variableKernelSeries lo hi (n := 𝔈)).det

𝗃 𝔚 ἀ n0 dims lo hi
𝗃 𝔒 𝔚 ἀ a b
𝗇 𝔍 𝔒 inverseVariableSeries
𝗇 𝔏 𝔚 determinantVariableSeries i
def combinedVariableSeries (n0 : ℕ) (dims : 𝔅) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries 𝔇 :=
  𝔍 * ∏ i, 𝔏

𝗇 𝔐 𝔒 combinedVariableSeries
def combinedCoefficientPolynomial (n0 : ℕ) (dims : 𝔅) (lo hi : ℝ)
    (a b : Fin n0) (k : ℕ) : 𝔇 :=
  PowerSeries.coeff k 𝔐

theorem inverseVariableSeries_degree n0 (dims : 𝔅) lo hi
    a b k :
    (PowerSeries.coeff k 𝔍).totalDegree ≤ k := by
  rw [inverseVariableSeries, PowerSeries.coeff_map]
  apply (MvPolynomial.totalDegree_rename_le ..).trans
  simp only [variableKernelSeries, PowerSeries.coeff_mk]
  exact (matrixEntryPolynomial_degree _ a b).trans $ kernelCoefficientPolynomial_natDegree lo hi k

theorem determinantVariableSeries_degree n0 dims lo hi
    (i : Fin N) k :
    (PowerSeries.coeff k 𝔏).totalDegree ≤ k := (MvPolynomial.totalDegree_rename_le ..).trans
    $ determinantCoefficientPolynomial_totalDegree lo hi k

𝗇 𝔎 𝔒 combinedCoefficientPolynomial k
theorem combinedCoefficientPolynomial_degree n0 (dims : 𝔅) lo hi
    a b k :
    (𝔎).totalDegree ≤ k := by
  apply coeff_totalDegree_mul_le
  · exact 𝔒 inverseVariableSeries_degree
  · intro j
    exact coeff_totalDegree_prod_le Finset.univ _
      (fun i _ => 𝔚 determinantVariableSeries_degree i) j

𝗇 𝔊 (intervalGeometricMean lo hi ^ ( ∑ i, dims i + 1))⁻¹
𝗇 𝔔 m + 1
def truncationEntryPolynomial (n0 : ℕ) (dims : 𝔅) (lo hi : ℝ)
    (a b : Fin n0) (m : ℕ) : 𝔇 :=
  MvPolynomial.C 𝔊 *
    ∑ k ∈ Finset.range 𝔔, 𝔎

𝗇 𝔑 𝔒 truncationEntryPolynomial m
theorem truncationEntryPolynomial_degree n0 (dims : 𝔅) lo hi
    a b m :
    (𝔑).totalDegree ≤ m := by
  apply (MvPolynomial.totalDegree_mul ..).trans
  simp
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  exact (𝔒 combinedCoefficientPolynomial_degree k).trans
    $ Nat.le_of_lt_succ $ Finset.mem_range.mp hk

def entryValuation
    (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix 𝔈 𝔈 ℝ) : 𝔘 → ℝ
  | Sum.inl ab => M0 ab.1 ab.2
  | Sum.inr ⟨i, ab⟩ => M i ab.1 ab.2

theorem eval_renamed_series (f : V → W) values
    (P : PowerSeries $ MvPolynomial V ℝ ) :
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) values)
      (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) $ values ∘ f ) P := by
  ext k
  exact MvPolynomial.eval_rename f values _

𝗇 𝔉 MvPolynomial.eval₂Hom (RingHom.id ℝ) $ entryValuation M0 M
theorem inverseVariableSeries_eval n0 (dims : 𝔅) lo hi
    M0
    M a b :
    PowerSeries.map 𝔉
      𝔍 = kernelSeries lo hi M0 a b := by
  rw [inverseVariableSeries, eval_renamed_series]
  exact congrArg (fun A => A a b) $ variableKernelSeries_map_eval lo hi M0

𝗇 𝔗 (kernelSeries lo hi $ M i ).det
theorem determinantVariableSeries_eval n0 dims lo hi
    M0
    M (i : Fin N) :
    PowerSeries.map 𝔉
      𝔏 = 𝔗 := by
  rw [determinantVariableSeries, eval_renamed_series]
  ext k
  exact determinantCoefficientPolynomial_eval lo hi (M i) k

𝗇 𝔄 kernelSeries lo hi M0 a b * ∏ i, 𝔗
theorem combinedVariableSeries_eval n0 (dims : 𝔅) lo hi
    M0
    M a b :
    PowerSeries.map 𝔉
      𝔐 =
      𝔄 := by
  simp only [combinedVariableSeries, map_mul, map_prod,
    inverseVariableSeries_eval, determinantVariableSeries_eval]

𝗇 𝔖 entryValuation M0 M
theorem combinedCoefficientPolynomial_eval n0 (dims : 𝔅) lo hi
    M0
    M a b k :
    MvPolynomial.eval 𝔖
      𝔎 =
      PowerSeries.coeff k 𝔄 := by
  have he := congrArg ( PowerSeries.coeff k )
    $ 𝔚 combinedVariableSeries_eval M0 M a b
  assumption

theorem truncationEntryPolynomial_eval n0 (dims : 𝔅) lo hi
    M0
    M a b m :
    MvPolynomial.eval 𝔖 𝔑 =
      𝔊 *
        ∑ k ∈ Finset.range 𝔔,
          PowerSeries.coeff k 𝔄 := by
  simp [truncationEntryPolynomial, combinedCoefficientPolynomial_eval]
