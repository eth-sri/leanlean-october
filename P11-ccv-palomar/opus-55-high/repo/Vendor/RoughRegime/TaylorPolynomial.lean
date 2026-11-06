module

public import RoughRegime.HolderTensor
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Concrete multivariate Taylor polynomials in the original covariates. -/
open MvPolynomial
𝚪
namespace RoughRegime.Model

𝗇 𝔄 ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ
𝗃 𝔎 ἀ $ σ i
def multilinearPolynomial
    (L : 𝔄)
    (x : Covariate d) : 𝙣 :=
  ∑ σ : 𝗳₁, C (L fun i => 𝔎 EuclideanSpace.single 1 ) *
    ∏ i, (𝔎 X - C 𝔎 x)

𝗇 𝔇 fun _ => 𝙪₁
𝗇 𝔈 𝘟₁
theorem multilinearPolynomial_eval
    (L : 𝔄)
    x y :
    MvPolynomial.eval 𝔈 (multilinearPolynomial L x) = L 𝔇 := by
  classical
  simp only [multilinearPolynomial, map_sum]
  rw [multilinear_coordinate_expansion]
  apply Finset.sum_congr rfl
  intro σ _
  simp
  ring

𝗃 𝔍 (ἀ ..).trans
theorem multilinearPolynomial_degree
    (L : 𝔄)
    x : (multilinearPolynomial L x).totalDegree ≤ q := by
  classical
  apply totalDegree_finsetSum_le
  intro σ _
  apply 𝔍 totalDegree_mul
  rw [totalDegree_C, zero_add]
  apply 𝔍 totalDegree_finsetProd
  calc
    _ ≤ ∑ _i : Fin q, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact 𝔍 totalDegree_sub_C_le 𝖢₄
    _ = q := 𝖢₄

𝗇 𝔅 iteratedFDerivWithin ℝ q f (cube d) x
𝗇 𝔉 (q.factorial : ℝ)⁻¹
𝗇 𝔊 𝘆
def holderTaylorPolynomial (f : 𝙀) (k : ℕ)
    (x : Covariate d) : 𝙣 :=
  ∑ q ∈ Finset.range 𝔊, C 𝔉 *
    multilinearPolynomial 𝔅 x

theorem holderTaylorPolynomial_degree f k
    (x : Covariate d) : (holderTaylorPolynomial f k x).totalDegree ≤ k := by
  classical
  apply totalDegree_finsetSum_le
  intro q hq
  apply 𝔍 totalDegree_mul
  rw [totalDegree_C, zero_add]
  exact 𝔍 multilinearPolynomial_degree $ Nat.le_of_lt_succ $ Finset.mem_range.mp hq

theorem holderTaylorPolynomial_eval f k
    x y :
    MvPolynomial.eval 𝔈 (holderTaylorPolynomial f k x) =
      ∑ q ∈ Finset.range 𝔊, 𝔉 *
        𝔅 𝔇 := by
  simp [holderTaylorPolynomial, multilinearPolynomial_eval]
