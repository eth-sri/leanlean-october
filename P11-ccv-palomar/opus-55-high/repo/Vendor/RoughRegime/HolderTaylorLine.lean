module

public import RoughRegime.TaylorPolynomial
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact within derivatives and Taylor polynomials along cube segments. -/
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model

def linePath (x y : Covariate d) : ℝ →ᴬ[ℝ] Covariate d :=
  ContinuousAffineMap.lineMap x y

𝗇 𝔄 𝗃
𝗇 𝔅 linePath x y
𝗇 𝔉 𝗞₂
𝗇 𝔊 𝚏₂
theorem linePath_mem_cube x y (hx : 𝔉)
    (hy : 𝔊) z (hz : z ∈ 𝔄) : 𝔅 z ∈ cube d := (convex_cube d).segment_subset hx hy $ lineMap_mem_segment ℝ x y hz

section

variable (x y : Covariate d)

include y x

@[simp] theorem linePath_zero : 𝔅 0 = x := by
  simp [linePath, ContinuousAffineMap.coe_lineMap_eq]

@[simp] theorem linePath_one : 𝔅 1 = y := by
  simp [linePath, ContinuousAffineMap.coe_lineMap_eq]

@[simp] theorem linePath_contLinear_one :
    (𝔅).contLinear 1 = 𝙪₁ := by
  simp [linePath]

end

𝗇 𝔇 ContDiffOn ℝ k f $ cube d
𝗇 𝔈 fun z hz => linePath_mem_cube x y hx hy z hz
𝗇 𝔍 f ∘ 𝔅
theorem linePath_iteratedDerivWithin {d k q : ℕ} (f : 𝙀)
    (hf : 𝔇) (hq : q ≤ k)
    x y (hx : 𝔉) (hy : 𝔊)
    z (hz : z ∈ 𝔄) :
    iteratedDerivWithin q 𝔍 𝔄 z =
      iteratedFDerivWithin ℝ q f (cube d) (𝔅 z) fun _ => 𝙪₁ := by
  have hseries := ((hf.ftaylorSeriesWithin $ uniqueDiffOn_cube d ).comp_continuousAffineMap
    𝔅).mono 𝔈
  have he := hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by exact_mod_cast hq) (uniqueDiffOn_Icc 𝖠₄ ) hz
  simpa only [iteratedDerivWithin, ftaylorSeriesWithin,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, linePath_contLinear_one] using congrArg (fun L => L 𝘋₁) he.symm

theorem linePath_contDiffOn (f : 𝙀)
    (hf : 𝔇)
    x y (hx : 𝔉) (hy : 𝔊) :
    ContDiffOn ℝ k 𝔍 𝔄 := hf.comp (𝔅).contDiff.contDiffOn 𝔈

theorem linePath_taylor_eq {d k : ℕ} f
    (hf : 𝔇)
    x y (hx : 𝔉) (hy : 𝔊) :
    taylorWithinEval 𝔍 k 𝔄 0 1 =
      MvPolynomial.eval 𝘟₁ (holderTaylorPolynomial f k x) := by
  rw [taylor_within_apply, holderTaylorPolynomial_eval]
  apply Finset.sum_congr rfl
  intro q hq
  rw [linePath_iteratedDerivWithin f hf (Nat.le_of_lt_succ $ Finset.mem_range.mp hq )
    x y hx hy 0 𝖢₄ , linePath_zero]
  simp
