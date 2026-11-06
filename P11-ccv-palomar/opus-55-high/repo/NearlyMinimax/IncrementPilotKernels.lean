module

public import NearlyMinimax.IncrementPilotCoordinates
public import NearlyMinimax.IncrementPilotLocalization
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Exact global derivative kernels for the actual unbiased dyadic pilot.
They preserve the actual local raw energies and parent support, and their
centered factorial expansion is exactly the original polynomial pilot error. -/

open MeasureTheory ProbabilityTheory Matrix MvPolynomial
𝚺
𝚨
𝚭
𝚩

𝗇 𝔏 𝗣
𝗇 𝔖 𝖼₁
𝗇 𝔄 incrementFinScalar 𝔏 C.densityLower C.densityUpper 𝔖 y m row
𝗇 𝔇 dyadicIncrementRawMean θ j x
𝗇 𝔐 𝗸₁ 𝔄 𝔇
def dyadicIncrementKernel (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin 𝔏 → ℝ) (k : ℕ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin k => Fin (Fintype.card $ IncrementGlobalIndex d C.order j ) → ℝ) ℝ :=
  (𝔐).compContinuousLinearMap
         fun _ => incrementPilotCoordinate j x

𝗇 𝔅 𝖳₂ x y m row
𝗇 𝔈 fun i => 𝗤₁
𝗇 𝔉 dyadicIncrementRawVector j x $ z i
𝗇 𝔑 Fin k → Observation d
theorem dyadicIncrementKernel_raw C θ
    j x y m
    row k (z : 𝔑) :
    𝔅 k 𝔈 =
      𝔐 fun i => 𝔉 := by
  simp [dyadicIncrementKernel]

𝗇 𝔊 rowIncrementPolynomial 𝔏 C.densityLower C.densityUpper 𝔖 y m row
𝗇 𝔍 fun z => eval z F
theorem dyadicIncrementKernel_symmetric C
    θ j (x : Covariate d) y m
    row k
    (σ : Equiv.Perm $ Fin k ) v :
    𝔅 k (fun i => v $ σ i ) =
      𝔅 k v := by
  let F := 𝔊
  have hF : 𝔍 = 𝔄 := by
    funext z
    exact rowIncrementPolynomial_eval ..
  simp only [dyadicIncrementKernel]
  rw [← hF]
  exact (AnalyticOnNhd.eval_mvPolynomial F).analyticOn.iteratedFDeriv_comp_perm
    (fun i => incrementPilotCoordinate j x $ v i ) σ

𝗇 𝔓 𝘮
theorem dyadicIncrementKernel_disjoint C
    θ j k (hk : 𝖰) x v
    (hxv : dyadicPilotLabel 𝔓 x ≠ dyadicPilotLabel 𝔓 v)
    y t m l row s
    (z : 𝔑) :
    𝔅 k 𝔈 *
      𝖳₂ v t l s k 𝔈 = 0 := by
  rw [dyadicIncrementKernel_raw, dyadicIncrementKernel_raw]
  exact dyadic_increment_raw_kernels_disjoint hk j x v hxv _ _ z

𝗇 𝔎 𝗤₁ - 𝚆₁
theorem dyadicIncrementKernel_centered C
    θ (hθ : 𝙟) j x
    y m row k
    (z : 𝔑) :
    𝔅 k
      (fun i => 𝔎) =
      𝔐
         fun i => 𝔉 - 𝔇 := by
  simp [dyadicIncrementKernel, incrementPilotCoordinate_mean C θ hθ]

𝗇 𝔒 𝗙₁
𝗇 𝔔 m + 𝔏 + 1
/-- Exact translation of the original coefficient pilot to a single fixed
global feature vector, with no covariance or mean premise. -/
theorem dyadicPolynomialPilot_centered_global (C : ModelConstants d)
    [Nonempty 𝘘] θ (hθ : 𝙟)
    n j x y m
    row
    (hdegree : 𝔔 ≤ n) z :
    LiftL2.centeredKernelExpansion 0
      (fun r : Fin 𝔔 =>
        𝔅 𝔒)
      (fun i z => 𝔎) z =
      𝘌₁ z -
        𝔄 𝔇 := by
  let F := 𝔊
  have hF : 𝔍 = 𝔄 := by
    funext z
    exact rowIncrementPolynomial_eval ..
  have he := LiftL2.polynomialLift_centering_l2 F
    (fun i (z : 𝙌) => 𝔉)
    𝔇 (rowIncrementPolynomial_degree ..) hdegree
  change _ = RoughRegime.Upper.polynomialLift F
    (fun i z => 𝔉) z - _
  rw [he]
  change _ = eval 𝔇 F + _ - _
  rw [rowIncrementPolynomial_eval, add_sub_cancel_left]
  simp only [LiftL2.centeredKernelExpansion, zero_add]
  apply Finset.sum_congr rfl
  intro r _
  apply congrArg fun a => ( (𝔒).factorial *
    (n.descFactorial 𝔒 : ℝ))⁻¹ * a
  apply Finset.sum_congr rfl
  intro e _
  rw [hF]
  exact dyadicIncrementKernel_centered C θ hθ j x y m row _ fun i => z $ e i
