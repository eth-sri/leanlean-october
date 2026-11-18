module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Mathlib's actual smooth compact test space on the whole real line. -/
abbrev BellmanRealTest := TestFunction (⊤ : TopologicalSpace.Opens ℝ) ℝ (⊤ : ℕ∞)

/-- The ordinary derivative of a real smooth compact test, in the same Mathlib test space. -/
def bellmanTestDerivative (φ : BellmanRealTest) : BellmanRealTest where
  toFun := deriv φ
  contDiff' := (contDiff_infty_iff_deriv.mp φ.contDiff).2
  hasCompactSupport' := φ.hasCompactSupport.deriv
  tsupport_subset' := subset_univ _

/-- A test-space linear functional annihilating all derivatives is a constant distribution. -/
theorem bellman_test_derivative_kernel (L : BellmanRealTest →ₗ[ℝ] ℝ)
    (hzero : ∀ ψ : BellmanRealTest, L (bellmanTestDerivative ψ) = 0) :
    ∃ c : ℝ, ∀ φ : BellmanRealTest, L φ = c * (∫ x, φ x)  := by
  have bellman_exists_test_primitive (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hm : (∫ x, φ x) = 0) :
      ∃ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ deriv ψ = φ := by
    by_cases hn : (tsupport φ).Nonempty
    · obtain ⟨a₀, _, hmin⟩ := hc.exists_isMinOn hn continuousOn_id
      obtain ⟨b₀, _, hmax⟩ := hc.exists_isMaxOn hn continuousOn_id
      let a := a₀ - 1
      let b := b₀ + 1
      let ψ : ℝ → ℝ := fun t => ∫ x in a..t, φ x
      have hleft : ∀ t : ℝ, t < a → ψ t = 0 := by
        intro t ht
        rw [show ψ t = ∫ x in a..t, φ x from rfl,
          intervalIntegral.integral_of_ge ht.le]
        apply neg_eq_zero.mpr
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        apply image_eq_zero_of_notMem_tsupport
        intro hs
        have hl : a₀ ≤ x := hmin hs
        have hr := hx.2
        dsimp [a] at hr
        linarith
      have hright : ∀ t : ℝ, b < t → ψ t = 0 := by
        intro t ht
        change (∫ x in a..t, φ x) = 0
        rw [intervalIntegral.integral_eq_integral_of_support_subset]
        · exact hm
        · intro x hx
          have hs := subset_tsupport φ hx
          have hl := hmin hs
          have hr := hmax hs
          dsimp [a, b] at *
          constructor <;> linarith
      have hsupp : Function.support ψ ⊆ Icc a b := by
        intro t ht
        rcases lt_or_ge t a with hta | hta
        · exact False.elim (ht (hleft t hta))
        · have htb : t ≤ b := by
            by_contra hn
            exact ht (hright t (lt_of_not_ge hn))
          exact ⟨hta, htb⟩
      have hderiv : deriv ψ = φ := by
        funext t
        exact hφ.continuous.deriv_integral _ a t
      refine ⟨ψ, ?_, isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hsupp isClosed_Icc), hderiv⟩
      apply contDiff_infty_iff_deriv.mpr
      refine ⟨?_, ?_⟩
      · intro t
        exact (hφ.continuous.integral_hasStrictDerivAt a t).hasDerivAt.differentiableAt
      · rw [hderiv]
        exact hφ
    · have hz : φ = 0 := by
        funext t
        exact image_eq_zero_of_notMem_tsupport (fun ht => hn ⟨t, ht⟩)
      refine ⟨0, contDiff_zero_fun, HasCompactSupport.zero, ?_⟩
      rw [hz]
      exact deriv_zero
  let raw : ContDiffBump (0 : ℝ) :=
    { rIn := 1
      rOut := 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let ρ : BellmanRealTest :=
    { toFun := raw.normed volume
      contDiff' := raw.contDiff_normed
      hasCompactSupport' := raw.hasCompactSupport_normed
      tsupport_subset' := subset_univ _ }
  have hρ : (∫ x, ρ x) = 1 := raw.integral_normed
  refine ⟨L ρ, ?_⟩
  intro φ
  let a : ℝ := ∫ x, φ x
  let θ : BellmanRealTest := φ - a • ρ
  have hiφ : Integrable (fun x => φ x) volume :=
    φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hiρ : Integrable (fun x => ρ x) volume :=
    ρ.contDiff.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport
  have hmean : (∫ x, θ x) = 0 := by
    change (∫ x, φ x - a * ρ x) = 0
    rw [integral_sub hiφ (hiρ.const_mul a), integral_const_mul, hρ]
    ring
  obtain ⟨ψ, hψ, hcψ, hdψ⟩ :=
    bellman_exists_test_primitive θ θ.contDiff θ.hasCompactSupport hmean
  let Ψ : BellmanRealTest := ⟨ψ, hψ, hcψ, subset_univ _⟩
  have he : bellmanTestDerivative Ψ = θ := by
    apply DFunLike.ext
    intro x
    exact congrFun hdψ x
  have hz := hzero Ψ
  rw [he] at hz
  change L (φ - a • ρ) = 0 at hz
  rw [map_sub, map_smul] at hz
  change L φ - a * L ρ = 0 at hz
  linarith


/-- The ordinary derivative is a linear map on the native real compact test space. -/
def bellmanTestDerivativeLinearMap : BellmanRealTest →ₗ[ℝ] BellmanRealTest where
  toFun := bellmanTestDerivative
  map_add' φ ψ := by
    apply DFunLike.ext
    intro x
    change deriv (fun y => φ y + ψ y) x = deriv φ x + deriv ψ x
    exact deriv_add (φ.contDiff.differentiable (by simp) x)
      (ψ.contDiff.differentiable (by simp) x)
  map_smul' c φ := by
    apply DFunLike.ext
    intro x
    change deriv (fun y => c * φ y) x = c * deriv φ x
    exact deriv_const_mul c (φ.contDiff.differentiable (by simp) x)

/-- The actual weighted measure pairing, using Mathlib's integral-against-test linear map. -/
def bellmanWeightedTestIntegral (μ : Measure ℝ) (g : ℝ → ℝ) : BellmanRealTest →ₗ[ℝ] ℝ :=
  (TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) μ g).toLinearMap

/-- For a locally integrable weight the concrete test pairing is its literal measure integral. -/
theorem bellmanWeightedTestIntegral_apply (μ : Measure ℝ) (g : ℝ → ℝ)
    (hg : LocallyIntegrable g μ) (φ : BellmanRealTest) :
    bellmanWeightedTestIntegral μ g φ = ∫ x, φ x * g x ∂μ := by
  exact TestFunction.integralAgainstBilinCLM_eq_integral (hg.locallyIntegrableOn Set.univ)

end HypoellipticAleksandrov.KineticAleksandrov

