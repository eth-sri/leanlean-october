module

public import HypoellipticAleksandrov.Parabolic.SmoothGradientTimeEnergy
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Lean.Elab.Tactic.SolveByElim
import all HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
import all HypoellipticAleksandrov.Parabolic.SmoothGradientTimeEnergy
import all HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.velocityGradient_component_contDiff from HypoellipticAleksandrov.Parabolic.SmoothGradientTimeEnergy
section
open private HypoellipticAleksandrov.Parabolic.velocityHessian_compact from HypoellipticAleksandrov.Parabolic.WeakJetProduct
private alias _semanticProof_02a680b7b556 := HypoellipticAleksandrov.Parabolic.velocityHessian_compact
end


/-!
# Weak gradient time-energy identity

This file begins the compatible localization of the selected weak spacetime
jet used in the weak gradient time-energy identity.
-/

 public section



open MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy

/-- Strong global `L²` convergence descends to every restricted carrier,
without a measurability or finite-measure assumption on the carrier. -/
private theorem tendsto_eLpNorm_two_restrict_of_global
    {d : ℕ} {l : Filter ℝ} (S : HypoellipticAleksandrov.Parabolic.Region d)
    (f : ℝ → HypoellipticAleksandrov.Parabolic.ScalarField d) (f₀ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (h : Filter.Tendsto
      (fun a => eLpNorm (fun z => f a z - f₀ z) (2 )
        ) l (𝓝 0)) :
    Filter.Tendsto
      (fun a => eLpNorm (fun z => f a z - f₀ z) (2 )
        ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun a =>
      eLpNorm_mono_measure (fun z => f a z - f₀ z) Measure.restrict_le_self)

variable {d : ℕ}

variable {l : Filter ℝ}

variable (S : HypoellipticAleksandrov.Parabolic.Region d)

/-- After restriction, multiplication by a fixed `L∞` field preserves
strong `L²` convergence. -/
private theorem tendsto_eLpNorm_two_mul_restrict

    (c : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (f : ℝ → HypoellipticAleksandrov.Parabolic.ScalarField d) (f₀ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hc : MemLp c ∞ ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (h : Filter.Tendsto
      (fun a => eLpNorm (fun z => f a z - f₀ z) (2 )
        ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (𝓝 0)) :
    Filter.Tendsto
      (fun a => eLpNorm (fun z => c z * f a z - c z * f₀ z)
        (2 ) ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
      l (𝓝 0) := HypoellipticAleksandrov.Analysis.tendsto_eLpNorm_mul_sub_mul_of_tendsto_eLpNorm_two
    c f f₀ hc h

/-- Restricted scalar-product integrals converge when both factors converge
strongly in restricted `L²` and have the corresponding eventual membership. -/
private theorem tendsto_integral_mul_restrict

    (f g : ℝ → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (f₀ g₀ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ∀ᶠ a in l, MemLp (f a) (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hg : ∀ᶠ a in l, MemLp (g a) (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hf₀ : MemLp f₀ (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hg₀ : MemLp g₀ (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hft : Filter.Tendsto
      (fun a => eLpNorm (fun z => f a z - f₀ z) (2 )
        ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (𝓝 0))
    (hgt : Filter.Tendsto
      (fun a => eLpNorm (fun z => g a z - g₀ z) (2 )
        ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (𝓝 0)) :
    Filter.Tendsto
      (fun a => ∫ z in S, f a z * g a z)
      l (𝓝 (∫ z in S, f₀ z * g₀ z)) := HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    f g f₀ g₀ hf hg hf₀ hg₀ hft hgt

/-- A fixed bounded coefficient may be absorbed into the first factor of a
restricted `L² × L²` product limit. -/
private theorem tendsto_integral_fixed_mul_mul_restrict

    (c : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (f g : ℝ → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (f₀ g₀ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hc : MemLp c ∞ ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hf : ∀ᶠ a in l, MemLp (f a) (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hg : ∀ᶠ a in l, MemLp (g a) (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hf₀ : MemLp f₀ (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hg₀ : MemLp g₀ (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hft : Filter.Tendsto
      (fun a => eLpNorm (fun z => f a z - f₀ z) (2 )
        ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (𝓝 0))
    (hgt : Filter.Tendsto
      (fun a => eLpNorm (fun z => g a z - g₀ z) (2 )
        ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) l (𝓝 0)) :
    Filter.Tendsto
      (fun a => ∫ z in S, c z * f a z * g a z)
      l (𝓝 (∫ z in S, c z * f₀ z * g₀ z)) := tendsto_integral_mul_restrict S
    (fun a z => c z * f a z) g (fun z => c z * f₀ z) g₀
    (by
        filter_upwards [hf] with a hfa
        simpa only [mul_comm] using hfa.mul' hc) hg (by
        simpa only [mul_comm] using hf₀.mul' hc) hg₀ (tendsto_eLpNorm_two_mul_restrict S c f f₀ hc hft) hgt

/-- Coordinatewise scalar limits assemble over the exact finite coordinate
set, including the empty `Fin 0` case. -/
private theorem tendsto_sum_coordinates
      (F : Fin d → ℝ → ℝ)
    (F₀ : Fin d → ℝ)
    (hF : ∀ i : Fin d, Filter.Tendsto (F i) l (𝓝 (F₀ i))) : type_of% (tendsto_finset_sum Finset.univ fun i _ => hF i) := tendsto_finset_sum Finset.univ fun i _ => hF i

variable (S : HypoellipticAleksandrov.Parabolic.Region d)

/-- A separated spacetime multiplier is globally bounded when both its time
and spatial factors are continuous and compactly supported.  In particular,
compactness is never falsely attributed to the time factor pulled back alone. -/
private theorem separated_multiplier_memLp_top_restrict

    (a : ℝ → ℝ) (ha : Continuous a) (haCompact : HasCompactSupport a)
    (c : PDE.ScalarField d) (hc : Continuous c) (hcCompact : HasCompactSupport c) :
    MemLp (fun z : TimeVelocity d => a z.1 * c z.2) ∞
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S) := (((ha.comp continuous_fst).mul (hc.comp continuous_snd)).memLp_of_hasCompactSupport (by

      apply HasCompactSupport.of_support_subset_isCompact (haCompact.isCompact.prod hcCompact.isCompact)
      intro z hz


      exact ⟨subset_tsupport a (Function.mem_support.mpr (by
          intro hzero
          exact hz (by simp [hzero]))),
        subset_tsupport c (Function.mem_support.mpr (by
            intro hzero
            exact hz (by simp [hzero])))⟩)).restrict S

/-- The three literal coefficients in the coordinatewise energy limits are
bounded on every restricted carrier, with compactness supplied in both time
and velocity variables. -/
private theorem concrete_energy_multipliers_memLp_top

    (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (hζCompact : HasCompactSupport ζ) :
    (∀ i : Fin d, MemLp
      (fun z : TimeVelocity d => (-2 : ℝ) * ζ z.1 *
        (η z.2 * spatialPartial i η z.2)) ∞
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) ∧
    MemLp (fun z : TimeVelocity d => (-1 : ℝ) * ζ z.1 * η z.2 ^ 2) ∞
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S) ∧
    MemLp (fun z : TimeVelocity d => _root_.deriv ζ z.1 * η z.2 ^ 2) ∞
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S) := by
  let sharedTerm_f570d3926c := (show (fun t => (fderiv ℝ ζ t : ℝ → ℝ) 1) = _root_.deriv ζ
    by
    funext t
    exact fderiv_apply_one_eq_deriv)
  have hpartialCont (i : Fin d) : Continuous (spatialPartial i η) := by
    unfold spatialPartial
    simpa using (hη.continuous_fderiv (by simp)).clm_apply continuous_const



  have hetaSqCont : Continuous (fun v => η v ^ 2) := hη.continuous.pow 2
  have hetaSqCompact : HasCompactSupport (fun v => η v ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hηCompact.mul_right (f' := η)
  constructor
  · intro i
    have hspatialCont : Continuous (fun v => η v * spatialPartial i η v) :=
      hη.continuous.mul (hpartialCont i)
    have hspatialCompact : HasCompactSupport
        (fun v => η v * spatialPartial i η v) :=
      hηCompact.mul_right
    have hbase := separated_multiplier_memLp_top_restrict S ζ hζ.continuous
      hζCompact _ hspatialCont hspatialCompact
    have hscaled := hbase.const_smul (-2 : ℝ)
    convert hscaled using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  constructor
  · have hbase := separated_multiplier_memLp_top_restrict S ζ hζ.continuous
      hζCompact _ hetaSqCont hetaSqCompact
    have hscaled := hbase.const_smul (-1 : ℝ)
    convert hscaled using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · exact separated_multiplier_memLp_top_restrict S _ (show _ by
      rw [← sharedTerm_f570d3926c]
      exact (hζ.continuous_fderiv (by simp)).clm_apply continuous_const) (show _ by
      rw [← sharedTerm_f570d3926c]
      exact hζCompact.fderiv_apply ℝ 1)
      _ hetaSqCont hetaSqCompact

private theorem eventually_spacetimeMollification_memLp_restrict
      (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 ) ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, MemLp
      (SpacetimeMollifier.spacetimeMollification ε f) (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S) := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (SpacetimeMollifierL2.spacetimeMollification_memLp hε f hf).restrict S

section
variable (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η) (hηCompact : HasCompactSupport η) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ) (hζCompact : HasCompactSupport ζ) (rt : HypoellipticAleksandrov.Parabolic.ScalarField d) (ri rii : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)

section
variable (hrt : MemLp rt (2 ) volume) (hri : ∀ i, MemLp (ri i) (2 ) volume) (hrii : ∀ i, MemLp (rii i) (2 ) volume)

include hη hηCompact hζ hζCompact hrt hri hrii
/-- The three literal coordinate products used by the weak energy identity
converge for the common positive-radius spacetime mollifier. -/
private theorem coordinate_energy_product_limits



    (i : Fin d) :
    Filter.Tendsto (fun ε  => ∫ z in S,
        ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) *
          SpacetimeMollifier.spacetimeMollification ε rt z *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) *
          rt z * ri i z)) ∧
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
          SpacetimeMollifier.spacetimeMollification ε rt z *
          SpacetimeMollifier.spacetimeMollification ε (rii i) z)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * rt z * rii i z)) ∧
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        (_root_.deriv ζ z.1 * η z.2 ^ 2) *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z * ri i z)) := by
  rcases concrete_energy_multipliers_memLp_top S η hη hηCompact ζ hζ hζCompact with
    ⟨hc₁, hc₂, hc₃⟩
  have hrtE := eventually_spacetimeMollification_memLp_restrict S rt hrt
  have hriE := eventually_spacetimeMollification_memLp_restrict S (ri i) (hri i)

  have hrtR := hrt.restrict S
  have hriR := (hri i).restrict S

  have hrtT := tendsto_eLpNorm_two_restrict_of_global S
    (fun ε => SpacetimeMollifier.spacetimeMollification ε rt) rt
    (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub rt hrt)
  have hriT := tendsto_eLpNorm_two_restrict_of_global S
    (fun ε => SpacetimeMollifier.spacetimeMollification ε (ri i)) (ri i)
    (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub (ri i) (hri i))
  have hriiT := tendsto_eLpNorm_two_restrict_of_global S
    (fun ε => SpacetimeMollifier.spacetimeMollification ε (rii i)) (rii i)
    (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub (rii i) (hrii i))
  exact ⟨
    tendsto_integral_fixed_mul_mul_restrict S _ _ _ rt (ri i)
      (hc₁ i) hrtE hriE hrtR hriR hrtT hriT,
    tendsto_integral_fixed_mul_mul_restrict S _ _ _ rt (rii i)
      hc₂ hrtE (eventually_spacetimeMollification_memLp_restrict S (rii i) (hrii i)) hrtR ((hrii i).restrict S) hrtT hriiT,
    tendsto_integral_fixed_mul_mul_restrict S _ _ _ (ri i) (ri i)
      hc₃ hriE hriE hriR hriR hriT hriT⟩

/-- The three coordinate limits assemble into the exact finite sums used on
the two sides of the localized weak energy identity. -/
private theorem summed_energy_product_limits


     :
    Filter.Tendsto (fun ε : ℝ => ∑ i : Fin d,
        ((∫ z in S, ((-2 : ℝ) * ζ z.1 *
            (η z.2 * spatialPartial i η z.2)) *
            SpacetimeMollifier.spacetimeMollification ε rt z *
            SpacetimeMollifier.spacetimeMollification ε (ri i) z) +
          ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
            SpacetimeMollifier.spacetimeMollification ε rt z *
            SpacetimeMollifier.spacetimeMollification ε (rii i) z))
      (𝓝[>] 0) (𝓝 (∑ i : Fin d,
        ((∫ z in S, ((-2 : ℝ) * ζ z.1 *
            (η z.2 * spatialPartial i η z.2)) * rt z * ri i z) +
          ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
            rt z * rii i z))) ∧
    Filter.Tendsto (fun ε : ℝ => ∑ i : Fin d,
        ∫ z in S, (_root_.deriv ζ z.1 * η z.2 ^ 2) *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z)
      (𝓝[>] 0) (𝓝 (∑ i : Fin d,
        ∫ z in S, (_root_.deriv ζ z.1 * η z.2 ^ 2) *
          ri i z * ri i z)) := by
  have hcoord (i : Fin d) := coordinate_energy_product_limits S η hη hηCompact
    ζ hζ hζCompact rt ri rii hrt hri hrii i
  constructor
  · apply tendsto_sum_coordinates
    intro i
    exact (hcoord i).1.add (hcoord i).2.1
  · apply tendsto_sum_coordinates
    intro i
    exact (hcoord i).2.2
end


include hη hηCompact hζ hζCompact in
/-- The coordinate-product presentation is exactly the literal localized
divergence and gradient-square presentation; every integral rewrite is backed
by explicit `L² × L²` integrability. -/
private theorem energy_coordinate_integral_algebra


    (hrt : MemLp rt (2 ) ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hri : ∀ i, MemLp (ri i) (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S))
    (hrii : ∀ i, MemLp (rii i) (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S)) :
    (∑ i : Fin d,
        ((∫ z in S, ((-2 : ℝ) * ζ z.1 *
            (η z.2 * spatialPartial i η z.2)) * rt z * ri i z) +
          ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
            rt z * rii i z)) =
      ∫ z in S, ζ z.1 * rt z *
        localizedGradientDivergence η
          (fun z i => ri i z) (fun z i _ => rii i z) z ∧
    (∑ i : Fin d, ∫ z in S,
        (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z * ri i z) =
      ∫ z in S, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ i : Fin d, ri i z ^ 2 := by
  let μ := (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S
  rcases concrete_energy_multipliers_memLp_top S η hη hηCompact ζ hζ hζCompact with
    ⟨hc₁, hc₂, hc₃⟩
  let A  := fun i z =>
    ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) * rt z * ri i z
  let B  := fun i z =>
    ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * rt z * rii i z
  let C  := fun i z =>
    (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z * ri i z
  have hA (i : Fin d) : Integrable (A i) μ := by
    have hw : MemLp (fun z =>
        ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) * rt z)
        (2 ) μ := by
      simpa only [mul_comm] using hrt.mul' (hc₁ i)
    simpa only [A, Pi.mul_def] using hw.integrable_mul (hri i)
  have hB (i : Fin d) : Integrable (B i) μ := by
    have hw : MemLp (fun z => ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * rt z)
        (2 ) μ := by
      simpa only [mul_comm] using hrt.mul' hc₂
    simpa only [B, Pi.mul_def] using hw.integrable_mul (hrii i)
  have hC (i : Fin d) : Integrable (C i) μ := by
    have hw : MemLp (fun z => (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z)
        (2 ) μ := by
      simpa only [mul_comm] using (hri i).mul' hc₃
    simpa only [C, Pi.mul_def] using hw.integrable_mul (hri i)
  constructor
  · calc
      _ = ∑ i : Fin d, ∫ z, A i z + B i z ∂μ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_add (hA i) (hB i)]
      _ = ∫ z, ∑ i : Fin d, (A i z + B i z) ∂μ := (integral_finset_sum Finset.univ (fun i _ => (hA i).add (hB i))).symm
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          simp only [A, B, localizedGradientDivergence]
          rw [← Finset.sum_neg_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
  · rw [← integral_finset_sum Finset.univ (fun i _ => hC i)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      simp only [C, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

include hη hηCompact hζ hζCompact in
/-- The exact localized divergence and gradient-square integrals converge for
the one common mollification of all localized representatives. -/
private theorem localized_energy_integral_limits


    (hrt : MemLp rt (2 ) )
    (hri : ∀ i, MemLp (ri i) (2 ) )
    (hrii : ∀ i, MemLp (rii i) (2 ) ) :
    Filter.Tendsto (fun ε  => ∫ z in S,
        ζ z.1 * SpacetimeMollifier.spacetimeMollification ε rt z *
          localizedGradientDivergence η
            (fun z i => SpacetimeMollifier.spacetimeMollification ε (ri i) z)
            (fun z i _j => SpacetimeMollifier.spacetimeMollification ε (rii i) z) z) (𝓝[>] 0) (𝓝 (∫ z in S,
          ζ z.1 * rt z * localizedGradientDivergence η
            (fun z i => ri i z) (fun z i _j => rii i z) z)) ∧
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d,
            SpacetimeMollifier.spacetimeMollification ε (ri i) z ^ 2)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        _root_.deriv ζ z.1 * η z.2 ^ 2 * ∑ i : Fin d, ri i z ^ 2)) := by
  have hsum := summed_energy_product_limits S η hη hηCompact ζ hζ hζCompact
    rt ri rii hrt hri hrii
  have halg₀ := energy_coordinate_integral_algebra S η hη hηCompact ζ hζ hζCompact
    rt ri rii (hrt.restrict S) (fun i => (hri i).restrict S)
      (fun i => (hrii i).restrict S)
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ((∑ i : Fin d,
          ((∫ z in S, ((-2 : ℝ) * ζ z.1 *
              (η z.2 * spatialPartial i η z.2)) *
              SpacetimeMollifier.spacetimeMollification ε rt z *
              SpacetimeMollifier.spacetimeMollification ε (ri i) z) +
            ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
              SpacetimeMollifier.spacetimeMollification ε rt z *
              SpacetimeMollifier.spacetimeMollification ε (rii i) z)) =
        ∫ z in S, ζ z.1 * SpacetimeMollifier.spacetimeMollification ε rt z *
          localizedGradientDivergence η
            (fun z i => SpacetimeMollifier.spacetimeMollification ε (ri i) z)
            (fun z i _j => SpacetimeMollifier.spacetimeMollification ε (rii i) z) z) ∧
      (∑ i : Fin d, ∫ z in S,
          (_root_.deriv ζ z.1 * η z.2 ^ 2) *
            SpacetimeMollifier.spacetimeMollification ε (ri i) z *
            SpacetimeMollifier.spacetimeMollification ε (ri i) z) =
        ∫ z in S, _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d,
            SpacetimeMollifier.spacetimeMollification ε (ri i) z ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply energy_coordinate_integral_algebra S η hη hηCompact ζ hζ hζCompact
      (SpacetimeMollifier.spacetimeMollification ε rt)
      (fun i => SpacetimeMollifier.spacetimeMollification ε (ri i))
      (fun i => SpacetimeMollifier.spacetimeMollification ε (rii i))
    · exact (SpacetimeMollifierL2.spacetimeMollification_memLp hε rt hrt).restrict S
    · intro i
      exact (SpacetimeMollifierL2.spacetimeMollification_memLp hε (ri i) (hri i)).restrict S
    · intro i
      exact (SpacetimeMollifierL2.spacetimeMollification_memLp hε (rii i) (hrii i)).restrict S
  constructor
  · rw [← halg₀.1]
    exact hsum.1.congr' (hevent.mono fun ε h => h.1)
  · rw [← halg₀.2]
    exact hsum.2.congr' (hevent.mono fun ε h => h.2)
end


/-- The two literal weak-energy target integrands are integrable directly
from the componentwise `L²` assumptions and bounded compact cutoffs. -/
private theorem weak_energy_targets_integrableOn

    (QW : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hQW : ParabolicMemLpOn S (2 ) QW)
    (hQG : ∀ i : Fin d,
      ParabolicMemLpOn S (2 ) (fun z => QG z i))
    (hQH : ∀ i : Fin d,
      ParabolicMemLpOn S (2 ) (fun z => QH z i i))
    (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (hζCompact : HasCompactSupport ζ) :
    IntegrableOn (fun z => ζ z.1 * QW z *
      localizedGradientDivergence η QG QH z) S  ∧
    IntegrableOn (fun z => _root_.deriv ζ z.1 * η z.2 ^ 2 *
      ∑ i : Fin d, QG z i ^ 2) S volume := by
  let μ := (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict S
  rcases concrete_energy_multipliers_memLp_top S η hη hηCompact ζ hζ hζCompact with
    ⟨hc₁, hc₂, hc₃⟩
  let A  := fun i z =>
    ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) * QW z * QG z i
  let B  := fun i z =>
    ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * QW z * QH z i i
  let C  := fun i z =>
    (_root_.deriv ζ z.1 * η z.2 ^ 2) * QG z i * QG z i
  have hA (i : Fin d) : Integrable (A i) μ := by
    have hw : MemLp (fun z =>
        ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) * QW z)
        (2 ) μ := by
      simpa only [mul_comm] using hQW.mul' (hc₁ i)
    simpa only [A, Pi.mul_def] using hw.integrable_mul (hQG i)
  have hB (i : Fin d) : Integrable (B i) μ := by
    have hw : MemLp (fun z => ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * QW z)
        (2 ) μ := by
      simpa only [mul_comm] using hQW.mul' hc₂
    simpa only [B, Pi.mul_def] using hw.integrable_mul (hQH i)
  have hC (i : Fin d) : Integrable (C i) μ := by
    have hw : MemLp (fun z => (_root_.deriv ζ z.1 * η z.2 ^ 2) * QG z i)
        (2 ) μ := by
      simpa only [mul_comm] using (hQG i).mul' hc₃
    simpa only [C, Pi.mul_def] using hw.integrable_mul (hQG i)
  constructor
  · apply (integrable_finset_sum Finset.univ fun i _ => (hA i).add (hB i)).congr
    exact Filter.Eventually.of_forall fun z => by
      simp only [A, B, localizedGradientDivergence]
      rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [Pi.add_apply]
      ring
  · apply (integrable_finset_sum Finset.univ fun i _ => hC i).congr
    exact Filter.Eventually.of_forall fun z => by
      simp only [C, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Plateau agreement on the product of cutoff supports identifies both
localized weighted integrands with the selected raw representatives globally. -/
private theorem weak_energy_integrands_eq_of_eqOn_cutoff_support
     (QW rt : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (ri rii : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (η : PDE.ScalarField d) (ζ : ℝ → ℝ)
    (hrt : Set.EqOn rt QW (tsupport ζ ×ˢ tsupport η))
    (hri : ∀ i, Set.EqOn (ri i) (fun z => QG z i)
      (tsupport ζ ×ˢ tsupport η))
    (hrii : ∀ i, Set.EqOn (rii i) (fun z => QH z i i)
      (tsupport ζ ×ˢ tsupport η)) :
    (∀ z, ζ z.1 * rt z * localizedGradientDivergence η
        (fun z i => ri i z) (fun z i _j => rii i z) z =
      ζ z.1 * QW z * localizedGradientDivergence η QG QH z) ∧
    ∀ z, _root_.deriv ζ z.1 * η z.2 ^ 2 * ∑ i : Fin d, ri i z ^ 2 =
      _root_.deriv ζ z.1 * η z.2 ^ 2 * ∑ i : Fin d, QG z i ^ 2 := by
  constructor
  · intro z
    by_cases ht : z.1 ∈ tsupport ζ
    · by_cases hv : z.2 ∈ tsupport η
      · rw [hrt ⟨ht, hv⟩]
        unfold localizedGradientDivergence
        congr 2
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only
        rw [hri i ⟨ht, hv⟩, hrii i ⟨ht, hv⟩]
      · have hzero  := image_eq_zero_of_notMem_tsupport hv
        simp [localizedGradientDivergence, hzero]
    · have hzero  := image_eq_zero_of_notMem_tsupport ht
      simp [hzero]
  · intro z
    by_cases ht : z.1 ∈ tsupport ζ
    · by_cases hv : z.2 ∈ tsupport η
      · apply congrArg (fun x : ℝ => _root_.deriv ζ z.1 * η z.2 ^ 2 * x)
        apply Finset.sum_congr rfl
        intro i hi
        rw [hri i ⟨ht, hv⟩]
      · have hzero  := image_eq_zero_of_notMem_tsupport hv
        simp [hzero]
    · have hzero : _root_.deriv ζ z.1 = 0 := by
        rw [← fderiv_apply_one_eq_deriv, fderiv_of_notMem_tsupport ℝ ht]
        rfl
      simp [hzero]

/-- The supports of the two cutoffs have one common smooth compact
spacetime plateau inside the literal product cylinder. -/
private theorem exists_common_cutoff_plateau
     (s₀ s₁ : ℝ) (O : PDE.VelocityRegion d) (hO : IsOpen O)
    (η : PDE.ScalarField d) (hηCompact : HasCompactSupport η)
    (hηSub : tsupport η ⊆ O)
    (ζ : ℝ → ℝ) (hζCompact : HasCompactSupport ζ)
    (hζSub : tsupport ζ ⊆ Set.Ioo s₀ s₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ b : HypoellipticAleksandrov.Parabolic.ScalarField d,
      ContDiff ℝ PDE.smoothOrder b ∧ HasCompactSupport b ∧
        tsupport b ⊆ Set.Ioo s₀ s₁ ×ˢ O ∧
        Set.EqOn b 1
          (Metric.cthickening δ (tsupport ζ ×ˢ tsupport η)) := exists_contDiff_one_on_cthickening_tsupport_subset (isOpen_Ioo.prod hO) (hζCompact.isCompact.prod hηCompact.isCompact) (by
      rintro ⟨t, v⟩ ⟨ht, hv⟩
      exact ⟨hζSub ht, hηSub hv⟩)

section
variable {K : HypoellipticAleksandrov.Parabolic.Region d} {δ : ℝ} (hδ : 0 < δ)

include hδ
/-- A plateau on a positive closed thickening is genuinely locally constant
at every point of the underlying carrier, so its first and second selected
derivatives vanish there. -/
private theorem plateau_value_derivatives

    (b : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hbOne : Set.EqOn b 1 (Metric.cthickening δ K))
    {z : TimeVelocity d} (hz : z ∈ K) :
    b z = 1 ∧ timeDerivative b z = 0 ∧
      (∀ i : Fin d, velocityGradient b z i = 0) ∧
      ∀ i : Fin d, velocityHessian b z i i = 0 := by
  have hev : b =ᶠ[𝓝 z] (1 ) := by
    filter_upwards [Metric.ball_mem_nhds z hδ] with y hy
    apply hbOne
    exact Metric.mem_cthickening_of_dist_le y z δ K hz hy.le

  have hdb : fderiv ℝ b z = 0 := by
    rw [hev.fderiv_eq]
    simp
  have hddb : fderiv ℝ (fderiv ℝ b) z = 0 := by

    rw [hev.fderiv.fderiv_eq]
    have hconst : fderiv ℝ (1 : HypoellipticAleksandrov.Parabolic.ScalarField d) = 0 := by
      funext y
      simp
    rw [hconst]
    simp
  refine ⟨hev.self_of_nhds, ?_, ?_, ?_⟩
  · unfold timeDerivative
    rw [hdb]
    rfl
  · intro i
    unfold velocityGradient
    rw [hdb]
    rfl
  · intro i
    unfold velocityHessian
    rw [hddb]
    rfl

/-- On the plateau carrier, all four localized representatives agree exactly
with the originally selected representatives. -/
private theorem localized_jet_eqOn_plateau

    (q QW : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (b : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hbOne : Set.EqOn b 1 (Metric.cthickening δ K)) :
    Set.EqOn (fun z => b z * q z) q K ∧
      Set.EqOn (fun z => b z * QW z + q z * timeDerivative b z) QW K ∧
      (∀ i : Fin d, Set.EqOn
        (fun z => b z * QG z i + q z * velocityGradient b z i)
        (fun z => QG z i) K) ∧
      ∀ i : Fin d, Set.EqOn
        (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
          q z * velocityHessian b z i i)
        (fun z => QH z i i) K := by
  constructor
  · intro z hz
    obtain ⟨hbz, hbt, hbi, hbii⟩ := plateau_value_derivatives hδ b hbOne hz
    simp [hbz]
  constructor
  · intro z hz
    obtain ⟨hbz, hbt, hbi, hbii⟩ := plateau_value_derivatives hδ b hbOne hz
    simp [hbz, hbt]
  constructor
  · intro i z hz
    obtain ⟨hbz, hbt, hbi, hbii⟩ := plateau_value_derivatives hδ b hbOne hz
    simp [hbz, hbi i]
  · intro i z hz
    obtain ⟨hbz, hbt, hbi, hbii⟩ := plateau_value_derivatives hδ b hbOne hz
    simp [hbz, hbi i, hbii i]
end


/-- Multiplication by one smooth cutoff gives the exact selected weak time
derivative and every selected first velocity derivative. -/
private theorem localized_first_jet
     {U : HypoellipticAleksandrov.Parabolic.Region d}
    (q QW : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d)
    (hqLoc : LocallyIntegrableOn q U )
    (hQWLoc : LocallyIntegrableOn QW U )
    (hQGLoc : ∀ i : Fin d,
      LocallyIntegrableOn (fun z => QG z i) U )
    (hqTime : HasWeakTimeDerivOn U q QW)
    (hqVelocity : ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn U i q (fun z => QG z i))
    (b : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hb : ContDiff ℝ PDE.smoothOrder b) :
    HasWeakTimeDerivOn U
        (fun z => b z * q z)
        (fun z => b z * QW z + q z * timeDerivative b z) ∧
      ∀ i : Fin d,
        HasWeakVelocityPartialDerivOn U i
          (fun z => b z * q z)
          (fun z => b z * QG z i + q z * velocityGradient b z i) := by
  constructor
  · exact hqTime.mul_contDiff hb hqLoc hQWLoc
  · intro i
    exact (hqVelocity i).mul_contDiff hb hqLoc (hQGLoc i)

/-- Every field in the localized first jet is supported in the support of the
single common cutoff. -/
private theorem localized_first_jet_tsupport_subset
     (q QW : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d)
    (b : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    tsupport (fun z => b z * q z) ⊆ tsupport b ∧
      tsupport (fun z => b z * QW z + q z * timeDerivative b z) ⊆ tsupport b ∧
      ∀ i : Fin d,
        tsupport (fun z => b z * QG z i + q z * velocityGradient b z i) ⊆
          tsupport b := by
  have close_support_subset (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
      (hf : Function.support f ⊆ tsupport b) : tsupport f ⊆ tsupport b := by

    simpa only [tsupport, closure_closure] using closure_mono hf
  constructor
  · exact close_support_subset _ fun z hz =>
      tsupport_mul_subset_left (subset_closure hz)
  constructor
  · apply close_support_subset
    intro z hz
    by_contra hzb

    have hdb0 : timeDerivative b z = 0 := by
      unfold timeDerivative
      rw [fderiv_of_notMem_tsupport ℝ hzb]
      rfl
    exact hz (by simp [(image_eq_zero_of_notMem_tsupport hzb), hdb0])
  · intro i
    apply close_support_subset
    intro z hz
    by_contra hzb

    have hdb0 : velocityGradient b z i = 0 := by
      unfold velocityGradient
      rw [fderiv_of_notMem_tsupport ℝ hzb]
      rfl
    exact hz (by simp [(image_eq_zero_of_notMem_tsupport hzb), hdb0])

section
variable (b : HypoellipticAleksandrov.Parabolic.ScalarField d) (hb : ContDiff ℝ PDE.smoothOrder b) (i : Fin d)




include hb in
private theorem velocityGradient_cutoff_gradient
      (z : TimeVelocity d) :
    velocityGradient (fun y => velocityGradient b y i) z i =
      velocityHessian b z i i := by
  unfold velocityGradient velocityHessian

  rw [fderiv_clm_apply
    (((contDiff_infty_iff_fderiv.mp hb).2).differentiable (by simp) z) (differentiableAt_const _)]
  rw [fderiv_const_apply]
  simp
end


/-- The localized selected first velocity representative has the exact
diagonal second weak derivative furnished by the same cutoff. -/
private theorem localized_diagonal_second_jet
     {U : HypoellipticAleksandrov.Parabolic.Region d}
    (q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (i : Fin d)
    (hqLoc : LocallyIntegrableOn q U )
    (hQGiLoc : LocallyIntegrableOn (fun z => QG z i) U )
    (hQHiiLoc : LocallyIntegrableOn (fun z => QH z i i) U )
    (hqVelocity : HasWeakVelocityPartialDerivOn U i q (fun z => QG z i))
    (hQGVelocity : HasWeakVelocityPartialDerivOn U i
      (fun z => QG z i) (fun z => QH z i i))
    (b : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hb : ContDiff ℝ PDE.smoothOrder b)
    (hfirstLoc : LocallyIntegrableOn (fun z => b z * QG z i) U )
    (hfirstDerivLoc : LocallyIntegrableOn
      (fun z => b z * QH z i i + QG z i * velocityGradient b z i) U )
    (hsecondLoc : LocallyIntegrableOn
      (fun z => velocityGradient b z i * q z) U )
    (hsecondDerivLoc : LocallyIntegrableOn
      (fun z => velocityGradient b z i * QG z i +
        q z * velocityGradient (fun y => velocityGradient b y i) z i) U ) :
    HasWeakVelocityPartialDerivOn U i
      (fun z => b z * QG z i + q z * velocityGradient b z i)
      (fun z => b z * QH z i i +
        2 * velocityGradient b z i * QG z i +
          q z * velocityHessian b z i i) := by




  convert ((hQGVelocity.mul_contDiff hb hQGiLoc hQHiiLoc).add (hqVelocity.mul_contDiff (_root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.velocityGradient_component_contDiff b hb i) hqLoc hQGiLoc) hfirstLoc hfirstDerivLoc hsecondLoc hsecondDerivLoc) using 1 <;> funext z
  · ring
  · rw [velocityGradient_cutoff_gradient b hb i z]
    ring

/-- The exact localized diagonal representative remains supported in the
support of the common cutoff. -/
private theorem localized_diagonal_second_tsupport_subset
     (q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (b : HypoellipticAleksandrov.Parabolic.ScalarField d) (i : Fin d) :
    tsupport (fun z => b z * QH z i i +
      2 * velocityGradient b z i * QG z i +
        q z * velocityHessian b z i i) ⊆ tsupport b := by


  simpa only [tsupport, closure_closure] using closure_mono (show Function.support (fun z => b z * QH z i i +
      2 * velocityGradient b z i * QG z i +
        q z * velocityHessian b z i i) ⊆ tsupport b by
      intro z hz
      by_contra hzb

      have hdb0 : velocityGradient b z i = 0 := by
        unfold velocityGradient
        rw [fderiv_of_notMem_tsupport ℝ hzb]
        rfl
      have hddb0 : velocityHessian b z i i = 0 := by
        unfold velocityHessian

        have hsecond : fderiv ℝ (fderiv ℝ b) z = 0 := by
          rw [fderiv_of_notMem_tsupport ℝ]
          exact fun hmem => hzb (tsupport_fderiv_subset ℝ hmem)
        rw [hsecond]
        rfl
      exact hz (by simp [(image_eq_zero_of_notMem_tsupport hzb), hdb0, hddb0]))

variable (b : HypoellipticAleksandrov.Parabolic.ScalarField d)

private theorem timeDerivative_cutoff_continuous

    (hb : ContDiff ℝ PDE.smoothOrder b) : Continuous (timeDerivative b) := by
  unfold timeDerivative
  simpa using (hb.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem timeDerivative_cutoff_compact
      (hb : HasCompactSupport b) :
    HasCompactSupport (timeDerivative b) := (id (HasCompactSupport.fderiv_apply ℝ hb (1, 0)))

private theorem velocityGradient_cutoff_compact
      (hb : HasCompactSupport b) (i : Fin d) :
    HasCompactSupport (fun z => velocityGradient b z i) := (id (HasCompactSupport.fderiv_apply ℝ hb (0, Pi.single i 1)))

private theorem velocityHessian_cutoff_continuous

    (hb : ContDiff ℝ PDE.smoothOrder b) (i : Fin d) :
    Continuous (fun z => velocityHessian b z i i) := by
  unfold velocityHessian

  simpa using (((contDiff_infty_iff_fderiv.mp hb).2).continuous_fderiv (by simp)).clm_apply continuous_const |>.clm_apply
    continuous_const

private theorem velocityHessian_cutoff_compact
      (hb : HasCompactSupport b) (i : Fin d) :
    HasCompactSupport (fun z => velocityHessian b z i i) := (_semanticProof_02a680b7b556 hb)

variable {U : HypoellipticAleksandrov.Parabolic.Region d}

/-- The four representatives obtained from one smooth compact localization
inherit the `L²` exponent from the selected weak jet. -/
private theorem localized_jet_memLp

    (q QW : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hq : ParabolicMemLpOn U (2 ) q)
    (hQW : ParabolicMemLpOn U (2 ) QW)
    (hQG : ∀ i : Fin d,
      ParabolicMemLpOn U (2 ) (fun z => QG z i))
    (hQH : ∀ i : Fin d,
      ParabolicMemLpOn U (2 ) (fun z => QH z i i))
    (b : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hb : ContDiff ℝ PDE.smoothOrder b)
    (hbCompact : HasCompactSupport b) :
    ParabolicMemLpOn U (2 ) (fun z => b z * q z) ∧
      ParabolicMemLpOn U (2 )
        (fun z => b z * QW z + q z * timeDerivative b z) ∧
      (∀ i : Fin d, ParabolicMemLpOn U (2 )
        (fun z => b z * QG z i + q z * velocityGradient b z i)) ∧
      ∀ i : Fin d, ParabolicMemLpOn U (2 )
        (fun z => b z * QH z i i +
          2 * velocityGradient b z i * QG z i +
            q z * velocityHessian b z i i) := by
  have hbTop : ParabolicMemLpOn U ∞ b :=
    (hb.continuous.memLp_of_hasCompactSupport hbCompact).restrict U
  have hbtTop : ParabolicMemLpOn U ∞ (timeDerivative b) :=
    ((timeDerivative_cutoff_continuous b hb).memLp_of_hasCompactSupport
      (timeDerivative_cutoff_compact b hbCompact)).restrict U
  have hbiTop (i : Fin d) : ParabolicMemLpOn U ∞
      (fun z => velocityGradient b z i) :=
    ((_root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.velocityGradient_component_contDiff b hb i).continuous.memLp_of_hasCompactSupport
      (velocityGradient_cutoff_compact b hbCompact i)).restrict U
  have hbiiTop (i : Fin d) : ParabolicMemLpOn U ∞
      (fun z => velocityHessian b z i i) :=
    ((velocityHessian_cutoff_continuous b hb i).memLp_of_hasCompactSupport
      (velocityHessian_cutoff_compact b hbCompact i)).restrict U


  have hri (i : Fin d) : ParabolicMemLpOn U (2 )
      (fun z => b z * QG z i + q z * velocityGradient b z i) := by
    have h1 : ParabolicMemLpOn U (2 ) (fun z => b z * QG z i) := by
      simpa only [mul_comm] using (hQG i).mul' hbTop

    exact h1.add (by
        simpa only using hq.mul' (hbiTop i))
  have hrii (i : Fin d) : ParabolicMemLpOn U (2 )
      (fun z => b z * QH z i i +
        2 * velocityGradient b z i * QG z i +
          q z * velocityHessian b z i i) := by
    have h1 : ParabolicMemLpOn U (2 ) (fun z => b z * QH z i i) := by
      simpa only [mul_comm] using (hQH i).mul' hbTop



    convert (h1.add ((show ParabolicMemLpOn U (2 )
        (fun z => velocityGradient b z i * QG z i) by
        simpa only [mul_comm] using (hQG i).mul' (hbiTop i)).const_smul (2 : ℝ))).add ((MemLp.mul' hq (hbiiTop i))) using 1
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨(by
      simpa only [mul_comm] using hq.mul' hbTop), (((MemLp.add (Eq.mpr (id (congrArg (ParabolicMemLpOn U 2) (funext fun z => mul_comm (b z) (QW z)))) (MemLp.mul' hQW hbTop))
      (MemLp.mul' hq hbtTop)))), hri, hrii⟩

section
variable (hU : IsOpen U) (q QW : HypoellipticAleksandrov.Parabolic.ScalarField d) (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d) (hq : ParabolicMemLpOn U (2 ) q) (hQW : ParabolicMemLpOn U (2 ) QW) (hQG : ∀ i : Fin d, ParabolicMemLpOn U (2 ) (fun z => QG z i)) (hQH : ∀ i : Fin d, ParabolicMemLpOn U (2 ) (fun z => QH z i i)) (hqTime : HasWeakTimeDerivOn U q QW) (hqVelocity : ∀ i : Fin d, HasWeakVelocityPartialDerivOn U i q (fun z => QG z i)) (hQGVelocity : ∀ i : Fin d, HasWeakVelocityPartialDerivOn U i (fun z => QG z i) (fun z => QH z i i)) (b : HypoellipticAleksandrov.Parabolic.ScalarField d) (hb : ContDiff ℝ PDE.smoothOrder b) (hbCompact : HasCompactSupport b) (hbSub : tsupport b ⊆ U)

include hU hq hQW hQG hQH hqTime hqVelocity hQGVelocity hb hbCompact hbSub
/-- One compact localization of the selected diagonal jet globalizes both its
raw weak relations and its `L²` representatives. -/
private theorem localized_jet_univ
       :
    HasWeakTimeDerivOn Set.univ
        (fun z => b z * q z)
        (fun z => b z * QW z + q z * timeDerivative b z) ∧
      (∀ i : Fin d, HasWeakVelocityPartialDerivOn Set.univ i
        (fun z => b z * q z)
        (fun z => b z * QG z i + q z * velocityGradient b z i)) ∧
      (∀ i : Fin d, HasWeakVelocityPartialDerivOn Set.univ i
        (fun z => b z * QG z i + q z * velocityGradient b z i)
        (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
          q z * velocityHessian b z i i)) ∧
      MemLp (fun z => b z * q z) (2 )  ∧
      MemLp (fun z => b z * QW z + q z * timeDerivative b z)
        (2 )  ∧
      (∀ i : Fin d, MemLp
        (fun z => b z * QG z i + q z * velocityGradient b z i)
        (2 ) ) ∧
      ∀ i : Fin d, MemLp
        (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
          q z * velocityHessian b z i i) (2 ) volume := by

  rcases (localized_jet_memLp q QW QG QH hq hQW hQG hQH b hb hbCompact) with ⟨hr, hrt, hri, hrii⟩
  have hfirst := localized_first_jet q QW QG
    (hq.locallyIntegrableOn (by norm_num))
    (hQW.locallyIntegrableOn (by norm_num))
    (fun i => (hQG i).locallyIntegrableOn (by norm_num))
    hqTime hqVelocity b hb
  rcases hfirst with ⟨hrTime, hrVelocity⟩

  rcases (localized_first_jet_tsupport_subset q QW QG b) with ⟨hrSupp, hrtSupp, hriSupp⟩
  have hbTop : ParabolicMemLpOn U ∞ b :=
    (hb.continuous.memLp_of_hasCompactSupport hbCompact).restrict U
  have hbiTop (i : Fin d) : ParabolicMemLpOn U ∞
      (fun z => velocityGradient b z i) :=
    ((_root_.HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy.velocityGradient_component_contDiff b hb i).continuous.memLp_of_hasCompactSupport
      (velocityGradient_cutoff_compact b hbCompact i)).restrict U
  have hbiiTop (i : Fin d) : ParabolicMemLpOn U ∞
      (fun z => velocityHessian b z i i) :=
    ((velocityHessian_cutoff_continuous b hb i).memLp_of_hasCompactSupport
      (velocityHessian_cutoff_compact b hbCompact i)).restrict U
  have hdiag (i : Fin d) : HasWeakVelocityPartialDerivOn U i
      (fun z => b z * QG z i + q z * velocityGradient b z i)
      (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
        q z * velocityHessian b z i i) := by




    exact localized_diagonal_second_jet q QG QH i
      (hq.locallyIntegrableOn (by norm_num))
      ((hQG i).locallyIntegrableOn (by norm_num))
      ((hQH i).locallyIntegrableOn (by norm_num))
      (hqVelocity i) (hQGVelocity i) b hb
      ((show ParabolicMemLpOn U (2 )
        (fun z => b z * QG z i) by
          simpa only [mul_comm] using (hQG i).mul' hbTop).locallyIntegrableOn (by norm_num))
      ((show ParabolicMemLpOn U (2 )
        (fun z => b z * QH z i i + QG z i * velocityGradient b z i) by


          exact (show ParabolicMemLpOn U (2 ) (fun z => b z * QH z i i) by
              simpa only [mul_comm] using (hQH i).mul' hbTop).add (by
              simpa only using (hQG i).mul' (hbiTop i))).locallyIntegrableOn (by norm_num))
      ((show ParabolicMemLpOn U (2 )
        (fun z => velocityGradient b z i * q z) by
          simpa only [mul_comm] using hq.mul' (hbiTop i)).locallyIntegrableOn (by norm_num))
      ((show ParabolicMemLpOn U (2 )
        (fun z => velocityGradient b z i * QG z i +
          q z * velocityGradient (fun y => velocityGradient b y i) z i) by


          exact (show ParabolicMemLpOn U (2 )
              (fun z => velocityGradient b z i * QG z i) by
              simpa only [mul_comm] using (hQG i).mul' (hbiTop i)).add (by
              have hraw : ParabolicMemLpOn U (2 )
                  (fun z => q z * velocityHessian b z i i) := by
                simpa only using hq.mul' (hbiiTop i)
              simpa only [velocityGradient_cutoff_gradient b hb i] using hraw)).locallyIntegrableOn (by norm_num))
  have hdiagSupp (i : Fin d) := localized_diagonal_second_tsupport_subset q QG QH b i
  have hrTimeUniv := hrTime.univ_of_tsupport_subset hU
    (hrSupp.trans hbSub) (hrtSupp.trans hbSub)
  have hrVelocityUniv (i : Fin d) := (hrVelocity i).univ_of_tsupport_subset hU
    (hrSupp.trans hbSub) ((hriSupp i).trans hbSub)
  have hdiagUniv (i : Fin d) := (hdiag i).univ_of_tsupport_subset hU
    ((hriSupp i).trans hbSub) ((hdiagSupp i).trans hbSub)
  have globalize {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
      (hf : ParabolicMemLpOn U (2 ) f)
      (hs : tsupport f ⊆ U)  :=
    hf.memLp_of_support_subset hU.measurableSet
      (subset_tsupport f |>.trans hs)
  exact ⟨hrTimeUniv, hrVelocityUniv, hdiagUniv,
    globalize hr (hrSupp.trans hbSub),
    globalize hrt (hrtSupp.trans hbSub),
    fun i => globalize (hri i) ((hriSupp i).trans hbSub),
    fun i => globalize (hrii i) ((hdiagSupp i).trans hbSub)⟩

/-- The single mollification of the localized scalar realizes all selected
time, first velocity, and diagonal second derivatives and converges strongly
to their localized representatives. -/
private theorem common_mollifier_of_localized_jet

    (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ PDE.smoothOrder
        (SpacetimeMollifier.spacetimeMollification ε (fun z => b z * q z)) ∧
      timeDerivative
          (SpacetimeMollifier.spacetimeMollification ε (fun z => b z * q z)) =
        SpacetimeMollifier.spacetimeMollification ε
          (fun z => b z * QW z + q z * timeDerivative b z) ∧
      (∀ i : Fin d,
        (fun z => velocityGradient
          (SpacetimeMollifier.spacetimeMollification ε (fun z => b z * q z)) z i) =
          SpacetimeMollifier.spacetimeMollification ε
            (fun z => b z * QG z i + q z * velocityGradient b z i)) ∧
      (∀ i : Fin d,
        (fun z => velocityHessian
          (SpacetimeMollifier.spacetimeMollification ε (fun z => b z * q z)) z i i) =
          SpacetimeMollifier.spacetimeMollification ε
            (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
              q z * velocityHessian b z i i)) ∧
      Filter.Tendsto (fun a  => eLpNorm
          (SpacetimeMollifier.spacetimeMollification a (fun z => b z * q z) -
            fun z => b z * q z) (2 ) )
        (𝓝[>] 0) (𝓝 0) ∧
      Filter.Tendsto (fun a  => eLpNorm
          (SpacetimeMollifier.spacetimeMollification a
              (fun z => b z * QW z + q z * timeDerivative b z) -
            fun z => b z * QW z + q z * timeDerivative b z)
          (2 ) ) (𝓝[>] 0) (𝓝 0) ∧
      (∀ i : Fin d, Filter.Tendsto (fun a  => eLpNorm
          (SpacetimeMollifier.spacetimeMollification a
              (fun z => b z * QG z i + q z * velocityGradient b z i) -
            fun z => b z * QG z i + q z * velocityGradient b z i)
          (2 ) ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ i : Fin d, Filter.Tendsto (fun a  => eLpNorm
          (SpacetimeMollifier.spacetimeMollification a
              (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
                q z * velocityHessian b z i i) -
            fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
              q z * velocityHessian b z i i)
          (2 ) ) (𝓝[>] 0) (𝓝 0) := by
  let sharedTerm_72d33ecb14 := ((fun z => b z * q z))
  rcases localized_jet_univ hU q QW QG QH hq hQW hQG hQH
      hqTime hqVelocity hQGVelocity b hb hbCompact hbSub with
    ⟨hrTime, hrVelocity, hriiVelocity, hrMem, hrtMem, hriMem, hriiMem⟩
  have hrLoc := hrMem.locallyIntegrable (by norm_num)

  have hriLoc (i : Fin d) := (hriMem i).locallyIntegrable (by norm_num)
  have hriiLoc (i : Fin d) := (hriiMem i).locallyIntegrable (by norm_num)
  have hsmooth := SpacetimeMollifier.contDiff_spacetimeMollification hε
    sharedTerm_72d33ecb14 hrLoc
  have htime := SpacetimeMollifier.timeDerivative_spacetimeMollification hε
    sharedTerm_72d33ecb14
    (fun z => b z * QW z + q z * timeDerivative b z) hrLoc (hrtMem.locallyIntegrable (by norm_num)) hrTime
  have hgrad (i : Fin d) := SpacetimeMollifier.velocityGradient_spacetimeMollification hε i
    sharedTerm_72d33ecb14
    (fun z => b z * QG z i + q z * velocityGradient b z i)
    hrLoc (hriLoc i) (hrVelocity i)
  have hhess (i : Fin d) :
      (fun z => velocityHessian
        (SpacetimeMollifier.spacetimeMollification ε sharedTerm_72d33ecb14) z i i) =
        SpacetimeMollifier.spacetimeMollification ε
          (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
            q z * velocityHessian b z i i) := by
    have hsecond := SpacetimeMollifier.velocityGradient_spacetimeMollification hε i
      (fun z => b z * QG z i + q z * velocityGradient b z i)
      (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
        q z * velocityHessian b z i i)
      (hriLoc i) (hriiLoc i) (hriiVelocity i)
    rw [← hgrad i] at hsecond
    funext z
    rw [← hsecond]
    exact (velocityGradient_cutoff_gradient _ hsmooth i z).symm
  exact ⟨hsmooth, htime, hgrad, hhess,
    SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub _ hrMem,
    SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub _ hrtMem,
    fun i => SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub _ (hriMem i),
    fun i => SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub _ (hriiMem i)⟩
end


/-- Compactly supported weak gradient time-energy identity on a literal
product cylinder. -/
theorem weakGradient_timeEnergy
     (s₀ s₁ : ℝ)
    (O : PDE.VelocityRegion d) (hO : IsOpen O)
    (q QW : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hq_memLp :
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 ) q)
    (hQW_memLp :
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 ) QW)
    (hQG_memLp : ∀ i : Fin d,
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 )
        (fun z => QG z i))
    (hQHdiag_memLp : ∀ i : Fin d,
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 )
        (fun z => QH z i i))
    (hq_time :
      HasWeakTimeDerivOn (Set.Ioo s₀ s₁ ×ˢ O) q QW)
    (hq_velocity : ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn
        (Set.Ioo s₀ s₁ ×ˢ O) i q (fun z => QG z i))
    (hQG_velocity : ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn
        (Set.Ioo s₀ s₁ ×ˢ O) i
        (fun z => QG z i) (fun z => QH z i i))
    (η : PDE.ScalarField d)
    (hη : ContDiff ℝ PDE.smoothOrder η)
    (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O)
    (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (hζcompact : HasCompactSupport ζ)
    (hζsupport : tsupport ζ ⊆ Set.Ioo s₀ s₁) :
    IntegrableOn
        (fun z =>
          ζ z.1 * QW z *
            localizedGradientDivergence η QG QH z)
        (Set.Ioo s₀ s₁ ×ˢ O)  ∧
      IntegrableOn
        (fun z =>
          _root_.deriv ζ z.1 * η z.2 ^ 2 *
            ∑ i : Fin d, QG z i ^ 2)
        (Set.Ioo s₀ s₁ ×ˢ O) volume ∧
      2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
          ζ z.1 * QW z *
            localizedGradientDivergence η QG QH z) =
        -(∫ z in Set.Ioo s₀ s₁ ×ˢ O,
          _root_.deriv ζ z.1 * η z.2 ^ 2 *
            ∑ i : Fin d, QG z i ^ 2) := by
  let U : HypoellipticAleksandrov.Parabolic.Region d := Set.Ioo s₀ s₁ ×ˢ O

  have hU : IsOpen U := isOpen_Ioo.prod hO
  obtain ⟨δ, hδ, b, hb, hbCompact, hbSub, hbOne⟩ :=
    exists_common_cutoff_plateau s₀ s₁ O hO η hηcompact hηsupport
      ζ hζcompact hζsupport
  let rt  := fun z => b z * QW z + q z * timeDerivative b z
  let ri  := fun i z =>
    b z * QG z i + q z * velocityGradient b z i
  let rii  := fun i z =>
    b z * QH z i i + 2 * velocityGradient b z i * QG z i +
      q z * velocityHessian b z i i
  rcases localized_jet_univ hU q QW QG QH hq_memLp hQW_memLp hQG_memLp
      hQHdiag_memLp hq_time hq_velocity hQG_velocity b hb hbCompact hbSub with
    ⟨hrTime, hrVelocity, hriiVelocity, hrMem, hrtMem, hriMem, hriiMem⟩
  have hlimits := localized_energy_integral_limits U η hη hηcompact ζ hζ hζcompact
    rt ri rii hrtMem hriMem hriiMem

  have hleftT := hlimits.1.const_mul 2
  have hrightT := hlimits.2.neg


  have hplateau := localized_jet_eqOn_plateau hδ q QW QG QH b hbOne
  rcases hplateau with ⟨hrEq, hrtEq, hriEq, hriiEq⟩
  have hid := weak_energy_integrands_eq_of_eqOn_cutoff_support QW rt QG QH ri rii η ζ
    (hrtEq)
    (fun i => by exact hriEq i)
    (fun i => by exact hriiEq i)
  have htargetInt := weak_energy_targets_integrableOn U QW QG QH hQW_memLp
    hQG_memLp hQHdiag_memLp η hη hηcompact ζ hζ hζcompact
  refine ⟨htargetInt.1, htargetInt.2, ?_⟩
  rw [show (∫ z in U, ζ z.1 * QW z * localizedGradientDivergence η QG QH z) = ∫ z in U, ζ z.1 * rt z * localizedGradientDivergence η
        (fun z i => ri i z) (fun z i _j => rii i z) z by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => (hid.1 z).symm]
  rw [show (∫ z in U, _root_.deriv ζ z.1 * η z.2 ^ 2 *
      ∑ i : Fin d, QG z i ^ 2) =
      ∫ z in U, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ i : Fin d, ri i z ^ 2 by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => (hid.2 z).symm]
  exact (tendsto_nhds_unique (hleftT.congr' (show _ by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rcases common_mollifier_of_localized_jet hU q QW QG QH hq_memLp hQW_memLp
          hQG_memLp hQHdiag_memLp hq_time hq_velocity hQG_velocity
          b hb hbCompact hbSub ε hε with
        ⟨hrSmooth, hrtEq, hriEq, hriiEq, _⟩
      have hs := smoothGradient_timeEnergy s₀ s₁ O hO
        (SpacetimeMollifier.spacetimeMollification ε (fun z => b z * q z)) hrSmooth
        η hη hηcompact hηsupport ζ hζ hζcompact hζsupport
      dsimp [U, rt, ri, rii] at hrtEq hriEq hriiEq ⊢
      rw [hrtEq] at hs
      convert hs using 1 <;> congr 1 <;> apply integral_congr_ae
      · exact Filter.Eventually.of_forall fun z => by
          dsimp only
          apply congrArg (fun x : ℝ =>
            ζ z.1 * SpacetimeMollifier.spacetimeMollification ε
              (fun z => b z * QW z + q z * timeDerivative b z) z * x)
          unfold localizedGradientDivergence
          apply congrArg Neg.neg
          apply Finset.sum_congr rfl
          intro i hi
          dsimp only
          rw [← congrFun (hriEq i) z, ← congrFun (hriiEq i) z]
      · exact Filter.Eventually.of_forall fun z => by
          dsimp only
          apply congrArg (fun x : ℝ => _root_.deriv ζ z.1 * η z.2 ^ 2 * x)
          apply Finset.sum_congr rfl
          intro i hi
          rw [← congrFun (hriEq i) z])) hrightT)

end HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy
