module

public import HypoellipticAleksandrov.Parabolic.WeightedTimeVelocityL2
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import HypoellipticAleksandrov.Parabolic.WeakJetLocalization

/-!
# Weak gradient time-energy identity

This file begins the compatible localization of the selected weak spacetime
jet used in the weak gradient time-energy identity.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy

/-- The three literal coordinate products used by the weak energy identity
converge for the common positive-radius spacetime mollifier. -/
private theorem coordinate_energy_product_limits
    {d : ℕ} (S : Set (TimeVelocity d))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ)
    (rt : TimeVelocity d → ℝ)
    (ri rii : Fin d → TimeVelocity d → ℝ)
    (hrt : MemLp rt (2 : ℝ≥0∞) volume)
    (hri : ∀ i, MemLp (ri i) (2 : ℝ≥0∞) volume)
    (hrii : ∀ i, MemLp (rii i) (2 : ℝ≥0∞) volume)
    (i : Fin d) :
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) *
          SpacetimeMollifier.spacetimeMollification ε rt z *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) *
          rt z * ri i z ∂volume)) ∧
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
          SpacetimeMollifier.spacetimeMollification ε rt z *
          SpacetimeMollifier.spacetimeMollification ε (rii i) z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * rt z * rii i z ∂volume)) ∧
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        (_root_.deriv ζ z.1 * η z.2 ^ 2) *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z * ri i z ∂volume)) := by
  obtain ⟨hc₁, hc₂, -, hc₃⟩ := energy_weights_memLp_top S η hη hηCompact ζ hζ hζCompact
  have ht := (SpacetimeMollifierL2.spacetimeMollification_strongL2 hrt).restrict S
  have hi := (SpacetimeMollifierL2.spacetimeMollification_strongL2 (hri i)).restrict S
  have hii := (SpacetimeMollifierL2.spacetimeMollification_strongL2 (hrii i)).restrict S
  exact ⟨(ht.weight (hc₁ i)).pairing hi, (ht.weight hc₂).pairing hii, (hi.weight hc₃).pairing hi⟩

section
variable {d : ℕ} (S : Set (TimeVelocity d)) (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
  (hηCompact : HasCompactSupport η) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
  (hζCompact : HasCompactSupport ζ) (rt : TimeVelocity d → ℝ) (ri rii : Fin d → TimeVelocity d → ℝ)
include hη hηCompact hζ hζCompact

/-- The three coordinate limits assemble into the exact finite sums used on
the two sides of the localized weak energy identity. -/
private theorem summed_energy_product_limits
    (hrt : MemLp rt (2 : ℝ≥0∞) volume)
    (hri : ∀ i, MemLp (ri i) (2 : ℝ≥0∞) volume)
    (hrii : ∀ i, MemLp (rii i) (2 : ℝ≥0∞) volume) :
    Filter.Tendsto (fun ε : ℝ => ∑ i : Fin d,
        ((∫ z in S, ((-2 : ℝ) * ζ z.1 *
            (η z.2 * spatialPartial i η z.2)) *
            SpacetimeMollifier.spacetimeMollification ε rt z *
            SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume) +
          ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
            SpacetimeMollifier.spacetimeMollification ε rt z *
            SpacetimeMollifier.spacetimeMollification ε (rii i) z ∂volume))
      (𝓝[>] 0) (𝓝 (∑ i : Fin d,
        ((∫ z in S, ((-2 : ℝ) * ζ z.1 *
            (η z.2 * spatialPartial i η z.2)) * rt z * ri i z ∂volume) +
          ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
            rt z * rii i z ∂volume))) ∧
    Filter.Tendsto (fun ε : ℝ => ∑ i : Fin d,
        ∫ z in S, (_root_.deriv ζ z.1 * η z.2 ^ 2) *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume)
      (𝓝[>] 0) (𝓝 (∑ i : Fin d,
        ∫ z in S, (_root_.deriv ζ z.1 * η z.2 ^ 2) *
          ri i z * ri i z ∂volume)) := by
  have hcoord (i : Fin d) := coordinate_energy_product_limits S η hη hηCompact
    ζ hζ hζCompact rt ri rii hrt hri hrii i
  constructor
  · apply tendsto_finsetSum Finset.univ
    intro i _
    exact (hcoord i).1.add (hcoord i).2.1
  · apply tendsto_finsetSum Finset.univ
    intro i _
    exact (hcoord i).2.2

/-- The coordinate-product presentation is exactly the literal localized
divergence and gradient-square presentation; every integral rewrite is backed
by explicit `L² × L²` integrability. -/
private theorem energy_coordinate_integral_algebra
    (hrt : MemLp rt (2 : ℝ≥0∞) ((volume : Measure (TimeVelocity d)).restrict S))
    (hri : ∀ i, MemLp (ri i) (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S))
    (hrii : ∀ i, MemLp (rii i) (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S)) :
    (∑ i : Fin d,
        ((∫ z in S, ((-2 : ℝ) * ζ z.1 *
            (η z.2 * spatialPartial i η z.2)) * rt z * ri i z ∂volume) +
          ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
            rt z * rii i z ∂volume)) =
      ∫ z in S, ζ z.1 * rt z *
        localizedGradientDivergence η
          (fun z i => ri i z) (fun z i _ => rii i z) z ∂volume ∧
    (∑ i : Fin d, ∫ z in S,
        (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z * ri i z ∂volume) =
      ∫ z in S, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ i : Fin d, ri i z ^ 2 ∂volume := by
  let μ := (volume : Measure (TimeVelocity d)).restrict S
  obtain ⟨hc₁, hc₂, -, hc₃⟩ := energy_weights_memLp_top S η hη hηCompact ζ hζ hζCompact
  let A : Fin d → TimeVelocity d → ℝ := fun i z =>
    ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) * rt z * ri i z
  let B : Fin d → TimeVelocity d → ℝ := fun i z =>
    ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * rt z * rii i z
  let C : Fin d → TimeVelocity d → ℝ := fun i z =>
    (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z * ri i z
  have hA (i : Fin d) : Integrable (A i) μ := by
    have hw : MemLp (fun z =>
        ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) * rt z)
        (2 : ℝ≥0∞) μ := by
      simpa only [mul_comm] using hrt.mul' (hc₁ i)
    simpa only [A, Pi.mul_def] using hw.integrable_mul (hri i)
  have hB (i : Fin d) : Integrable (B i) μ := by
    have hw : MemLp (fun z => ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * rt z)
        (2 : ℝ≥0∞) μ := by
      simpa only [mul_comm] using hrt.mul' hc₂
    simpa only [B, Pi.mul_def] using hw.integrable_mul (hrii i)
  have hC (i : Fin d) : Integrable (C i) μ := by
    have hw : MemLp (fun z => (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z)
        (2 : ℝ≥0∞) μ := by
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

end

section
variable {d : ℕ}

section
variable (S : Set (TimeVelocity d))

/-- The exact localized divergence and gradient-square integrals converge for
the one common mollification of all localized representatives. -/
private theorem localized_energy_integral_limits
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ)
    (rt : TimeVelocity d → ℝ)
    (ri rii : Fin d → TimeVelocity d → ℝ)
    (hrt : MemLp rt (2 : ℝ≥0∞) volume)
    (hri : ∀ i, MemLp (ri i) (2 : ℝ≥0∞) volume)
    (hrii : ∀ i, MemLp (rii i) (2 : ℝ≥0∞) volume) :
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        ζ z.1 * SpacetimeMollifier.spacetimeMollification ε rt z *
          localizedGradientDivergence η
            (fun z i => SpacetimeMollifier.spacetimeMollification ε (ri i) z)
            (fun z i _j => SpacetimeMollifier.spacetimeMollification ε (rii i) z) z
        ∂volume) (𝓝[>] 0) (𝓝 (∫ z in S,
          ζ z.1 * rt z * localizedGradientDivergence η
            (fun z i => ri i z) (fun z i _j => rii i z) z ∂volume)) ∧
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d,
            SpacetimeMollifier.spacetimeMollification ε (ri i) z ^ 2 ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        _root_.deriv ζ z.1 * η z.2 ^ 2 * ∑ i : Fin d, ri i z ^ 2 ∂volume)) := by
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
              SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume) +
            ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
              SpacetimeMollifier.spacetimeMollification ε rt z *
              SpacetimeMollifier.spacetimeMollification ε (rii i) z ∂volume)) =
        ∫ z in S, ζ z.1 * SpacetimeMollifier.spacetimeMollification ε rt z *
          localizedGradientDivergence η
            (fun z i => SpacetimeMollifier.spacetimeMollification ε (ri i) z)
            (fun z i _j => SpacetimeMollifier.spacetimeMollification ε (rii i) z) z ∂volume) ∧
      (∑ i : Fin d, ∫ z in S,
          (_root_.deriv ζ z.1 * η z.2 ^ 2) *
            SpacetimeMollifier.spacetimeMollification ε (ri i) z *
            SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume) =
        ∫ z in S, _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d,
            SpacetimeMollifier.spacetimeMollification ε (ri i) z ^ 2 ∂volume := by
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

/-- The two literal weak-energy target integrands are integrable directly
from the componentwise `L²` assumptions and bounded compact cutoffs. -/
private theorem weak_energy_targets_integrableOn
    (QW : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hQW : ParabolicMemLpOn S (2 : ℝ≥0∞) QW)
    (hQG : ∀ i : Fin d,
      ParabolicMemLpOn S (2 : ℝ≥0∞) (fun z => QG z i))
    (hQH : ∀ i : Fin d,
      ParabolicMemLpOn S (2 : ℝ≥0∞) (fun z => QH z i i))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ) :
    IntegrableOn (fun z => ζ z.1 * QW z *
      localizedGradientDivergence η QG QH z) S volume ∧
    IntegrableOn (fun z => _root_.deriv ζ z.1 * η z.2 ^ 2 *
      ∑ i : Fin d, QG z i ^ 2) S volume := by
  have hdiv := localizedGradientDivergence_memLp S QG QH hQG hQH
    η hη hηCompact ζ hζ hζCompact
  obtain ⟨-, -, -, hc⟩ := energy_weights_memLp_top S η hη hηCompact ζ hζ hζCompact
  exact ⟨(hQW.integrable_mul hdiv).congr (ae_of_all _ fun _ => by simp [Pi.mul_apply]; ring),
    Analysis.integrable_weighted_sum_sq hc hQG⟩

end

/-- Plateau agreement on the product of cutoff supports identifies both
localized weighted integrands with the selected raw representatives globally. -/
private theorem weak_energy_integrands_eq_of_eqOn_cutoff_support (QW rt : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (ri rii : Fin d → TimeVelocity d → ℝ)
    (η : PDE.Vec d → ℝ) (ζ : ℝ → ℝ)
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
      · have hzero : η z.2 = 0 := image_eq_zero_of_notMem_tsupport hv
        simp [localizedGradientDivergence, hzero]
    · have hzero : ζ z.1 = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [hzero]
  · intro z
    by_cases ht : z.1 ∈ tsupport ζ
    · by_cases hv : z.2 ∈ tsupport η
      · apply congrArg (fun x : ℝ => _root_.deriv ζ z.1 * η z.2 ^ 2 * x)
        apply Finset.sum_congr rfl
        intro i hi
        rw [hri i ⟨ht, hv⟩]
      · have hzero : η z.2 = 0 := image_eq_zero_of_notMem_tsupport hv
        simp [hzero]
    · have hzero : _root_.deriv ζ z.1 = 0 := by
        rw [← fderiv_apply_one_eq_deriv, fderiv_of_notMem_tsupport ℝ ht]
        rfl
      simp [hzero]

/-- Compactly supported weak gradient time-energy identity on a literal
product cylinder. -/
theorem weakGradient_timeEnergy (s₀ s₁ : ℝ)
    (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (q QW : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hq_memLp :
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞) q)
    (hQW_memLp :
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞) QW)
    (hQG_memLp : ∀ i : Fin d,
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞)
        (fun z => QG z i))
    (hQHdiag_memLp : ∀ i : Fin d,
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞)
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
    (η : PDE.Vec d → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O)
    (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcompact : HasCompactSupport ζ)
    (hζsupport : tsupport ζ ⊆ Set.Ioo s₀ s₁) :
    IntegrableOn
        (fun z =>
          ζ z.1 * QW z *
            localizedGradientDivergence η QG QH z)
        (Set.Ioo s₀ s₁ ×ˢ O) volume ∧
      IntegrableOn
        (fun z =>
          _root_.deriv ζ z.1 * η z.2 ^ 2 *
            ∑ i : Fin d, QG z i ^ 2)
        (Set.Ioo s₀ s₁ ×ˢ O) volume ∧
      2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
          ζ z.1 * QW z *
            localizedGradientDivergence η QG QH z
          ∂volume) =
        -(∫ z in Set.Ioo s₀ s₁ ×ˢ O,
          _root_.deriv ζ z.1 * η z.2 ^ 2 *
            ∑ i : Fin d, QG z i ^ 2
          ∂volume) := by
  let U : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  let K : Set (TimeVelocity d) := tsupport ζ ×ˢ tsupport η
  have hU : IsOpen U := isOpen_Ioo.prod hO
  obtain ⟨δ, hδ, b, hb, hbCompact, hbSub, hbOne⟩ := exists_contDiff_one_on_cthickening_tsupport_subset
    hU (hζcompact.isCompact.prod hηcompact.isCompact) (Set.prod_mono hζsupport hηsupport)
  let rt := localizedTimeDeriv b q QW
  let ri := localizedGradient b q QG
  let rii (i : Fin d) := localizedHessian b q QG QH i i
  obtain ⟨hrTime, hrtMem⟩ := localized_time_jet_univ hU hq_memLp hQW_memLp hq_time hb hbCompact hbSub
  obtain ⟨hrVelocity, hriiVelocity, hrMem, hriMem, hH⟩ := localized_spatial_jet_univ (P := Eq)
    hU hq_memLp hQG_memLp (fun j i h => h ▸ hQHdiag_memLp j) hq_velocity
    (fun j i h => h ▸ hQG_velocity j) hb hbCompact hbSub
  have hriiMem (i : Fin d) : MemLp (rii i) 2 volume := hH i i rfl
  have hrLoc := hrMem.locallyIntegrable (by norm_num)
  have hrtLoc := hrtMem.locallyIntegrable (by norm_num)
  have hriLoc (i : Fin d) := (hriMem i).locallyIntegrable (by norm_num)
  have hriiLoc (i : Fin d) := (hriiMem i).locallyIntegrable (by norm_num)
  have hlimits := localized_energy_integral_limits U η hη hηcompact ζ hζ hζcompact
    rt ri rii hrtMem hriMem hriiMem
  have hsmoothEq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      2 * (∫ z in U, ζ z.1 * SpacetimeMollifier.spacetimeMollification ε rt z *
        localizedGradientDivergence η
          (fun z i => SpacetimeMollifier.spacetimeMollification ε (ri i) z)
          (fun z i _j => SpacetimeMollifier.spacetimeMollification ε (rii i) z) z ∂volume) =
      -(∫ z in U, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ i : Fin d, SpacetimeMollifier.spacetimeMollification ε (ri i) z ^ 2
        ∂volume) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let u := SpacetimeMollifier.spacetimeMollification ε (localizedScalar b q)
    have hu := SpacetimeMollifier.contDiff_spacetimeMollification hε _ hrLoc
    have ht := SpacetimeMollifier.timeDerivative_spacetimeMollification hε _ _ hrLoc hrtLoc hrTime
    have hg (z : TimeVelocity d) (i : Fin d) := congrFun
      (SpacetimeMollifier.velocityGradient_spacetimeMollification hε i _ _ hrLoc (hriLoc i) (hrVelocity i)) z
    have hh (z : TimeVelocity d) (i : Fin d) := congrFun
      (SpacetimeMollifier.velocityHessian_spacetimeMollification hε hrLoc (hriLoc i) (hriiLoc i)
        (hrVelocity i) (hriiVelocity i i rfl)) z
    have hs := smoothGradient_timeEnergy s₀ s₁ O hO u hu η hη hηcompact hηsupport ζ hζ hζcompact hζsupport
    dsimp only [u] at hs
    simpa only [U, rt, ri, rii, ht, localizedGradientDivergence, hg, hh] using hs
  have hleftT := hlimits.1.const_mul 2
  have hrightT := hlimits.2.neg
  have hleftAsRight := hleftT.congr' hsmoothEq
  have hlocalIdentity := tendsto_nhds_unique hleftAsRight hrightT
  obtain ⟨_, hrtEq, hriEq, hriiEq⟩ := Parabolic.localized_jet_eqOn_plateau q QW QG QH hbOne
  have hsub : K ⊆ Metric.thickening δ K := Metric.self_subset_thickening hδ K
  have hid := weak_energy_integrands_eq_of_eqOn_cutoff_support QW rt QG QH ri rii η ζ
    (hrtEq.mono hsub) (fun i => (hriEq i).mono hsub) (fun i => (hriiEq i i).mono hsub)
  have htargetInt := weak_energy_targets_integrableOn U QW QG QH hQW_memLp
    hQG_memLp hQHdiag_memLp η hη hηcompact ζ hζ hζcompact
  refine ⟨htargetInt.1, htargetInt.2, ?_⟩
  rw [show (∫ z in U, ζ z.1 * QW z * localizedGradientDivergence η QG QH z
      ∂volume) = ∫ z in U, ζ z.1 * rt z * localizedGradientDivergence η
        (fun z i => ri i z) (fun z i _j => rii i z) z ∂volume by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => (hid.1 z).symm]
  rw [show (∫ z in U, _root_.deriv ζ z.1 * η z.2 ^ 2 *
      ∑ i : Fin d, QG z i ^ 2 ∂volume) =
      ∫ z in U, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ i : Fin d, ri i z ^ 2 ∂volume by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => (hid.2 z).symm]
  exact hlocalIdentity

end

end HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy
