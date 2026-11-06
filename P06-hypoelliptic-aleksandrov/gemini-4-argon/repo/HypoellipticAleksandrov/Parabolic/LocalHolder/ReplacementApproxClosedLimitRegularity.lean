module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxLocalSequence
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxUniformLp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.Parabolic.ScalarClassical
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Regular
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxCollarGeometry
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxControlledFamilies
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxHomogeneousLimit
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxUniformSeed

/-! # Classical interior regularity of the continuous closed-cylinder limit

Uniform convergence bounds all outer value energies. Nested compact product collars and
the actual local sequence theorem then cover the prescribed open cylinder.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Topology MatrixOrder Matrix.Norms.Elementwise
open scoped BigOperators

/- The actual uniform closed-cylinder limit of homogeneous classical functions is classical. -/
theorem homogeneous_continuousMap_limit_is_classical {d }
    (a T : ℝ) (Ω ) (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (u : ℕ → TimeVelocity d → ℝ)
    (hu : ∀ n, IsScalarC12On (u n) (Ioo a T ×ˢ Ω))
    (hEq : ∀ n z, z ∈ Ioo a T ×ˢ Ω → scalarTimeDerivative (u n) z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian (u n) z) = 0)
    (U : ℕ → C(scalarParabolicClosedCylinder a T Ω, ℝ))
    (V )
    (hUeq : ∀ (n : ℕ) (z : scalarParabolicClosedCylinder a T Ω), U n z = u n z)
    (hlim : Tendsto U atTop (𝓝 V)) :
    IsScalarC12On (continuousMapZeroExtension V) (Ioo a T ×ˢ Ω) ∧
      ∀ z ∈ Ioo a T ×ˢ Ω, scalarTimeDerivative (continuousMapZeroExtension V) z +
        matrixContraction (coefficientAt A z)
          (scalarSpatialHessian (continuousMapZeroExtension V) z) = 0 := by
  classical
  let K := scalarParabolicClosedCylinder a T Ω
  let D := Ioo a T ×ˢ Ω
  have hD : IsOpen D := isOpen_Ioo.prod hΩ
  have hDc := isCompact_closure_local_product a T hΩc
  have hKc : IsCompact K := isCompact_Icc.prod hΩc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let : IsFiniteMeasure (timeVelocityVolumeOn D) := ⟨by
    simpa only [timeVelocityVolumeOn, Measure.restrict_apply_univ] using
      lt_of_le_of_lt (measure_mono subset_closure) hDc.measure_lt_top⟩
  have hDK : D ⊆ K := fun z hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, subset_closure hz.2⟩
  obtain ⟨B₀, hB₀⟩ := (Metric.isBounded_range_of_tendsto U hlim).exists_norm_le
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hub (n : ℕ) (z : TimeVelocity d) (hz : z ∈ D) : |u n z| ≤ B := by
    rw [← hUeq n ⟨z, hDK hz⟩, ← Real.norm_eq_abs]
    exact ((U n).norm_coe_le_norm ⟨z, hDK hz⟩).trans
      ((hB₀ _ (mem_range_self n)).trans (le_max_left _ _))
  have hun (n : ℕ) : ParabolicMemLpOn D 2 (u n) := by
    apply MemLp.of_bound ((hu n).continuousOn.aestronglyMeasurable hD.measurableSet) B
    apply ae_restrict_of_forall_mem hD.measurableSet
    intro z hz
    simpa only [Real.norm_eq_abs] using hub n z hz
  have hq (n : ℕ) : IntegrableOn (fun z => u n z ^ 2) D := by
    simpa only [Real.norm_eq_abs, sq_abs, timeVelocityVolumeOn, IntegrableOn] using
      (hun n).integrable_norm_pow (by norm_num)
  let N := ((timeVelocityVolumeOn D) univ).toReal * B ^ 2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hb (n : ℕ) : (∫ z in D, u n z ^ 2) ≤ N :=
    integral_square_le_measure_mul_bound_sq (u n) (hun n) B hB
      (ae_restrict_of_forall_mem hD.measurableSet (fun z hz => hub n z hz))
  have hvK := continuousOn_continuousMapZeroExtension V
  have hlocal : ∀ z ∈ D, ∃ S : Set (TimeVelocity d), IsOpen S ∧ z ∈ S ∧
      IsScalarC12On (continuousMapZeroExtension V) S ∧
      (∀ y ∈ S, scalarTimeDerivative (continuousMapZeroExtension V) y +
        matrixContraction (coefficientAt A y)
          (scalarSpatialHessian (continuousMapZeroExtension V) y) = 0) := by
    intro z hz
    obtain ⟨O₀, O₁, O₂, hO₀, hO₀c, hO₀Ω, hO₁, hO₁c, hO₁O₀,
      hO₂, hO₂c, hO₂O₁, hzO₂⟩ : ∃ O₀ O₁ O₂ : Set (PDE.Vec d),
      IsOpen O₀ ∧ IsCompact (closure O₀) ∧ closure O₀ ⊆ Ω ∧
      IsOpen O₁ ∧ IsCompact (closure O₁) ∧ closure O₁ ⊆ O₀ ∧
      IsOpen O₂ ∧ IsCompact (closure O₂) ∧ closure O₂ ⊆ O₁ ∧ z.2 ∈ O₂ := by
      let x := z.2
      have hx := hz.2
      obtain ⟨O₀, hO₀, hxO₀, hO₀Ω, hO₀c⟩ :=
        exists_open_between_and_isCompact_closure (isCompact_singleton (x := x)) hΩ
          (singleton_subset_iff.mpr hx)
      obtain ⟨O₁, hO₁, hxO₁, hO₁O₀, hO₁c⟩ :=
        exists_open_between_and_isCompact_closure (isCompact_singleton (x := x)) hO₀ hxO₀
      obtain ⟨O₂, hO₂, hxO₂, hO₂O₁, hO₂c⟩ :=
        exists_open_between_and_isCompact_closure (isCompact_singleton (x := x)) hO₁ hxO₁
      exact ⟨O₀, O₁, O₂, hO₀, hO₀c, hO₀Ω, hO₁, hO₁c, hO₁O₀,
        hO₂, hO₂c, hO₂O₁, hxO₂ (mem_singleton x)⟩
    let q₀ := (a + z.1) / 2
    let p₀ := (q₀ + z.1) / 2
    let s₀ := (p₀ + z.1) / 2
    let q₁ := (T + z.1) / 2
    let p₁ := (q₁ + z.1) / 2
    let s₁ := (p₁ + z.1) / 2
    have htimes : a < q₀ ∧ q₀ < p₀ ∧ p₀ < s₀ ∧ s₀ < z.1 ∧
        z.1 < s₁ ∧ s₁ < p₁ ∧ p₁ < q₁ ∧ q₁ < T := by
      dsimp [q₀, p₀, s₀, q₁, p₁, s₁]
      rcases hz.1 with ⟨hal, hrT⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hal, hrT]
    rcases htimes with ⟨haq₀, hq₀p₀, hp₀s₀, hs₀z, hzs₁, hs₁p₁, hp₁q₁, hq₁T⟩
    let S := Ioo s₀ s₁ ×ˢ O₂
    have hS : IsOpen S := isOpen_Ioo.prod hO₂
    have hSc := isCompact_closure_local_product s₀ s₁ hO₂c
    have hO₂Ω := hO₂O₁.trans (subset_closure.trans
      (hO₁O₀.trans (subset_closure.trans hO₀Ω)))
    have hSD := closure_local_product_subset
      (haq₀.trans (hq₀p₀.trans hp₀s₀)) ((hs₁p₁.trans hp₁q₁).trans hq₁T) hO₂Ω
    have huS (n : ℕ) : ParabolicMemLpOn S 2 (u n) :=
      memLp_on_of_continuousOn_compact_closure (hu n).continuousOn hS hSc hSD 2
    obtain ⟨hvS, hstrong⟩ := tendsto_local_toLp_of_continuousMap_tendsto K S
      hS hSc (hSD.trans hDK) U V hlim u huS hUeq
    have _h_xinl_0 : IsScalarC12On (continuousMapZeroExtension V) (Ioo s₀ s₁ ×ˢ O₂) ∧ ∀ z ∈ Ioo s₀ s₁ ×ˢ O₂, scalarTimeDerivative (continuousMapZeroExtension V) z + matrixContraction (coefficientAt A z) (scalarSpatialHessian (continuousMapZeroExtension V) z) = 0 := by
      have hs₀s₁ := (hs₀z.trans hzs₁)
      have hO₂ne : O₂.Nonempty := ⟨z.2, hzO₂⟩
      let v := (continuousMapZeroExtension V)
      have hvcont := (hvK.mono ((subset_closure.trans hSD).trans hDK))
      have hQD := closure_local_product_subset haq₀ hq₁T hO₀Ω
      have hPQ := closure_local_product_subset hq₀p₀ hp₁q₁ hO₁O₀
      have hPD := hPQ.trans (subset_closure.trans hQD)
      have hPS := hp₀s₀.trans (hs₀s₁.trans hs₁p₁)
      have hO₁Ω := hO₁O₀.trans (subset_closure.trans hO₀Ω)
      let J (n : ℕ) := classicalLocalW12Jet (u n) (hu n) (isOpen_Ioo.prod hO₁)
        (isCompact_closure_local_product p₀ p₁ hO₁c) hPD
      obtain ⟨Cs, hCs, hseedrun⟩ := exists_uniform_classical_seed_constant
        a T q₀ p₀ p₁ q₁ hq₀p₀ hPS.le hp₁q₁ Ω O₀ O₁ hΩ
        (isCompact_closure_local_product a T hΩc) hO₀ hO₀c
        (isCompact_closure_local_product q₀ q₁ hO₀c) hQD hO₁ hO₁c hO₁O₀
        (isCompact_closure_local_product p₀ p₁ hO₁c) hPQ A hA lam Lam hlam hlamLam hlo hhi
      have hseed (n : ℕ) : ((J n).toWeakDerivativeFamily
          (isOpen_Ioo.prod hO₁)).squaredL2Norm ≤ Cs * N :=
        (hseedrun (u n) (hu n) (hq n) (hEq n)).trans
          (mul_le_mul_of_nonneg_left (hb n) hCs)
      have hJEq (n : ℕ) := classicalLocalW12Jet_homogeneous_equation
        (u n) (hu n) (isOpen_Ioo.prod hO₁)
        (isCompact_closure_local_product p₀ p₁ hO₁c) hPD A (hEq n)
      obtain ⟨C, D, hC, hDb, hDzero⟩ := exists_controlled_homogeneous_higher_families
        a p₀ s₀ s₁ p₁ T (haq₀.trans hq₀p₀) hp₀s₀ hs₀s₁ hs₁p₁ (hp₁q₁.trans hq₁T)
        hΩ hO₁ hO₁c hO₁Ω hO₂ hO₂ne hO₂c hO₂O₁
        lam Lam hlam hlamLam A hA hlo hhi J hJEq (Cs * N) (mul_nonneg hCs hN) hseed
      exact scalarC12_homogeneous_of_strongL2_limit (Ioo s₀ s₁ ×ˢ O₂)
        (isOpen_Ioo.prod hO₂) A hA Lam
        (fun z _ i j => abs_apply_le_of_loewner hlam (hlo z.1 z.2) (hhi z.1 z.2) i j)
        u D huS v hvS hvcont hstrong C hC hDb hDzero
    exact ⟨S, hS, ⟨⟨hs₀z, hzs₁⟩, hzO₂⟩, _h_xinl_0⟩
  refine ⟨scalarC12On_of_locally_scalarC12On (fun z hz => ?_), ?_⟩
  · obtain ⟨S, hS, hzS, huS, _⟩ := hlocal z hz
    exact ⟨S, hS, hzS, huS⟩
  · intro z hz
    obtain ⟨S, _, hzS, _, heqS⟩ := hlocal z hz
    exact heqS z hzS

end HypoellipticAleksandrov.Parabolic.LocalHolder
