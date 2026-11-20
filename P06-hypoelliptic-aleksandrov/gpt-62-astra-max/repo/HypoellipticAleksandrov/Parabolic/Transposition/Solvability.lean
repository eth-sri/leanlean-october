module
public import HypoellipticAleksandrov.Parabolic.Transposition.Kato
public import HypoellipticAleksandrov.Parabolic.Transposition.WeightedDual
import Mathlib

/-! # Transposition on an arbitrary open set

Use an equivalent finite measure with positive continuous density. Compactly supported
adjoint tests divided by this density still belong to `L²`. Thus no boundary regularity,
finite volume, or estimates at infinity are needed to obtain a solution below the envelope.
-/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity Set MeasureTheory Filter
open scoped ENNReal
variable {d k : ℕ} {U : Domain d}

private theorem exists_density : ∃ ρ : TimeVelocity d → ℝ, Continuous ρ ∧ (∀ z, 0 < ρ z) ∧ Integrable ρ := by
  let r : ℝ := Module.finrank ℝ (TimeVelocity d) + 1
  refine ⟨fun x => (1+‖x‖)^(-r), ?_, fun _ => by positivity, integrable_one_add_norm (by dsimp [r]; linarith)⟩
  exact (continuous_const.add continuous_norm).rpow_const (fun x => Or.inl (show (1 : ℝ) + ‖x‖ ≠ 0 by positivity))

private theorem testsL2 (ν : Measure (TimeVelocity d)) [IsFiniteMeasure ν] (ρ : TimeVelocity d → ℝ)
    (hc : Continuous ρ) (hp : ∀ z, 0 < ρ z) (φ : Test U) : MemLp (fun z => φ z / ρ z) 2 ν := by
  apply ((φ.contDiff.continuous.div hc (fun z => (hp z).ne')).memLp_top_of_hasCompactSupport _ ν).mono_exponent (by simp)
  simpa only [Pi.div_def,Pi.mul_def,div_eq_mul_inv] using! (φ.hasCompactSupport.mul_right (f' := fun x => (ρ x)⁻¹))

private def divided (ν : Measure (TimeVelocity d)) [IsFiniteMeasure ν] {ρ : TimeVelocity d → ℝ}
    (hc : Continuous ρ) (hp : ∀ z, 0 < ρ z) : Test U →ₗ[ℝ] Lp ℝ 2 ν where
  toFun φ := (testsL2 ν ρ hc hp φ).toLp
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]; apply MemLp.toLp_congr; exact ae_of_all _ (fun z => add_div ..)
  map_smul' c φ := by
    rw [← MemLp.toLp_const_smul]; apply MemLp.toLp_congr; exact ae_of_all _ (fun z => mul_div_assoc ..)

theorem solve_under (X : Fin (k+1) → Vector d)
    (span : KineticAleksandrov.LieAlgebraSpansOn ((unpack d) ⁻¹' (U : Set _)) (fun i => liftField (X i)))
    (F : Field d) (B : TimeVelocity d → ℝ) (hc : Continuous B) {C : ℝ} (hB : ∀ z ∈ U, 0 ≤ B z ∧ B z ≤ C)
    (est : ∀ φ : Test U, |weight U F.val φ| ≤ ∫ z in U, B z * |adjoint X φ z|) :
    ∃ w : Local U, EqOn (generator X w.val) F.val U ∧ ∀ z ∈ U, |w.val z| ≤ B z := by
  obtain ⟨ρ,hρ,hp,hi⟩ := exists_density (d := d)
  let μ := volume.restrict (U : Set (TimeVelocity d))
  let D (x) := ENNReal.ofReal (ρ x)
  let ν := μ.withDensity D
  have hm : Measurable D := hρ.measurable.ennreal_ofReal
  have ac : μ ≪ ν := withDensity_absolutelyContinuous' hm.aemeasurable (ae_of_all _ fun z => ENNReal.ofReal_ne_zero_iff.mpr (hp z))
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity ((hasFiniteIntegral_iff_ofReal (ae_of_all μ fun z => (hp z).le)).mp hi.integrableOn.hasFiniteIntegral).ne
  have transfer (g : TimeVelocity d → ℝ) : (∫ z, g z ∂ν) = ∫ z, ρ z * g z ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp [D, ENNReal.toReal_ofReal, (hp _).le]
  have mem := ae_restrict_mem (μ := volume) U.isOpen.measurableSet
  have memν : ∀ᵐ z ∂ν, z ∈ U := (withDensity_absolutelyContinuous μ D).ae_le mem
  let R := (divided ν hρ hp).comp (adjoint X (U := U))
  have hR (φ) : R φ =ᵐ[μ] (fun z => adjoint X φ z / ρ z) := ac.ae_le (testsL2 ν ρ hρ hp (adjoint X φ)).coeFn_toLp
  have he φ : (∫ z, B z * |R φ z| ∂ν) = ∫ z in U, B z * |adjoint X φ z| := by
    rw [transfer]; apply integral_congr_ae; filter_upwards [hR φ] with z hz; rw [hz,abs_div,abs_of_pos (hp z)]; field_simp [(hp z).ne'] <;> ring
  obtain ⟨u,hb,hu⟩ := weighted_dual R (weight U F.val).toLinearMap
    (MemLp.of_bound hc.aestronglyMeasurable C (memν.mono fun z hz => by simpa [Real.norm_eq_abs,abs_of_nonneg (hB z hz).1] using (hB z hz).2))
    (memν.mono fun z hz => (hB z hz).1) (fun φ => (est φ).trans_eq (he φ).symm)
  have hub := ac.ae_le hb
  have hloc : LocallyIntegrableOn (u : TimeVelocity d → ℝ) U volume := by
    apply locallyIntegrableOn_of_locallyIntegrable_restrict
    apply (hc.locallyIntegrable (μ := μ)).mono ((Lp.aestronglyMeasurable u).mono_ac ac)
    filter_upwards [hub,mem] with z hz h; simpa [Real.norm_eq_abs,abs_of_nonneg (hB z h).1] using hz
  obtain ⟨w,hw,eq⟩ := smooth_solution F span u hloc (fun φ => by
    rw [← weight_apply (F.prop.continuous.locallyIntegrable.locallyIntegrableOn U)]
    apply Eq.trans _ (hu φ); rw [transfer]
    apply integral_congr_ae; filter_upwards [hR φ] with z hz; rw [hz]; field_simp [(hp z).ne'] <;> ring)
  refine ⟨w,eq,?_⟩
  have hh := Measure.eqOn_open_of_ae_eq (μ := volume) (U := (U : Set _))
    (f := fun z => max |w.val z| (B z)) (g := B) ?_ U.isOpen
    ((smooth_local w).continuousOn.abs.sup hc.continuousOn) hc.continuousOn
  · exact fun z hz => max_eq_right_iff.mp (hh hz)
  · filter_upwards [hw,hub] with z hz h using max_eq_right (hz ▸ h)

end HypoellipticAleksandrov.Parabolic.Transposition
