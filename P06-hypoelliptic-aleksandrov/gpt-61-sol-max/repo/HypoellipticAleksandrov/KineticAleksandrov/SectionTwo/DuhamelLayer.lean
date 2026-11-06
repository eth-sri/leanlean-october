module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceLimit
public import PDEFoundation.Calculus.RegularityOrder


/-! # Terminal-layer weak identities for full kinetic source slices -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open Evolution Occupation
open scoped Topology
variable {d : ℕ}

variable {B : FullKineticCoefficient d} (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B) {b : PDE.VectorField d} (hb : IsSmoothDrift b) {D : Set (EvolutionVec d)} (hD : IsOpen D) {V u : EvolutionVec d → ℝ} (hV : ContDiffOn ℝ PDE.smoothOrder V D) (hVeq : ∀ p ∈ D, transportedOperator B b V p = 0) (huV : ∀ p ∈ D, u p = V p) (hum : Measurable u) (C : ℝ)

include hB hBs hb hD hV hVeq huV hum
/-- Testing a classical kinetic slice with the terminal-layer cutoff gives its weak identity. -/
theorem kinetic_slice_cutoff_identity  (hub : ∀ p, |u p| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ PDE.smoothOrder ψ) (hc : HasCompactSupport ψ)
    (r : ℝ) (hψD : ∀ x ∈ tsupport ψ, timeCoord d x < r → x ∈ D)
    (h : ℝ) (hh : 0 < h) :
    (∫ x, u x * (layerStep ((r - timeCoord d x) / h) * transportedAdjoint B b ψ x)) +
      ∫ x, u x * (h⁻¹ * layerKernel ((r - timeCoord d x) / h) * ψ x) = 0 := by
  let sharedTerm_0fefd121b9 := ((fun x : EvolutionVec d => h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x))
  set Ladj := transportedAdjoint B b with hLadj
  have hU  := hD
  have hχ := contDiff_sliceCutoff r h
  let φ  := fun x => sliceCutoff r h (Evolution.timeCoord d x) * ψ x


  have hφsub : tsupport φ ⊆ D := by
    intro x hx


    exact hψD x (tsupport_mul_subset_right hx) (by have := (show tsupport φ ⊆ {x | Evolution.timeCoord d x ≤ r - h} by
        apply closure_minimal
        · intro y hy

          exact (lt_of_sliceCutoff_ne_zero hh (left_ne_zero_of_mul hy)).le
        · exact isClosed_le (Evolution.timeCoord d).continuous continuous_const) hx; simp only [mem_ofPred_eq] at this; linarith)
  have key := integral_transportedAdjoint_contDiffOn hD hB hBs hb hV φ ((hχ.comp (Evolution.timeCoord d).contDiff).mul hψ) hc.mul_left hφsub
  have hR : (∫ x in D, transportedOperator B b V x * φ x) = 0 := by
    rw [setIntegral_congr_fun hU.measurableSet (g := fun _ => (0 : ℝ))]
    · simp
    · intro x hx
      simp only [hVeq _ hx, zero_mul]
  rw [hR] at key
  have hL : (∫ x in D, V x * Ladj φ x) = ∫ x, u x * Ladj φ x := by
    rw [setIntegral_congr_fun hU.measurableSet (g := fun x => u x * Ladj φ x)]
    · refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have  := fun h' => hx (hφsub h')
      rw [hLadj, transportedAdjoint_eq_zero_of_notMem_tsupport φ this, mul_zero]
    · intro x hx
      simp only [huV _ hx]
  rw [hL] at key
  have hexp : ∀ x, Ladj φ x = sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x +
      h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x := by
    intro x
    simp only [hLadj, φ]
    rw [transportedAdjoint_cutoff_mul hB hχ hψ x, deriv_sliceCutoff]
    ring
  simp_rw [hexp, mul_add] at key


  have hmeasu  := hum
  have hbd : ∀ᵐ x ∂(volume : Measure (EvolutionVec d)), ‖u x‖ ≤ C :=
    Eventually.of_forall fun x => hub x


  exact (integral_add (by
      have : Integrable (fun x => sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x) :=
        ((hχ.continuous.comp (Evolution.timeCoord d).continuous).mul ((contDiff_transportedAdjoint hB hb hψ).continuous)
          ).integrable_of_hasCompactSupport (hasCompactSupport_transportedAdjoint hc).mul_left
      exact this.bdd_mul hmeasu.aestronglyMeasurable hbd) (by
      have hk : Continuous sharedTerm_0fefd121b9 :=
        (continuous_const.mul (continuous_layerKernel.comp
          ((continuous_const.sub (Evolution.timeCoord d).continuous).div_const h))).mul hψ.continuous
      have : Integrable sharedTerm_0fefd121b9 :=
        hk.integrable_of_hasCompactSupport hc.mul_left
      exact this.bdd_mul hmeasu.aestronglyMeasurable hbd)).symm.trans key

/-- Passing the kinetic cutoff identity to the limit retains the terminal source term. -/
theorem kinetic_slice_weak_identity  (hC0 : 0 ≤ C) (hub : ∀ p, |u p| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ PDE.smoothOrder ψ) (hc : HasCompactSupport ψ)
    (r : ℝ) (hψD : ∀ x ∈ tsupport ψ, timeCoord d x < r → x ∈ D)
    (m₀ : EvolutionAmbientState d → ℝ)
    (hlim : ∀ w, Tendsto (fun t => u (packQ d (t, w)) * ψ (packQ d (t, w)))
      (𝓝[<] r) (𝓝 (m₀ w))) :
    (∫ q : ℝ × EvolutionAmbientState d,
      {q : ℝ × EvolutionAmbientState d | q.1 < r}.indicator
        (fun q => u (packQ d q) * transportedAdjoint B b ψ (packQ d q)) q) +
      ∫ w, m₀ w = 0 := by


  refine layer_slice_identity (volume : Measure (EvolutionAmbientState d)) r
    (fun q => u (packQ d q)) (fun q => ψ (packQ d q))
    (fun q => transportedAdjoint B b ψ (packQ d q))
    (hum.comp continuous_packQ.measurable) C hC0 (fun q => hub _)
    (hψ.continuous.comp continuous_packQ) (hasCompactSupport_comp_packQ hc)
    (((contDiff_transportedAdjoint hB hb hψ).continuous).comp continuous_packQ) (hasCompactSupport_comp_packQ (hasCompactSupport_transportedAdjoint (B := B) (b := b) hc)) ?_ m₀ hlim
  intro h hh
  have h1 := kinetic_slice_cutoff_identity hB hBs hb hD hV hVeq huV hum C hub
    hψ hc r hψD h hh
  rw [integral_evolution_eq_prod, integral_evolution_eq_prod] at h1
  simp only [timeCoord_packQ] at h1
  rw [← h1]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring
  · refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
