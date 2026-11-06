module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelLayerLimit
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelCutoff
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelLayer
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSlice

/-!
# The weak identity of one source slice, with its terminal boundary term

Passing to the limit `h ↓ 0` in the cut-off identity of `ParabolicDuhamelSliceWeak` (the
terminal-layer limit of `ParabolicDuhamelLayerLimit`) gives, for the bounded Borel extension `u`
of the slice solution,
`∫_{σ < r} u Lop^* ψ + ∫ g(r,·) ψ(r,·) = 0`, in the product coordinates `(σ, (v, z))`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ}

/- Packing product coordinates `(σ, (v, z))` into the packed evolution space. -/
def packQ (d : ℕ) (q : ℝ × (PDE.Vec d × PDE.Vec d)) : EvolutionVec d :=
  packPoint q.1 q.2.1 q.2.2

@[simp] theorem timeCoord_packQ (q : ℝ × (PDE.Vec d × PDE.Vec d)) :
    Evolution.timeCoord d (packQ d q) = q.1 := timeCoord_packPoint _ _ _

@[simp] theorem diffusedCoord_packQ (q : ℝ × (PDE.Vec d × PDE.Vec d)) :
    diffusedCoord d (packQ d q) = q.2.1 := diffusedCoord_packPoint _ _ _

@[simp] theorem evolutionToTimeVelocity_packQ (q : ℝ × (PDE.Vec d × PDE.Vec d)) :
    evolutionToTimeVelocity d (packQ d q) = (q.1, q.2.1) :=
  Prod.ext (timeCoord_packQ q) (diffusedCoord_packQ q)

theorem packQ_eq_symm (q : ℝ × (PDE.Vec d × PDE.Vec d)) :
    packQ d q = (evolutionProdMeasurableEquiv d).symm q := by
  rw [MeasurableEquiv.eq_symm_apply, evolutionProdMeasurableEquiv_apply]
  simp [packQ, evolutionProdCLE, evolutionProdLinearEquiv]

theorem continuous_packQ : Continuous (packQ d) := by
  have : packQ d = (evolutionProdCLE d).symm := by
    funext q; rfl
  rw [this]
  exact (evolutionProdCLE d).symm.continuous

/- Integrals over the packed space are integrals over product coordinates. -/
theorem integral_evolution_eq_prod (F : EvolutionVec d → ℝ) :
    ∫ x, F x = ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), F (packQ d q) := by
  have h := (measurePreserving_evolutionProdMeasurableEquiv (n := d)).integral_comp'
    (fun q => F ((evolutionProdMeasurableEquiv d).symm q))
  simp only [MeasurableEquiv.symm_apply_apply] at h
  rw [h]
  simp only [← packQ_eq_symm]

theorem hasCompactSupport_comp_packQ {f : EvolutionVec d → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun q => f (packQ d q)) := by
  have : (fun q => f (packQ d q)) = f ∘ (evolutionProdCLE d).symm.toHomeomorph := by
    funext q; rfl
  rw [this]
  exact hf.comp_homeomorph _

/- **The weak identity of one source slice.**  In product coordinates the integral of the bounded
Borel extension `u` of the slice solution against `Lop^* ψ` over the slab `σ < r` equals minus the
terminal boundary term `∫ m₀`, where `m₀` is the left limit of `u ψ` at `σ = r`. -/
theorem slice_weak_identity {B' : CoefficientField d}
    (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B'))
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {D } (hD : IsOpen D) {V u }
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V D)
    (hVeq : ∀ p ∈ D, scalarParabolicOperator B' (fun _ _ => 0) V p = 0)
    (huV : ∀ p ∈ D, u p = V p) (hum : Measurable u) (C : ℝ) (hC0 : 0 ≤ C)
    (hub : ∀ p, |u p| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (r : ℝ) (hψD : ∀ x ∈ tsupport ψ, Evolution.timeCoord d x < r →
      evolutionToTimeVelocity d x ∈ D)
    (m₀ : PDE.Vec d × PDE.Vec d → ℝ)
    (hlim : ∀ w : PDE.Vec d × PDE.Vec d,
      Tendsto (fun t => u (t, w.1) * ψ (packQ d (t, w))) (𝓝[<] r) (𝓝 (m₀ w))) :
    (∫ q : ℝ × (PDE.Vec d × PDE.Vec d), {q : ℝ × (PDE.Vec d × PDE.Vec d) | q.1 < r}.indicator
        (fun q => u (q.1, q.2.1) *
          transportedAdjoint (zIndependentCoefficient B') b ψ (packQ d q)) q) +
      ∫ w : PDE.Vec d × PDE.Vec d, m₀ w = 0 := by
  have hLc : Continuous (transportedAdjoint (zIndependentCoefficient B') b ψ) :=
    (contDiff_transportedAdjoint hB hb hψ).continuous
  have hLcs := hasCompactSupport_transportedAdjoint (B := zIndependentCoefficient B') (b := b) hc
  refine layer_slice_identity (volume : Measure (PDE.Vec d × PDE.Vec d)) r
    (fun q => u (q.1, q.2.1)) (fun q => ψ (packQ d q))
    (fun q => transportedAdjoint (zIndependentCoefficient B') b ψ (packQ d q))
    (hum.comp (measurable_fst.prodMk (measurable_snd.fst))) C hC0 (fun q => hub _)
    (hψ.continuous.comp continuous_packQ) (hasCompactSupport_comp_packQ hc)
    (hLc.comp continuous_packQ) (hasCompactSupport_comp_packQ hLcs) ?_ m₀ hlim
  intro h hh
  have h1 : (∫ x, u (evolutionToTimeVelocity d x) *
        (layerStep ((r - Evolution.timeCoord d x) / h) *
          transportedAdjoint (zIndependentCoefficient B') b ψ x)) +
      ∫ x, u (evolutionToTimeVelocity d x) *
        (h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) = 0 := by
    set Qp := evolutionToTimeVelocity d with hQp
    set Ladj := transportedAdjoint (zIndependentCoefficient B') b with hLadj
    have hQc : Continuous Qp := Qp.continuous
    have hU : IsOpen (Qp ⁻¹' D) := hD.preimage hQc
    have hχ := contDiff_sliceCutoff r h
    let φ : EvolutionVec d → ℝ := fun x => sliceCutoff r h (Evolution.timeCoord d x) * ψ x
    have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := (hχ.comp (Evolution.timeCoord d).contDiff).mul hψ
    have hφc : HasCompactSupport φ := hc.mul_left
    have hφsub : tsupport φ ⊆ Qp ⁻¹' D := by
      intro x hx
      have h1 : x ∈ tsupport ψ := tsupport_mul_subset_right hx
      have h2 : tsupport φ ⊆ {x | Evolution.timeCoord d x ≤ r - h} := by
        apply closure_minimal
        · intro y hy
          have hy1 : sliceCutoff r h (Evolution.timeCoord d y) ≠ 0 := left_ne_zero_of_mul hy
          exact (lt_of_sliceCutoff_ne_zero hh hy1).le
        · exact isClosed_le (Evolution.timeCoord d).continuous continuous_const
      exact hψD x h1 (by have := h2 hx; simp only [mem_ofPred_eq] at this; linarith)
    have key := integral_transportedAdjoint_zIndep hB hb hD hV hφs hφc hφsub
    have hR : (∫ x in Qp ⁻¹' D, scalarParabolicOperator B' (fun _ _ => 0) V (Qp x) * φ x) = 0 := by
      rw [setIntegral_congr_fun hU.measurableSet (g := fun _ => (0 : ℝ))]
      · simp
      · intro x hx
        simp only [hVeq _ hx, zero_mul]
    rw [hR] at key
    have hL : (∫ x in Qp ⁻¹' D, V (Qp x) * Ladj φ x) = ∫ x, u (Qp x) * Ladj φ x := by
      rw [setIntegral_congr_fun hU.measurableSet (g := fun x => u (Qp x) * Ladj φ x)]
      · refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
        have : x ∉ tsupport φ := fun h' => hx (hφsub h')
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
    have hLc : Continuous (Ladj ψ) := (contDiff_transportedAdjoint hB hb hψ).continuous
    have hLcs : HasCompactSupport (Ladj ψ) := hasCompactSupport_transportedAdjoint hc
    have hmeasu : Measurable (fun x => u (Qp x)) := hum.comp hQc.measurable
    have hbd : ∀ᵐ x ∂(volume : Measure (EvolutionVec d)), ‖u (Qp x)‖ ≤ C :=
      Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hub (Qp x)
    have i1 : Integrable (fun x => u (Qp x) * (sliceCutoff r h (Evolution.timeCoord d x) *
        Ladj ψ x)) := by
      have : Integrable (fun x => sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x) :=
        ((hχ.continuous.comp (Evolution.timeCoord d).continuous).mul hLc
          ).integrable_of_hasCompactSupport hLcs.mul_left
      exact this.bdd_mul hmeasu.aestronglyMeasurable hbd
    have i2 : Integrable (fun x => u (Qp x) * (h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h)
        * ψ x)) := by
      have hk : Continuous (fun x : EvolutionVec d =>
          h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
        (continuous_const.mul (continuous_layerKernel.comp
          ((continuous_const.sub (Evolution.timeCoord d).continuous).div_const h))).mul hψ.continuous
      have : Integrable (fun x : EvolutionVec d =>
          h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
        hk.integrable_of_hasCompactSupport hc.mul_left
      exact this.bdd_mul hmeasu.aestronglyMeasurable hbd
    exact (integral_add i1 i2).symm.trans key
  rw [integral_evolution_eq_prod, integral_evolution_eq_prod] at h1
  simp only [evolutionToTimeVelocity_packQ, timeCoord_packQ] at h1
  rw [← h1]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring
  · refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
