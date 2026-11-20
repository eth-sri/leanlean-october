module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelLayer
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSlice

/-!
# Cut-off weak identity for one source slice

For one source time `r`, let `V` be the classical solution of `P₀ V = 0` in the open cylinder
`{s < r, v ∈ Ω_s}`.  Testing the transported adjoint against `Θ((r - σ)/h) ψ`, whose support lies
in the open cylinder, gives the cut-off weak identity
`∫ u Θ_h Lop^*ψ + ∫ u h⁻¹ Θ'_h ψ = 0` for the bounded Borel extension `u` of `V`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ}

/-- The cutoff in the source-time variable. -/
def sliceCutoff (r h t : ℝ) : ℝ := layerStep ((r - t) / h)

theorem contDiff_sliceCutoff (r h : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sliceCutoff r h) :=
  contDiff_layerStep.comp ((contDiff_const.sub contDiff_id).div_const h)

theorem deriv_sliceCutoff (r h t : ℝ) :
    deriv (sliceCutoff r h) t = -(h⁻¹ * layerKernel ((r - t) / h)) := by
  have h1 : HasDerivAt (fun t : ℝ => (r - t) / h) (-h⁻¹) t := by
    have := ((hasDerivAt_id t).const_sub r).div_const h
    simpa [div_eq_mul_inv] using this
  have h2 := (hasDerivAt_layerStep ((r - t) / h)).comp t h1
  have : deriv (sliceCutoff r h) t = layerKernel ((r - t) / h) * -h⁻¹ := h2.deriv
  rw [this]
  ring

/-- Where the cutoff is nonzero, the time is below `r - h`. -/
theorem lt_of_sliceCutoff_ne_zero {r h t : ℝ} (hh : 0 < h) (hne : sliceCutoff r h t ≠ 0) :
    t < r - h := by
  by_contra hlt
  apply hne
  apply layerStep_of_le
  rw [div_le_iff₀ hh]
  linarith [not_lt.1 hlt]

/-- The homogeneous adjoint identity on a region for smooth tests supported there. -/
def AnnihilatesAdjointOn {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    (U : Set (EvolutionVec d)) (V : EvolutionVec d → ℝ) : Prop :=
  ∀ φ : EvolutionVec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ x in U, V x * transportedAdjoint B b φ x) = 0

/-- Testing a homogeneous adjoint identity against a terminal-layer cutoff. -/
theorem cutoff_identity_of_adjoint {B : FullKineticCoefficient d}
    (hB : IsSmoothFullKineticCoefficient B) {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {U : Set (EvolutionVec d)} (hU : MeasurableSet U) {V u : EvolutionVec d → ℝ}
    (hweak : AnnihilatesAdjointOn (B := B) (b := b) U V)
    (huV : EqOn u V U) (hum : Measurable u) {C : ℝ} (hub : ∀ x, |u x| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    {r h : ℝ} (hh : 0 < h) (hψU : ∀ x ∈ tsupport ψ, Evolution.timeCoord d x < r → x ∈ U) :
    (∫ x, u x * (layerStep ((r - Evolution.timeCoord d x) / h) * transportedAdjoint B b ψ x)) +
      ∫ x, u x * (h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) = 0 := by
  let Ladj := transportedAdjoint B b
  have hχ := contDiff_sliceCutoff r h
  let φ : EvolutionVec d → ℝ := fun x => sliceCutoff r h (Evolution.timeCoord d x) * ψ x
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := (hχ.comp (Evolution.timeCoord d).contDiff).mul hψ
  have hφc : HasCompactSupport φ := hc.mul_left
  have hφsub : tsupport φ ⊆ U := by
    intro x hx
    have h1 : x ∈ tsupport ψ := tsupport_mul_subset_right hx
    have h2 : tsupport φ ⊆ {x | Evolution.timeCoord d x ≤ r - h} := by
      apply closure_minimal
      · intro y hy
        have hy1 : sliceCutoff r h (Evolution.timeCoord d y) ≠ 0 := left_ne_zero_of_mul hy
        exact (lt_of_sliceCutoff_ne_zero hh hy1).le
      · exact isClosed_le (Evolution.timeCoord d).continuous continuous_const
    exact hψU x h1 (by have := h2 hx; simp only [mem_ofPred_eq] at this; linarith)
  have hL : (∫ x in U, V x * Ladj φ x) = ∫ x, u x * Ladj φ x := by
    rw [setIntegral_congr_fun hU (g := fun x => u x * Ladj φ x)]
    · exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        exact mul_eq_zero_of_right _ (transportedAdjoint_eq_zero_of_notMem_tsupport φ
          (fun hx' => hx (hφsub hx')))
    · intro x hx
      exact congrArg (· * Ladj φ x) (huV hx).symm
  have key := hL.symm.trans (hweak φ hφs hφc hφsub)
  have hexp : ∀ x, Ladj φ x = sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x +
      h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x := by
    intro x
    dsimp only [Ladj, φ]
    rw [transportedAdjoint_cutoff_mul hB hχ hψ x, deriv_sliceCutoff]
    ring
  simp_rw [hexp, mul_add] at key
  have hLc : Continuous (Ladj ψ) := (contDiff_transportedAdjoint hB hb hψ).continuous
  have hLcs : HasCompactSupport (Ladj ψ) := hasCompactSupport_transportedAdjoint hc
  have hbd : ∀ᵐ x ∂(volume : Measure (EvolutionVec d)), ‖u x‖ ≤ C :=
    Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hub x
  have i1 : Integrable (fun x => u x * (sliceCutoff r h (Evolution.timeCoord d x) *
      Ladj ψ x)) := by
    have : Integrable (fun x => sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x) :=
      ((hχ.continuous.comp (Evolution.timeCoord d).continuous).mul hLc
        ).integrable_of_hasCompactSupport hLcs.mul_left
    exact this.bdd_mul hum.aestronglyMeasurable hbd
  have i2 : Integrable (fun x => u x * (h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h)
      * ψ x)) := by
    have hk : Continuous (fun x : EvolutionVec d =>
        h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
      (continuous_const.mul (continuous_layerKernel.comp
        ((continuous_const.sub (Evolution.timeCoord d).continuous).div_const h))).mul hψ.continuous
    have : Integrable (fun x : EvolutionVec d =>
        h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
      hk.integrable_of_hasCompactSupport hc.mul_left
    exact this.bdd_mul hum.aestronglyMeasurable hbd
  exact (integral_add i1 i2).symm.trans key

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
