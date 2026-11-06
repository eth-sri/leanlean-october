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

/- The transported adjoint of a smooth test is smooth. -/
theorem contDiff_transportedAdjoint {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (transportedAdjoint B b ψ) := by
  have hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun w : EvolutionVec d =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j) :=
    fun i j => (hB i j).comp (evolutionProdCLE d).contDiff
  have hF : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun w : EvolutionVec d =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) :=
    fun i j => (hA i j).mul hψ
  have hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y : EvolutionVec d =>
      fderiv ℝ (fun w : EvolutionVec d =>
        B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
        (basisV j)) := fun i j => contDiff_fderiv_apply (hF i j) _
  unfold transportedAdjoint
  refine (((contDiff_fderiv_apply hψ _).neg).add ?_).sub ?_
  · exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_fderiv_apply (hG i j) _
  · refine ContDiff.sum fun l _ => ?_
    exact ((contDiff_pi.1 hb l).comp (diffusedCoord d).contDiff).mul
      (contDiff_fderiv_apply hψ _)

/- The transported adjoint of a compactly supported test is compactly supported. -/
theorem hasCompactSupport_transportedAdjoint {B : FullKineticCoefficient d}
    {b : PDE.Vec d → PDE.Vec d} {ψ : EvolutionVec d → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (transportedAdjoint B b ψ) :=
  HasCompactSupport.intro hc fun _ hx => transportedAdjoint_eq_zero_of_notMem_tsupport ψ hx

/- The cutoff in the source-time variable. -/
def sliceCutoff (r h t : ℝ) : ℝ := layerStep ((r - t) / h)

theorem contDiff_sliceCutoff (r h : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sliceCutoff r h) :=
  contDiff_layerStep.comp ((contDiff_const.sub contDiff_id).div_const h)

theorem deriv_sliceCutoff (r h t : ℝ) :
    deriv (sliceCutoff r h) t = -(h⁻¹ * layerKernel ((r - t) / h)) := by
  have h1 : HasDerivAt (fun t : ℝ => (r - t) / h) (-h⁻¹) t := by
    have := ((hasDerivAt_id t).const_sub r).div_const h
    simpa [div_eq_mul_inv] using this
  have : deriv (sliceCutoff r h) t = layerKernel ((r - t) / h) * -h⁻¹ := ((hasDerivAt_layerStep ((r - t) / h)).comp t h1).deriv
  rw [this]
  ring

/- Where the cutoff is nonzero, the time is below `r - h`. -/
theorem lt_of_sliceCutoff_ne_zero {r h t } (hh : 0 < h) (hne : sliceCutoff r h t ≠ 0) :
    t < r - h := by
  by_contra hlt
  apply hne
  apply layerStep_of_le
  rw [div_le_iff₀ hh]
  linarith [not_lt.1 hlt]

/- **Cut-off weak identity for one source slice.** -/
end HypoellipticAleksandrov.KineticAleksandrov.Occupation
