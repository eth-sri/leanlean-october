module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValue
public import Mathlib.Topology.Algebra.Indicator
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Intermediate slices of a classical terminal solution

Zero extension across the lateral boundary is continuous. Strictly earlier slices
are smooth on the open state fiber. These facts justify compact interior cutoff data.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

open Set
open scoped Topology

variable {n : ℕ} {Ω : PDE.VelocityRegion n} {γ : ℝ → PDE.Vec n} {B : FullKineticCoefficient n} {b : PDE.VectorField n} {τ r : ℝ} {F : BoundedBorel (EvolutionAmbientState n)} {u : HypoellipticAleksandrov.KineticScalarField n} (hu : IsClassicalTerminalSolution Ω γ B b τ F u)

section
variable (hrτ : r ≤ τ)

include hu hrτ
/-- A classical solution restricted to any earlier state slice is continuous on the
closed state fiber. -/
theorem IsClassicalTerminalSolution.continuousOn_slice
      :
    ContinuousOn (fun x : EvolutionAmbientState n => u ⟨r, x.1, x.2⟩)
      (closure (evolutionStateSet Ω γ r)) := by
  refine hu.2.1.comp
    (KineticPoint.continuous_mk continuous_const continuous_fst continuous_snd).continuousOn ?_
  intro x hx
  have hx' : x ∈ closure (movingDomain Ω γ r) ×ˢ (univ : PDE.VelocityRegion n) := by
    simpa only [evolutionStateSet, closure_prod_eq, closure_univ] using hx
  exact ⟨hrτ, hx'.1⟩

/-- Extending an intermediate slice by zero outside its state fiber is continuous. -/
theorem IsClassicalTerminalSolution.continuous_zeroExtended_slice
      :
    Continuous ((evolutionStateSet Ω γ r).indicator
      (fun x  => u ⟨r, x.1, x.2⟩)) := by
  apply continuous_indicator ?_ (hu.continuousOn_slice hrτ)
  intro x hx
  have hx' : x ∈ frontier (movingDomain Ω γ r) ×ˢ (univ : PDE.VelocityRegion n) := by
    simpa only [evolutionStateSet, frontier_prod_univ_eq] using hx
  exact hu.2.2.2.2.2 _ ⟨hrτ, hx'.1⟩
end


include hu in
/-- A strictly earlier slice is smooth on the open state fiber. -/
theorem IsClassicalTerminalSolution.contDiffOn_slice
     (hrτ : r < τ) :
    ContDiffOn ℝ PDE.smoothOrder (fun x : EvolutionAmbientState n => u ⟨r, x.1, x.2⟩)
      (evolutionStateSet Ω γ r) := hu.2.2.1.comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
    (fun x hx => ⟨hrτ, hx.1⟩)

/-- Multiplying an interior-smooth function by an interior-supported smooth cutoff gives
an ambient smooth function, irrespective of the original function outside the open set. -/
theorem contDiff_mul_of_tsupport_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {χ g : E → ℝ}
    (hχ : ContDiff ℝ PDE.smoothOrder χ) (hg : ContDiffOn ℝ PDE.smoothOrder g U)
    (hs : tsupport χ ⊆ U) : ContDiff ℝ PDE.smoothOrder (fun x => χ x * g x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds (hs hx)))
  · have he  := notMem_tsupport_iff_eventuallyEq.mp hx
    have hz : ContDiffAt ℝ PDE.smoothOrder (fun _ : E => (0 : ℝ)) x := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

end HypoellipticAleksandrov.KineticAleksandrov
