module

public import Mathlib
public import PottsDiscontinuity.AnalyticTools.Implicit

/-! # Local sections in an admissible state region -/

public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

/-- An interior regular zero has a continuous local section in the state
region, with the local uniqueness needed by compact continuation. The auxiliary
section is extended outside its local domain by the base state; the equation
is asserted only locally. -/
theorem local_section_of_analytic_regular_interior_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Set ℝ} {C : Set E} {F : ℝ × E → E}
    (t : P) (x : C) (hF : AnalyticAt ℝ F (t.val, x.val))
    (hzero : F (t.val, x.val) = 0) (hx : x.val ∈ interior C)
    (e : E ≃L[ℝ] E)
    (he : (fderiv ℝ F (t.val, x.val)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      (e : E →L[ℝ] E)) :
    ∃ φ : P → C, ContinuousAt φ t ∧ φ t = x ∧
      (∀ᶠ u in 𝓝 t, F (u.val, (φ u).val) = 0) ∧
      ∃ W : Set (P × C), IsOpen W ∧ (t, x) ∈ W ∧
        ∀ u y, (u, y) ∈ W → F (u.val, y.val) = 0 → y = φ u := by
  classical
  obtain ⟨ψ, hψbase, hψanalytic, W, V, hWopen, hVopen, hWbase, hVbase, hbranch, hunique⟩ :=
    PottsDiscontinuity.AnalyticTools.exists_analytic_implicitFunction_with_local_uniqueness
      hF hzero e he
  have hψC : ∀ᶠ u in 𝓝 t.val, ψ u ∈ C :=
    hψanalytic.continuousAt.eventually (by rw [hψbase]; exact mem_interior_iff_mem_nhds.mp hx)
  have hsub : ContinuousAt (Subtype.val : P → ℝ) t := continuous_subtype_val.continuousAt
  let φ : P → C := fun u => if h : ψ u.val ∈ C then ⟨ψ u.val, h⟩ else x
  have hφeq : (fun u : P => (φ u).val) =ᶠ[𝓝 t] fun u => ψ u.val := by
    filter_upwards [(hsub.eventually hψC)] with u hu
    grind
  have hvalcont :=
    (hψanalytic.continuousAt.comp hsub).congr_of_eventuallyEq hφeq
  have hφbase : φ t = x := by
    grind
  let f : P × C → ℝ × E := fun z => (z.1.val, z.2.val)
  refine ⟨φ, (tendsto_subtype_rng.mpr hvalcont), hφbase, ?_, f ⁻¹' W, hWopen.preimage (by fun_prop), hWbase, ?_⟩
  · have hnearV : ∀ᶠ u : P in 𝓝 t, u.val ∈ V := hsub.eventually (hVopen.mem_nhds hVbase)
    filter_upwards [hnearV, hφeq] with u hu heq
    grind
  · grind

end PottsDiscontinuity.Bethe
