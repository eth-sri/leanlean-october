module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Compact evaluation of continuous representatives

The closed graph theorem controls continuous representatives of a closed L2 subspace.
The application to homogeneous kinetic solutions supplies the representatives by Hörmander.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsOpenPosMeasure]
  (U K : Set E) (hU : IsOpen U) (hKU : K ⊆ U)
  (hK : IsCompact K) (hKi : K ⊆ closure (interior K))
  (H : Submodule ℝ (Lp ℝ 2 (μ.restrict U))) (hH : IsClosed (H : Set (Lp ℝ 2 (μ.restrict U))))
  (hrep : ∀ u : H, ∃ f : E → ℝ, ContinuousOn f U ∧
    (u.1 : E → ℝ) =ᵐ[μ.restrict U] f)

/-- Chosen continuous representative of a homogeneous L2 class. -/
def continuousWeakRepresentative (u : H) : E → ℝ := (hrep u).choose

omit [NormedSpace ℝ E] [BorelSpace E] [μ.IsOpenPosMeasure] in
/-- The chosen representative is continuous on the open domain. -/
theorem continuousWeakRepresentative_continuous (u : H) :
    ContinuousOn (continuousWeakRepresentative μ U H hrep u) U :=
  (hrep u).choose_spec.1

omit [NormedSpace ℝ E] [BorelSpace E] [μ.IsOpenPosMeasure] in
/-- The chosen representative equals its L2 class almost everywhere. -/
theorem continuousWeakRepresentative_ae (u : H) :
    (u.1 : E → ℝ) =ᵐ[μ.restrict U] continuousWeakRepresentative μ U H hrep u :=
  (hrep u).choose_spec.2

/-- Restriction of the uniquely determined continuous representative to a compact set. -/
def compactRepresentativeMap : H →ₗ[ℝ] C(K, ℝ) := by
  let f := continuousWeakRepresentative μ U H hrep
  have hc (u : H) : ContinuousOn (f u) U :=
    continuousWeakRepresentative_continuous μ U H hrep u
  have he (u : H) : (u.1 : E → ℝ) =ᵐ[μ.restrict U] f u :=
    continuousWeakRepresentative_ae μ U H hrep u
  refine { toFun := fun u => ⟨fun z => f u z, (hc u).comp_continuous
      continuous_subtype_val (fun z => hKU z.2)⟩, map_add' := ?_, map_smul' := ?_ }
  · intro u v
    have hae : f (u + v) =ᵐ[μ.restrict U] (fun z => f u z + f v z) := by
      filter_upwards [he (u + v), he u, he v, Lp.coeFn_add u.1 v.1] with z ha hb hd heq
      simp_all
    have hpoint := Measure.eqOn_open_of_ae_eq hae hU (hc (u + v)) ((hc u).add (hc v))
    aesop
  · intro c u
    have hae : f (c • u) =ᵐ[μ.restrict U] (fun z => c * f u z) := by
      filter_upwards [he (c • u), he u, Lp.coeFn_smul c u.1] with z ha hb heq
      simp_all
    have hpoint := Measure.eqOn_open_of_ae_eq hae hU (hc (c • u))
      (continuousOn_const.mul (hc u))
    aesop

/-- Evaluation agrees pointwise with any actual continuous representative of the class. -/
theorem compactRepresentativeMap_apply_eq (u : H) (g : E → ℝ)
    (hg : ContinuousOn g U) (he : (u.1 : E → ℝ) =ᵐ[μ.restrict U] g) (z : K) :
    compactRepresentativeMap μ U K hU hKU H hrep u z = g z := by
  have hae := (continuousWeakRepresentative_ae μ U H hrep u).symm.trans he
  have hpoint := Measure.eqOn_open_of_ae_eq hae hU
    (continuousWeakRepresentative_continuous μ U H hrep u) hg
  aesop

include hK hKi hH in
/-- Compact evaluation of the continuous representatives is a continuous linear map. -/
theorem continuous_compactRepresentativeMap :
    Continuous (compactRepresentativeMap μ U K hU hKU H hrep) := by
  classical
  let  := isCompact_iff_compactSpace.mp hK
  apply LinearMap.continuous_of_seq_closed_graph
  intro u x y hu hy
  let f := continuousWeakRepresentative μ U H hrep
  have hf := continuousWeakRepresentative_continuous μ U H hrep x
  have hx := continuousWeakRepresentative_ae μ U H hrep x
  have hlp : Tendsto (fun n => (u n).1) atTop _ :=
    continuous_subtype_val.tendsto x |>.comp hu
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlp).exists_seq_tendsto_ae
  have hseq : ∀ᵐ z ∂μ.restrict U, ∀ n, (u n).1 z = f _ z :=
    ae_all_iff.mpr (fun n => continuousWeakRepresentative_ae μ U H hrep _)
  let yext  := fun z => if hz : z ∈ K then y ⟨z, hz⟩ else 0
  have hyc : ContinuousOn yext K := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert y.continuous using 1
    grind
  have heq : yext =ᵐ[μ.restrict K] f x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKU hae,
      ae_restrict_of_ae_restrict_of_subset hKU hseq,
      ae_restrict_of_ae_restrict_of_subset hKU hx, ae_restrict_mem hK.measurableSet]
      with z hz hs hxz hzK
    have hp := (continuous_eval_const ⟨z, hzK⟩).tendsto y |>.comp hy
    have hpσ := hp.comp hσ.tendsto_atTop
    have hactual : Tendsto (fun n => f (u (σ n)) z) atTop (𝓝 (f x z)) := by
      grind
    have hp' : Tendsto (fun n => f _ z) atTop _ := hpσ
    rw [show yext z = y _ from dite_eq_left hzK]
    exact tendsto_nhds_unique hp' hactual
  have hpoint := Measure.eqOn_of_ae_eq heq hyc (hf.mono hKU) hKi
  aesop

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
