module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.MajorantAbstract
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Smooth majorants on kinetic points

Kinetic form of the source step Proposition 6.2.  The kinetic carrier
`KineticPoint d` is identified with `ℝ × (Vec d × Vec d)` by `KineticPoint.equivProd`,
which is a homeomorphism carrying kinetic volume to product Lebesgue measure.  Smoothness
of a function `g : KineticPoint d → ℝ` is read in these coordinates, i.e. as
`ContDiff ℝ (⊤ : ℕ∞) (g ∘ (KineticPoint.equivProd d).symm)`.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov

open MeasureTheory Set
open scoped ENNReal

/- Product Lebesgue measure on the coordinate space of kinetic points is an additive Haar
measure. -/
theorem exists_smooth_majorant_kinetic {d : ℕ} {U K : Set (KineticPoint d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {h F : KineticPoint d → ℝ} (hcont : ContinuousOn h U) (hnn : ∀ z ∈ U, 0 ≤ h z)
    (hF : ∀ᵐ z ∂(volume.restrict U), h z ≤ F z)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => g ((KineticPoint.equivProd d).symm x)) ∧
      HasCompactSupport g ∧ tsupport g ⊆ U ∧ (∀ z, 0 ≤ g z) ∧ (∀ z ∈ K, h z ≤ g z) ∧
      eLpNorm g p (volume.restrict U) ≤ eLpNorm F p (volume.restrict U) + ENNReal.ofReal ε := by
  have : (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))).IsAddHaarMeasure := by
      have h1 : (volume : Measure (PDE.Vec d × PDE.Vec d)).IsAddHaarMeasure :=
        Measure.prod.instIsAddHaarMeasure volume volume
      exact Measure.prod.instIsAddHaarMeasure volume volume

    /- Kinetic form of the majorant lemma. -/
  let e := KineticPoint.homeomorphProd d
  have hmp : MeasurePreserving e volume volume := KineticPoint.measurePreserving_equivProd d
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have hpre : ∀ s : Set (KineticPoint d), e ⁻¹' (e.symm ⁻¹' s) = s := fun s => by
    ext z
    simp
  have hmpU : MeasurePreserving e (volume.restrict U) (volume.restrict (e.symm ⁻¹' U)) := by
    simpa only [hpre] using hmp.restrict_preimage_emb hemb (e.symm ⁻¹' U)
  have hU' : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hK' : IsCompact (e.symm ⁻¹' K) := e.symm.isCompact_preimage.2 hK
  have hKU' : e.symm ⁻¹' K ⊆ e.symm ⁻¹' U := preimage_mono hKU
  have hcont' : ContinuousOn (h ∘ e.symm) (e.symm ⁻¹' U) :=
    hcont.comp e.symm.continuous.continuousOn (fun x hx => hx)
  have hnn' : ∀ x ∈ e.symm ⁻¹' U, 0 ≤ (h ∘ e.symm) x := fun x hx => hnn _ hx
  have hF' : ∀ᵐ x ∂(volume.restrict (e.symm ⁻¹' U)), (h ∘ e.symm) x ≤ (F ∘ e.symm) x := by
    have hsymm : MeasurePreserving e.symm (volume.restrict (e.symm ⁻¹' U))
        (volume.restrict U) := by
      exact MeasurePreserving.symm e.toMeasurableEquiv hmpU
    exact hsymm.quasiMeasurePreserving.ae hF
  obtain ⟨g₀, hg1, hg2, hg3, hg4, hg5, hg6⟩ := exists_smooth_majorant_eLpNorm_le
    (E := ℝ × (PDE.Vec d × PDE.Vec d)) volume hU' hK'
    hKU' hcont' hnn' hF' hp hpt hε
  have hnormEq' : ∀ f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ,
      eLpNorm f p (volume.restrict (e.symm ⁻¹' U)) = eLpNorm (f ∘ e) p (volume.restrict U) := by
    intro f
    rw [← hmpU.map_eq, hemb.eLpNorm_map_measure]
  have hnormEq : eLpNorm (F ∘ e.symm) p (volume.restrict (e.symm ⁻¹' U)) =
      eLpNorm F p (volume.restrict U) := by
    rw [hnormEq']
    congr 1
  refine ⟨g₀ ∘ e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (fun x => (g₀ ∘ e) ((KineticPoint.equivProd d).symm x)) = g₀ := by
      funext x
      exact congrArg g₀ (e.apply_symm_apply x)
    rw [this]
    exact hg1
  · exact hg2.comp_homeomorph e
  · rw [tsupport_comp_eq_preimage g₀ e]
    exact fun z hz => hg3 hz
  · exact fun z => hg4 _
  · intro z hz
    have := hg5 (e z) (by simpa using hz)
    simpa using this
  · rw [← hnormEq, ← hnormEq']
    exact hg6

end HypoellipticAleksandrov.KineticAleksandrov
