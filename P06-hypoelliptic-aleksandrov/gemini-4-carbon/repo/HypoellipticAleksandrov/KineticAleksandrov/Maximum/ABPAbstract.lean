module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.Comparison
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractDefect
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.MajorantAbstract
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractHolder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Set MeasureTheory
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- Potential comparison with the operator inequality derived from its source premises. -/
theorem abp_potential_comparison {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (A : FullKineticCoefficient d) (u W g : KineticPoint d → ℝ)
    (hu : IsKineticC112On u (forwardCylinder Z₀ R hR))
    (hW : IsKineticC112On W (forwardCylinder Z₀ R hR))
    (hW0 : ∀ P ∈ forwardCylinder Z₀ R hR, 0 ≤ W P)
    (hWop : ∀ P ∈ forwardCylinder Z₀ R hR, forwardKineticOperator A W P = -g P)
    (hA : ∀ P ∈ forwardCylinder Z₀ R hR, (A P.time P.position P.velocity).PosSemidef)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2)
    (ε : ℝ) (hε : 0 < ε)
    (hmajor : ∀ P ∈ closure (innerCylinder Z₀ R hR δ hδ0 hδlt),
      abpPositiveCutoff ε (u P) * max (-forwardKineticOperator A u P) 0 ≤ g P)
    (M : ℝ) (hboundary : ∀ P ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt,
      max (u P) 0 ≤ M) :
    ∀ P ∈ innerCylinder Z₀ R hR δ hδ0 hδlt, u P ≤ M + W P + ε := by
  let w := fun P => u P + (-1) * W P + (-ε)
  have hw := comparison_regular_add
    (comparison_regular_add hu (comparison_regular_const_mul hW (-1)))
    (comparison_regular_const (-ε) (forwardCylinder Z₀ R hR))
  obtain ⟨hr,heq⟩ := innerCylinder_eq_forwardCylinder Z₀ R hR δ hδ0 hδlt
  obtain ⟨hr',heqB⟩ := innerExitBoundary_eq_exitBoundary Z₀ R hR δ hδ0 hδlt
  let Q := forwardCylinder (innerCentre Z₀ δ) (innerRatio R hR δ hδ0 hδlt * R) hr
  have hcl : closure Q ⊆ forwardCylinder Z₀ R hR := by
    dsimp only [Q]
    rw [← heq]
    exact closure_innerCylinder_subset Z₀ R hR δ hδ0 hδlt
  have hQi := subset_closure.trans hcl
  have hsub : ∀ P ∈ Q, 0 < w P → 0 ≤ forwardKineticOperator A w P := by
    intro P hP hpos
    have hPQ := hQi hP
    have hup : ε ≤ u P := by
      have hn := hW0 P hPQ
      dsimp only [w] at hpos
      linarith only [hpos,hn]
    have hθ := (abpPositiveCutoff_spec hε).2.2.2 (u P) hup
    have hPc : P ∈ closure (innerCylinder Z₀ R hR δ hδ0 hδlt) := by
      rw [heq]
      exact subset_closure hP
    have hm := hmajor P hPc
    rw [hθ,one_mul] at hm
    dsimp only [w]
    rw [comparison_forwardOperator_add
      (comparison_regular_add hu (comparison_regular_const_mul hW (-1)))
      (comparison_regular_const (-ε) _) A hPQ,
      comparison_forwardOperator_add hu (comparison_regular_const_mul hW (-1)) A hPQ,
      comparison_forwardOperator_const_mul hW (-1) A hPQ,
      comparison_forwardOperator_const, hWop P hPQ]
    linarith only [hm,(le_max_left (-forwardKineticOperator A u P) 0)]
  have hb : sSup ((fun P => max (w P) 0) '' exitBoundary (innerCentre Z₀ δ)
      (innerRatio R hR δ hδ0 hδlt * R) hr) ≤ M := by
    apply csSup_le ((comparison_exitBoundary_nonempty (innerCentre Z₀ δ) _ hr).image _)
    rintro _ ⟨P,hP,rfl⟩
    have hPb : P ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt := by
      rw [heqB]
      exact hP
    have hle : w P ≤ u P := by
      have hn := hW0 P (hcl hP.1)
      dsimp only [w]
      linarith only [hn,hε]
    exact (max_le_max_right 0 hle).trans (hboundary P hPb)
  intro P hP
  rw [heq] at hP
  have h := ((kinetic_comparison (innerCentre Z₀ δ) _ hr A w (fun P hP => hA P (hQi hP)) (hw.continuousOn.mono hcl) (comparison_regular_mono hw hQi) hsub) P (subset_closure hP)).trans hb
  dsimp only [w] at h
  linarith only [h]




/-- Kinetic form of the majorant lemma. -/
theorem exists_smooth_majorant_kinetic {d : ℕ} {U K : Set (KineticPoint d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {h F : KineticPoint d → ℝ} (hcont : ContinuousOn h U) (hnn : ∀ z ∈ U, 0 ≤ h z)
    (hF : ∀ᵐ z ∂(volume.restrict U), h z ≤ F z)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => g ((KineticPoint.equivProd d).symm x)) ∧
      HasCompactSupport g ∧ tsupport g ⊆ U ∧ (∀ z, 0 ≤ g z) ∧ (∀ z ∈ K, h z ≤ g z) ∧
      eLpNorm g p (volume.restrict U) ≤ eLpNorm F p (volume.restrict U) + ENNReal.ofReal ε  := by
  have isAddHaarMeasure_volume_coordinates :
      (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))).IsAddHaarMeasure := by
    have h1 : (volume : Measure (PDE.Vec d × PDE.Vec d)).IsAddHaarMeasure :=
      Measure.prod.instIsAddHaarMeasure volume volume
    exact Measure.prod.instIsAddHaarMeasure volume volume
  have := isAddHaarMeasure_volume_coordinates
  let e := KineticPoint.homeomorphProd d
  have hmp : MeasurePreserving e volume volume := KineticPoint.measurePreserving_equivProd d
  have hemb := e.measurableEmbedding
  have hpre : ∀ s : Set (KineticPoint d), e ⁻¹' (e.symm ⁻¹' s) = s := fun s => by
    ext z
    simp
  have hmpU : MeasurePreserving e (volume.restrict U) (volume.restrict (e.symm ⁻¹' U)) := by
    simpa only [hpre] using hmp.restrict_preimage_emb hemb (e.symm ⁻¹' U)
  have hU' := hU.preimage e.symm.continuous
  have hK' := e.symm.isCompact_preimage.2 hK
  have hKU' : e.symm ⁻¹' K ⊆ e.symm ⁻¹' U := preimage_mono hKU
  have hcont' :=
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


variable {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
local notation "Q" => forwardCylinder Z₀ R hR
local notation "μQ" => volume.restrict Q

/-- The Green-measure argument needs only continuous, pointwise positive diffusion. -/
theorem kinetic_abp_abstract_of_continuous
    (A : FullKineticCoefficient d)
    (hAcont : ContinuousOn (fun P : KineticPoint d => A P.time P.position P.velocity) Q)
    (hApos : ∀ P ∈ Q, (A P.time P.position P.velocity).PosSemidef)
    (q : ℝ) (hq : 1 < q) (K : ℝ) (hK : 0 < K)
    (Γ : KineticPoint d → Measure (KineticPoint d))
    (hpotential : ∀ g : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun z => g ((KineticPoint.equivProd d).symm z)) →
      HasCompactSupport g → tsupport g ⊆ Q → (∀ P, 0 ≤ g P) →
      IsKineticC112On (fun P => ∫ z, g z ∂Γ P) Q ∧
      (∀ P ∈ Q, 0 ≤ ∫ z, g z ∂Γ P) ∧
      (∀ P ∈ Q, forwardKineticOperator A (fun P => ∫ z, g z ∂Γ P) P = -g P))
    (hdensity : ∀ P ∈ Q, ∃ G : KineticPoint d → ℝ,
      Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      Γ P = (μQ).withDensity (fun z => ENNReal.ofReal (G z)) ∧
      (eLpNorm G (ENNReal.ofReal q) μQ).toReal ≤ K ∧ MemLp G (ENNReal.ofReal q) μQ)
    (u g₀ : KineticPoint d → ℝ)
    (hcont : ContinuousOn u (closure Q)) (hreg : IsKineticC112On u Q)
    (hg₀0 : ∀ P ∈ Q, 0 ≤ g₀ P)
    (hLp : MemLp g₀ (ENNReal.ofReal (q / (q - 1))) μQ)
    (hsub : ∀ᵐ P ∂μQ, -g₀ P ≤ forwardKineticOperator A u P) :
    ∀ P ∈ closure Q, u P ≤
      sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) +
      K * (eLpNorm ({P | 0 < u P}.indicator g₀)
        (ENNReal.ofReal (q / (q - 1))) μQ).toReal := by
  let : IsFiniteMeasureOnCompacts (volume : Measure (KineticPoint d)) :=
    Measure.IsFiniteMeasureOnCompacts.map
      (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))
      (KineticPoint.homeomorphProd d).symm
  let p := q / (q - 1)
  have hpq := Real.HolderConjugate.conjExponent hq
  have hQ := isOpen_forwardCylinder Z₀ R hR
  let F := {P | 0 < u P}.indicator g₀
  have hFeq : (Q ∩ {P | 0 < u P}).indicator g₀ =ᵐ[μQ] F := by
    filter_upwards [ae_restrict_mem hQ.measurableSet] with P hP
    simp [indicator, hP, F]
  have hFs : MeasurableSet (Q ∩ {P | 0 < u P}) :=
    (hreg.continuousOn.isOpen_inter_preimage hQ isOpen_Ioi).measurableSet
  have hFp := (hLp.indicator hFs).ae_eq hFeq
  let N := (eLpNorm F (ENNReal.ofReal p) μQ).toReal
  let M := sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR)
  have hinterior : ∀ P ∈ Q, u P ≤ M + K * N := by
    intro P hP
    apply le_of_forall_pos_le_add
    intro ζ hζ
    let ε := ζ / 4
    let η := ζ / (4 * (K + 1))
    have hε : 0 < ε := by positivity
    have hη : 0 < η := div_pos hζ (by positivity)
    have hbudget : K * η ≤ ζ / 4 := by
      dsimp only [η]
      rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
      nlinarith only [hK.le,hζ.le]
    obtain ⟨τ,hτ,hboundary⟩ := comparison_exit_boundary_approx Z₀ R hR u hcont hε
    obtain ⟨a,ha,hexhaust⟩ := innerCylinder_exhaustion Z₀ R hR P hP
    let δ := min (R ^ 2 / 4) (min τ a / 2)
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδlt : δ < R ^ 2 / 2 := by
      have hd : δ ≤ R ^ 2 / 4 := min_le_left _ _
      nlinarith [sq_pos_of_pos hR]
    have hδτ : δ < τ := by
      have h1 : δ ≤ min τ a / 2 := min_le_right _ _
      have h2 := min_le_left τ a
      linarith only [h1,h2,hτ]
    have hδa : δ < a := by
      have h1 : δ ≤ min τ a / 2 := min_le_right _ _
      linarith only [h1,(min_le_right τ a),ha]
    obtain ⟨hdef,hdef0,_,hdom⟩ := abp_defect_cutoff hQ.measurableSet A u g₀
      hreg hAcont hg₀0 hsub ε hε
    have hcut := abpPositiveCutoff_spec hε
    obtain ⟨g,hgs,hgc,hgQ,hg0,hmajor,hgnorm⟩ := exists_smooth_majorant_kinetic hQ
      (isCompact_closure_innerCylinder Z₀ R hR δ hδ0 hδlt)
      (closure_innerCylinder_subset Z₀ R hR δ hδ0 hδlt)

      (F := F) ((hcut.1.continuous.comp_continuousOn hreg.continuousOn).mul hdef)
      (fun P _ => mul_nonneg (hcut.2.1 _).1 (hdef0 P))
      (hdom.mono fun _ h => h.2) (ENNReal.one_le_ofReal.mpr hpq.symm.lt.le)
      ENNReal.ofReal_ne_top hη
    have hgc' : Continuous g := by
      have he : (fun P =>
          g ((KineticPoint.equivProd d).symm ((KineticPoint.homeomorphProd d) P))) = g := by
        funext P
        exact congrArg g ((KineticPoint.equivProd d).symm_apply_apply P)
      rw [← he]
      exact hgs.continuous.comp (KineticPoint.homeomorphProd d).continuous
    have hgp : MemLp g (ENNReal.ofReal p) μQ :=
      (hgc'.memLp_of_hasCompactSupport hgc).mono_measure Measure.restrict_le_self
    have hgN : (eLpNorm g (ENNReal.ofReal p) μQ).toReal ≤ N + η := by
      have hn := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨hFp.eLpNorm_ne_top,ENNReal.ofReal_ne_top⟩) hgnorm
      rw [ENNReal.toReal_add hFp.eLpNorm_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hη.le] at hn
      exact hn
    obtain ⟨hW,hW0,hWop⟩ := hpotential g hgs hgc hgQ hg0
    have hcompare := abp_potential_comparison Z₀ R hR A u
      (fun P => ∫ z, g z ∂Γ P) g hreg hW hW0 hWop hApos δ hδ0 hδlt ε hε
      hmajor (M + ε) (hboundary δ hδ0 hδlt hδτ) P (hexhaust δ hδ0 hδlt hδa)
    obtain ⟨G,hG,hG0,hΓ,hGnorm,hGq⟩ := hdensity P hP
    have hb : (∫ z, g z ∂Γ P) ≤ K * (N + η) :=
      (abp_potential_holder μQ (Γ P) G g hpq hG hG0 (Filter.Eventually.of_forall hg0) hΓ hGq hgp hGnorm).trans (mul_le_mul_of_nonneg_left hgN hK.le)
    dsimp only [ε] at hcompare
    nlinarith only [hcompare,hb,hbudget,hζ]
  exact le_on_closure hinterior hcont continuousOn_const

end HypoellipticAleksandrov.KineticAleksandrov

