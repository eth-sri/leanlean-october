module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractHolder
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.MajorantKinetic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # From the source Green measures to the localised Aleksandrov estimate -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Set MeasureTheory
open scoped MatrixOrder Matrix.Norms.Elementwise

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
  let : IsFiniteMeasureOnCompacts volume :=
    Measure.IsFiniteMeasureOnCompacts.map
      volume
      (KineticPoint.homeomorphProd d).symm
  let p := q / (q - 1)
  have hpq : q.HolderConjugate p := Real.HolderConjugate.conjExponent hq
  have hp  := hpq.symm.lt
  have hQ := isOpen_forwardCylinder Z₀ R hR
  let F := {P | 0 < u P}.indicator g₀
  have hFeq : (Q ∩ {P | 0 < u P}).indicator g₀ =ᵐ[μQ] F := by
    filter_upwards [ae_restrict_mem hQ.measurableSet] with P hP
    simp only [indicator,mem_inter_iff,hP,true_and,F]
  have hFs : MeasurableSet (Q ∩ {P | 0 < u P}) :=
    (hreg.continuousOn.isOpen_inter_preimage hQ isOpen_Ioi).measurableSet
  have hFp : MemLp F (ENNReal.ofReal p) μQ := (hLp.indicator hFs).ae_eq hFeq
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
      rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
      linarith
    obtain ⟨τ,hτ,hboundary⟩ := comparison_exit_boundary_approx Z₀ R hR u hcont hε
    obtain ⟨a,ha,hexhaust⟩ := innerCylinder_exhaustion Z₀ R hR P hP
    let δ := min (R ^ 2 / 4) (min τ a / 2)
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδlt : δ < R ^ 2 / 2 := by
      grind
    have hδτ : δ < τ := by
      grind
    have hδa : δ < a := by
      grind
    obtain ⟨hdef,hdef0,_,hdom⟩ := abp_defect_cutoff hQ.measurableSet A u g₀
      hreg hAcont hg₀0 hsub ε hε
    have hcut := abpPositiveCutoff_spec hε
    obtain ⟨g,hgs,hgc,hgQ,hg0,hmajor,hgnorm⟩ := exists_smooth_majorant_kinetic hQ
      (isCompact_closure_innerCylinder Z₀ R hR δ hδ0 hδlt)
      (closure_innerCylinder_subset Z₀ R hR δ hδ0 hδlt)
      (h := fun P => abpPositiveCutoff ε (u P) * max (-forwardKineticOperator A u P) 0)
      (F := F) ((hcut.1.continuous.comp_continuousOn hreg.continuousOn).mul hdef)
      (fun P _ => mul_nonneg (hcut.2.1 _).1 (hdef0 P))
      (hdom.mono fun _ h => h.2) (ENNReal.one_le_ofReal.mpr hp.le)
      ENNReal.ofReal_ne_top hη
    have hgc' : Continuous g := hgs.continuous.comp (KineticPoint.homeomorphProd d).continuous
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
      _ g hreg hW hW0 hWop hApos δ hδ0 hδlt ε hε
      hmajor (M + ε) (hboundary δ hδ0 hδlt hδτ) P (hexhaust δ hδ0 hδlt hδa)
    obtain ⟨G,hG,hG0,hΓ,hGnorm,hGq⟩ := hdensity P hP
    have hWbound := abp_potential_holder μQ (Γ P) G g hpq hG hG0
      (Filter.Eventually.of_forall hg0) hΓ hGq hgp hGnorm
    have hb : (∫ z, g z ∂Γ P) ≤ K * (N + η) :=
      hWbound.trans (mul_le_mul_of_nonneg_left hgN hK.le)
    grind
  exact le_on_closure hinterior hcont continuousOn_const

end HypoellipticAleksandrov.KineticAleksandrov
