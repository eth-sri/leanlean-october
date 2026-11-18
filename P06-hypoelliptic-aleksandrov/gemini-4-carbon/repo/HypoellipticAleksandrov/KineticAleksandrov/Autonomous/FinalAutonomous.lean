module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABPPotentials
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstract
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateReflection
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PDEFoundation.Measure.OneDimensionalCoordinate
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelDominated
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelBoundary
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateSource
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFuture
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionDomination
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationGreenRemainder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationStatement
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.LocalisedSource
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibilitySource
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyDensity
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.AssemblySource
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionTerminalDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartSlabBound

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic TheoremA Filter ContinuousLinearMap HypoellipticAleksandrov.Parabolic ProbabilityTheory
open scoped Convolution Topology ENNReal

/-- The backward smooth estimate retains the positive-set source and the same constant. -/
theorem autonomous_smooth_localised_of_below_four_density
    (hdensity : BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (p : ℝ)
    (hp : criticalP ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩ < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (P₀ : Point) (R : ℝ), 0 < R → ∀ (u f : Point → ℝ),
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        autonomousScalarOperator A.a u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C * R ^ (2 - 6 / p) *
            (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
              (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal  := by
  have forward_autonomous_abp_of_below_four_density :
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (u g : Point → ℝ),
      ContinuousOn u (closure (forwardCylinder Z₀ R hR)) →
      IsKineticC112On u (forwardCylinder Z₀ R hR) →
      (∀ P ∈ forwardCylinder Z₀ R hR, 0 ≤ g P) →
      MemLp g (ENNReal.ofReal p) (volume.restrict (forwardCylinder Z₀ R hR)) →
      (∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR),
        -g P ≤ forwardScalarOperator A.a u P) →
      ∀ P ∈ closure (forwardCylinder Z₀ R hR), u P ≤
        sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) +
          C * R ^ (2 - 6 / p) *
            (eLpNorm ({P | 0 < u P}.indicator g) (ENNReal.ofReal p)
              (volume.restrict (forwardCylinder Z₀ R hR))).toReal := by
    have autonomous_conjugate_identities (hp : 1 < p) :
        (p / (p - 1)) / (p / (p - 1) - 1) = p ∧
        6 / (p / (p - 1)) - 4 = 2 - 6 / p := by
      have hq : p / (p - 1) - 1 ≠ 0 := by
        have : 1 < p / (p - 1) := (one_lt_div (sub_pos.mpr hp)).mpr (by linarith)
        exact sub_ne_zero.mpr this.ne'
      constructor <;> field_simp [(ne_of_gt (lt_trans zero_lt_one hp)), (sub_ne_zero.mpr hp.ne'), hq] <;> ring
    obtain ⟨alpha, ha, ha1, -, hq, hqa⟩ := exists_autonomous_exponents lam Lam hlam hLam p hp
    obtain ⟨C, hC, hden⟩ := hdensity hH hLE lam Lam hlam hLam alpha (p / (p - 1))
      ⟨ha, ha1⟩ ⟨hq, hqa⟩
    have hp1 : 1 < p := by linarith only [((criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2 (by simpa using hLam)⟩).1), hp]
    have hid := autonomous_conjugate_identities hp1
    refine ⟨C, hC, ?_⟩
    intro A Z₀ R hR u g hcont hreg hg0 hLp hsub
    have hAc : ContinuousOn (fun P =>
        autonomousCoefficient A.a P.time P.position P.velocity) (forwardCylinder Z₀ R hR) := by
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_pi.mpr
      intro j
      exact (A.smooth.continuous.comp
        (((continuous_apply 0).comp continuous_position).prodMk
          ((continuous_apply 0).comp continuous_velocity))).continuousOn
    have hpos : ∀ P ∈ forwardCylinder Z₀ R hR,
        (autonomousCoefficient A.a P.time P.position P.velocity).PosSemidef := by
      intro P _
      have heq : autonomousCoefficient A.a P.time P.position P.velocity =
          A.a (P.position 0) (P.velocity 0) • 1 := by
        ext i j
        fin_cases i
        fin_cases j
        simp [autonomousCoefficient]
      rw [heq]
      exact Matrix.PosSemidef.smul Matrix.PosSemidef.one
        (hlam.le.trans (A.bounds _ _).1)
    have hden' : ∀ P ∈ forwardCylinder Z₀ R hR, ∃ G : Point → ℝ,
        Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR P =
          (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
            (fun z => ENNReal.ofReal (G z)) ∧
        (eLpNorm G (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤ C * R ^ (2 - 6 / p) ∧
        MemLp G (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (forwardCylinder Z₀ R hR)) := by
      intro P hP
      obtain ⟨G, hG, hG0, heq, hGLp, hGN⟩ := hden A Z₀ R hR P hP
      rw [hid.2] at hGN
      refine ⟨G, hG, hG0, ?_, hGN, hGLp⟩
      simp only [autonomousCylinderGreen, dite_eq_left hP]
      exact heq
    have hs : ∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR),
        -g P ≤ forwardKineticOperator (autonomousCoefficient A.a) u P := by
      simpa only [forwardOperator_autonomous] using hsub
    have hl : MemLp g (ENNReal.ofReal ((p / (p - 1)) / (p / (p - 1) - 1)))
        (volume.restrict (forwardCylinder Z₀ R hR)) := by rwa [hid.1]
    simpa only [hid.1] using (kinetic_abp_abstract_of_continuous Z₀ R hR (autonomousCoefficient A.a) hAc hpos (p / (p - 1)) hq (C * R ^ (2 - 6 / p)) (mul_pos hC (Real.rpow_pos_of_pos hR _)) (autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR) (autonomous_cylinder_green_potentials hH hLE hlam hLam A Z₀ R hR) hden' u g hcont hreg hg0 hl hs)
  obtain ⟨C, hC, hforward⟩ := forward_autonomous_abp_of_below_four_density
  refine ⟨C, hC, ?_⟩
  intro A P₀ R hR u f hcont hreg hLp hsub P hP
  let B : SmoothAutonomous lam Lam :=
    ⟨reflectedAutonomous A.a, reflectedAutonomous_smooth A, reflectedAutonomous_bounds A⟩
  let Z₀ := kineticReflection P₀
  let Q := forwardCylinder Z₀ R hR
  let U := u ∘ kineticReflection
  let g := (fun P => max (f P) 0) ∘ kineticReflection
  have hmp := measurePreserving_reflection_forward P₀ R hR
  have hUc : ContinuousOn U (closure Q) := by
    simpa only [preimage_closure_backwardCylinder_reflection P₀ R hR] using (hcont.comp (continuous_kineticReflection 1).continuousOn (fun x hx => hx : MapsTo kineticReflection (kineticReflection ⁻¹' closure (backwardCylinder P₀ R)) _))
  have hUr : IsKineticC112On U Q := by
    simpa only [preimage_backwardCylinder_reflection P₀ R hR] using
      isKineticC112On_kineticReflection u (backwardCylinder P₀ R) hreg
  have hUs : ∀ᵐ P ∂volume.restrict Q, -g P ≤ forwardScalarOperator B.a U P := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hsub] with P hP
    rw [autonomousScalarOperator_reflection]
    exact neg_le_neg (hP.trans (le_max_left _ _))
  have hbound := hforward B Z₀ R hR U g hUc hUr (fun _ _ => le_max_right _ _) (hLp.comp_measurePreserving hmp) hUs
  have hPr : kineticReflection P ∈ closure Q := by
    rw [← preimage_closure_backwardCylinder_reflection P₀ R hR]
    change kineticReflection (kineticReflection P) ∈ closure (backwardCylinder P₀ R)
    rw [kineticReflection_involutive P]
    exact hP
  have hresult := hbound (kineticReflection P) hPr
  have hnorm : eLpNorm ({P | 0 < U P}.indicator g) (ENNReal.ofReal p)
      (volume.restrict Q) =
      eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) := by
    have hL := borelSource_memLp (isOpen_backwardCylinder P₀ R hR) true u f
      hreg.continuousOn hLp
    change MemLp ({P | 0 < u P}.indicator (fun P => max (f P) 0)) _ _ at hL
    have hfun : {P | 0 < U P}.indicator g =
        ({P | 0 < u P}.indicator (fun P => max (f P) 0)) ∘ kineticReflection := rfl
    rw [hfun]
    exact eLpNorm_comp_measurePreserving hL.aestronglyMeasurable hmp
  rw [hnorm, boundarySup_reflection P₀ R hR u] at hresult
  simpa [U, kineticReflection_involutive P] using hresult


/-- Shrinking normalized scalar bumps with fixed inner-to-outer radius ratio. -/
def scalarBorelBump (j : ℕ) : ContDiffBump (0 : ℝ × ℝ) :=
  ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
    half_lt_self (by positivity)⟩





/-- Tonelli lifts position-velocity null sets to physical spacetime. -/
theorem scalar_borel_phase_ae_lift {p : (ℝ × ℝ) → Prop}
    (hp : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), p z) :
    ∀ᵐ P ∂(volume : Measure Point), p (P.position 0, P.velocity 0) := by
  have hpv := (PDE.volumePreserving_vecOneEquivReal.prod PDE.volumePreserving_vecOneEquivReal).quasiMeasurePreserving.ae hp
  have hproj : Measure.QuasiMeasurePreserving
      (Prod.snd : ℝ × (PDE.Vec 1 × PDE.Vec 1) → PDE.Vec 1 × PDE.Vec 1) volume volume :=
    Measure.quasiMeasurePreserving_snd
  have hp' := hproj.ae hpv
  have h := (KineticPoint.measurePreserving_equivProd 1).quasiMeasurePreserving.ae hp'
  change ∀ᵐ P : Point ∂volume, p (P.position 0, P.velocity 0) at h
  exact h


/-- The literal scalar Hessian contraction defect; the classical solution stays fixed. -/
def scalarBorelError (C a : ℝ → ℝ → ℝ) (H : Point → ℝ) (P : Point) : ℝ :=
  |(C (P.position 0) (P.velocity 0) - a (P.position 0) (P.velocity 0)) * H P|


/-- Scalar ellipticity bounds the contraction defect without differentiating coefficients. -/
theorem scalar_borel_error_bound {lam Lam : ℝ} (hlam : 0 < lam)
    {C a : ℝ → ℝ → ℝ} (hC : ∀ x v, lam ≤ C x v ∧ C x v ≤ Lam)
    (ha : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) (H : Point → ℝ) (P : Point) :
    scalarBorelError C a H P ≤ 2 * Lam * |H P| := by
  change |(C (P.position 0) (P.velocity 0) - a (P.position 0) (P.velocity 0)) * H P| ≤ _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hl := hC (P.position 0) (P.velocity 0)
  have hr := ha (P.position 0) (P.velocity 0)
  apply abs_le.mpr
  constructor <;> linarith





/-- Source lemma `l:borel#autonomous`, class (b), with C₀ fixed before all coefficient and
  solution data. -/
theorem autonomous_abp_smooth_to_borel
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ) (localised : Bool)
    (hsmoothEstimate :
      ∀ a : ℝ → ℝ → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry a) →
        (∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) →
        ∀ (P₀ : Point) (R : ℝ), 0 < R →
        ∀ u f : Point → ℝ,
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        Measurable f → MemLp (fun P => max (f P) 0)
          (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
          sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C₀ * R ^ alpha * (eLpNorm (borelSource localised u f)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal)
    (a : ℝ → ℝ → ℝ) (ha : Measurable (Function.uncurry a))
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam)
    (P₀ : Point) (R : ℝ) (hR : 0 < R)
    (u f : Point → ℝ)
    (hcont : ContinuousOn u (closure (backwardCylinder P₀ R)))
    (hreg : IsKineticC112On u (backwardCylinder P₀ R))
    (hf : Measurable f) (hLp : MemLp (fun P => max (f P) 0)
      (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
    (hsub : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
      autonomousScalarOperator a u P ≤ f P) :
    ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + C₀ * R ^ alpha *
      (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R))).toReal   := by
  have scalar_borel_smooth_inner_limit (alpha C₀ : ℝ) (localised : Bool) (hsmooth : ∀ a : ℝ → ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry a) →
      (∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (P₀ : Point) (R : ℝ), 0 < R → ∀ u f : Point → ℝ,
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R), autonomousScalarOperator a u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + C₀ * R ^ alpha *
        (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R))).toReal) (a : ℝ → ℝ → ℝ) (ha : Measurable (Function.uncurry a)) (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) (C : ℕ → ℝ → ℝ → ℝ) (hC : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (C j)) ∧
      ∀ x v, lam ≤ C j x v ∧ C j x v ≤ Lam) (hc : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      Tendsto (fun j => C j z.1 z.2) atTop (𝓝 (a z.1 z.2))) {D : Set (Point)} (u : Point → ℝ) (f : Point → ℝ) (hreg : IsKineticC112On u D) (P₁ : Point) (r : ℝ) (hr : 0 < r) (hK : IsCompact (closure (backwardCylinder P₁ r))) (hKD : closure (backwardCylinder P₁ r) ⊆ D) (hf : Measurable f) (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₁ r))) (hsub : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₁ r)),
      autonomousScalarOperator a u P ≤ f P) :
      ∀ P ∈ closure (backwardCylinder P₁ r), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₁ r) + C₀ * r ^ alpha *
      (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₁ r))).toReal := by
    have scalar_borel_inner_error (K : Set Point) (hK : IsCompact K) (H : Point → ℝ) (hH : ContinuousOn H K) {p : ℝ} (hp : 0 < p) :
        (∀ j, ∀ P, scalarBorelError (C j) a H P ≤ 2 * Lam * |H P|) ∧
      (∀ j, MemLp (scalarBorelError (C j) a H) (ENNReal.ofReal p) (volume.restrict K)) ∧
      Tendsto (fun j => (eLpNorm (scalarBorelError (C j) a H)
        (ENNReal.ofReal p) (volume.restrict K)).toReal) atTop (𝓝 0) := by
      have : IsFiniteMeasureOnCompacts (volume : Measure Point) :=
        Measure.IsFiniteMeasureOnCompacts.map
          (volume : Measure (ℝ × (PDE.Vec 1 × PDE.Vec 1))) (KineticPoint.homeomorphProd 1).symm
      have : IsFiniteMeasure (volume.restrict K) := ⟨by
        rw [Measure.restrict_apply_univ]
        exact hK.measure_lt_top⟩
      have hproj : Measurable (fun P : Point => (P.position 0, P.velocity 0)) :=
        (((continuous_apply 0).comp continuous_position).prodMk
          ((continuous_apply 0).comp continuous_velocity)).measurable
      have hHm : AEStronglyMeasurable H (volume.restrict K) :=
        hH.aestronglyMeasurable hK.measurableSet
      have hm j : AEStronglyMeasurable (scalarBorelError (C j) a H) (volume.restrict K) := by
        exact continuous_abs.comp_aestronglyMeasurable
          ((((hC j).1.continuous.measurable.comp hproj).aestronglyMeasurable.restrict.sub
            (ha.comp hproj).aestronglyMeasurable.restrict).mul hHm)
      have hbounds j := scalar_borel_error_bound hlam (hC j).2 hb H
      obtain ⟨B, hB⟩ := hK.bddAbove_image hH.abs
      let M := max B 0
      have hM : 0 ≤ M := le_max_right _ _
      have hHM P (hP : P ∈ K) : |H P| ≤ M :=
        (hB (mem_image_of_mem _ hP)).trans (le_max_left _ _)
      have hLam0 := hlam.le.trans (hb 0 0).1 |>.trans (hb 0 0).2
      have hbound j : ∀ᵐ P ∂(volume.restrict K), scalarBorelError (C j) a H P ≤
          2 * Lam * M := by
        filter_upwards [ae_restrict_mem hK.measurableSet] with P hP
        exact (hbounds j P).trans (mul_le_mul_of_nonneg_left (hHM P hP) (by positivity))
      have heconv : ∀ᵐ P ∂(volume.restrict K),
          Tendsto (fun j => scalarBorelError (C j) a H P) atTop (𝓝 0) := by
        filter_upwards [ae_restrict_of_ae (scalar_borel_phase_ae_lift hc)] with P hP
        simpa [scalarBorelError] using (((hP.sub_const (a (P.position 0) (P.velocity 0))).mul_const (H P)).abs)
      refine ⟨hbounds, ?_, borel_bounded_error_norm_tendsto (volume.restrict K) hp
        (by positivity) (fun j => scalarBorelError (C j) a H) hm
        (fun j => Filter.Eventually.of_forall fun P => abs_nonneg _) hbound heconv⟩
      intro j
      apply (memLp_const (2 * Lam * M)).of_le (hm j)
      filter_upwards [hbound j] with P hP
      simpa only [scalarBorelError, Real.norm_eq_abs, abs_abs,
        abs_of_nonneg (by positivity : 0 ≤ 2 * Lam * M)] using hP
    have scalar_borel_operator_sub (C : ℝ → ℝ → ℝ) (P : Point) :
        autonomousScalarOperator C u P - autonomousScalarOperator a u P =
        -(C (P.position 0) (P.velocity 0) - a (P.position 0) (P.velocity 0)) *
          kineticVelocityHessian u P 0 0 := by
      unfold autonomousScalarOperator
      ring
    classical
    let Q := backwardCylinder P₁ r
    let K := closure Q
    let H : Point → ℝ := fun P => kineticVelocityHessian u P 0 0
    have hH :=
      (continuous_apply 0).comp_continuousOn
        ((continuous_apply 0).comp_continuousOn
          (hreg.continuousOn_kineticVelocityHessian.mono hKD))
    let Hext := K.indicator H
    let e := fun j => scalarBorelError (C j) a Hext
    have he0 j P : 0 ≤ e j P := abs_nonneg _
    have hQ : IsOpen Q := isOpen_backwardCylinder P₁ r hr
    have hQK : Q ⊆ K := subset_closure
    have hregQ := comparison_regular_mono hreg (hQK.trans hKD)
    have hHext : Measurable Hext :=
      hH.measurable_piecewise continuousOn_const hK.measurableSet
    have hproj : Measurable (fun P : Point => (P.position 0, P.velocity 0)) :=
      (((continuous_apply 0).comp continuous_position).prodMk
        ((continuous_apply 0).comp continuous_velocity)).measurable
    have hem j : Measurable (e j) :=
      continuous_abs.measurable.comp
        ((((hC j).1.continuous.measurable.comp hproj).sub (ha.comp hproj)).mul hHext)
    have heq j : e j =ᵐ[volume.restrict K] scalarBorelError (C j) a H := by
      filter_upwards [ae_restrict_mem hK.measurableSet] with P hP
      simp only [e,scalarBorelError,Hext,indicator_of_mem hP]
    obtain ⟨_,hmraw,htraw⟩ := scalar_borel_inner_error K hK H hH
      (lt_of_lt_of_le zero_lt_one hp)
    have hmK j : MemLp (e j) (ENNReal.ofReal p) (volume.restrict K) :=
      (hmraw j).ae_eq (heq j).symm
    have hμ : volume.restrict Q ≤ volume.restrict K := Measure.restrict_mono_set volume hQK
    have hme j : MemLp (e j) (ENNReal.ofReal p) (volume.restrict Q) := (hmK j).mono_measure hμ
    have hte : Tendsto (fun j => (eLpNorm (e j) (ENNReal.ofReal p)
        (volume.restrict Q)).toReal) atTop (𝓝 0) := by
      have htK : Tendsto (fun j => (eLpNorm (e j) (ENNReal.ofReal p)
          (volume.restrict K)).toReal) atTop (𝓝 0) := by
        simpa only [eLpNorm_congr_ae (heq _)] using htraw
      apply squeeze_zero (fun j => ENNReal.toReal_nonneg) _ htK
      intro j
      exact ENNReal.toReal_mono (hmK j).eLpNorm_ne_top (eLpNorm_mono_measure _ hμ)
    let G := fun j => borelSource localised u (f + e j)
    have hpert j : MemLp (fun P => max ((f + e j) P) 0) (ENNReal.ofReal p)
        (volume.restrict Q) := by
      apply (hLp.add (hme j)).of_le ((hf.add (hem j)).sup measurable_const).aestronglyMeasurable
      filter_upwards with P
      change ‖max (f P + e j P) 0‖ ≤ ‖max (f P) 0 + e j P‖
      simp only [Real.norm_of_nonneg (le_max_right _ _),
        Real.norm_of_nonneg (add_nonneg (le_max_right _ _) (he0 j P))]
      exact max_le (by linarith only [le_max_left (f P) 0])
        (add_nonneg (le_max_right (f P) 0) (he0 j P))
    have hGp j := borelSource_memLp hQ localised u (f + e j) hregQ.continuousOn (hpert j)
    have htG := borel_source_norm_tendsto hp (borelSource localised u f) G e (borelSource_memLp hQ localised u f hregQ.continuousOn hLp) hme
      (fun j => (hGp j).aestronglyMeasurable)
      (Filter.Eventually.of_forall (borelSource_nonneg localised u f))
      (fun j => Filter.Eventually.of_forall (borelSource_nonneg localised u (f + e j)))
      (fun j => Filter.Eventually.of_forall (he0 j))
      (fun j => Filter.Eventually.of_forall fun P => borelSource_error_le localised u f P (he0 j P))
      hte
    have hineq j : ∀ P ∈ K, u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₁ r) +
        C₀ * r ^ alpha * (eLpNorm (G j) (ENNReal.ofReal p) (volume.restrict Q)).toReal := by
      apply hsmooth (C j) (hC j).1 (hC j).2
        P₁ r hr u (f + e j) (hreg.continuousOn.mono hKD) hregQ (hf.add (hem j)) (hpert j)
      filter_upwards [hsub,ae_restrict_mem hQ.measurableSet] with P hsubP hP
      have heP : e j P = scalarBorelError (C j) a H P := by
        simp only [e,scalarBorelError,Hext,indicator_of_mem (hQK hP)]
      dsimp only [scalarBorelError, H] at heP
      change autonomousScalarOperator (C j) u P ≤ f P + e j P
      rw [heP]
      linarith only [(scalar_borel_operator_sub (C j) P), hsubP, (neg_le_abs ((C j (P.position 0) (P.velocity 0) - a (P.position 0) (P.velocity 0)) * H P))]
    intro P hP
    exact ge_of_tendsto
      (tendsto_const_nhds.add (tendsto_const_nhds.mul htG))
      (Filter.Eventually.of_forall fun j => hineq j P hP)
  have scalar_borel_coefficient_approximation :
      ∃ C : ℕ → ℝ → ℝ → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (C j)) ∧
        ∀ x v, lam ≤ C j x v ∧ C j x v ≤ Lam) ∧
      ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
        Tendsto (fun j => C j z.1 z.2) atTop (𝓝 (a z.1 z.2)) := by
    have scalar_borel_locallyIntegrable :
        LocallyIntegrable (Function.uncurry a) volume := by
      apply (locallyIntegrable_const Lam).mono ha.aestronglyMeasurable
      filter_upwards with z
      dsimp only [Function.uncurry]
      rw [Real.norm_of_nonneg (hlam.le.trans (hb z.1 z.2).1),
        Real.norm_of_nonneg (hlam.le.trans (hb z.1 z.2).1 |>.trans (hb z.1 z.2).2)]
      exact (hb z.1 z.2).2
    let scalarBorelConvolution (φ : ContDiffBump 0) (a : ℝ → ℝ → ℝ) :=
      fun x v => (φ.normed volume ⋆[lsmul ℝ ℝ, volume] Function.uncurry a) (x, v)
    have scalarBorelConvolution_spec (φ : ContDiffBump 0) :
        ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (scalarBorelConvolution φ a)) ∧
        ∀ x v, lam ≤ scalarBorelConvolution φ a x v ∧
          scalarBorelConvolution φ a x v ≤ Lam := by
      have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
        Measure.prod.instIsAddHaarMeasure volume volume
      have hloc := scalar_borel_locallyIntegrable
      refine ⟨φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
        φ.contDiff_normed hloc, ?_⟩
      intro x v
      have hi := φ.hasCompactSupport_normed.convolutionExists_left
        (μ := volume) (lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hloc (x, v)
      simpa [scalarBorelConvolution, convolution, lsmul_apply, integral_mul_const, φ.integral_normed] using And.intro (integral_mono ((φ.integrable_normed (μ := volume)).smul_const lam) hi (fun y => mul_le_mul_of_nonneg_left (hb ((x, v) - y).1 ((x, v) - y).2).1 (φ.nonneg_normed y))) (integral_mono hi ((φ.integrable_normed (μ := volume)).smul_const Lam) (fun y => mul_le_mul_of_nonneg_left (hb ((x, v) - y).1 ((x, v) - y).2).2 (φ.nonneg_normed y)))
    have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
      Measure.prod.instIsAddHaarMeasure volume volume
    let C := fun j => scalarBorelConvolution (scalarBorelBump j) a
    refine ⟨C, fun j => scalarBorelConvolution_spec _, ?_⟩
    have hr : Tendsto (fun j => (scalarBorelBump j).rOut) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hratio : ∀ᶠ j in atTop, (scalarBorelBump j).rOut ≤ 2 * (scalarBorelBump j).rIn := by
      filter_upwards with j
      dsimp only [scalarBorelBump]
      linarith
    exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hr hratio
      (scalar_borel_locallyIntegrable)
  obtain ⟨C,hC,hc⟩ := scalar_borel_coefficient_approximation
  apply borel_boundary_limit p hp alpha C₀ localised P₀ R hR u f hcont hLp
  intro n P hP
  have hk := isCompact_closure_reflected_innerCylinder P₀ R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2
  have hKD := closure_reflected_innerCylinder_subset P₀ R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2
  rw [kineticReflection_image_innerCylinder] at hk hKD
  have hμ := Measure.restrict_mono_set volume (subset_closure.trans hKD)
  exact scalar_borel_smooth_inner_limit alpha C₀ localised hsmoothEstimate
    a ha hb C hC hc u f hreg (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)
    (borelInnerRadius_pos R hR n) hk hKD hf (hLp.mono_measure hμ)
    (hsub.filter_mono (ae_mono hμ)) P hP


/-- Removing source localisation only increases a finite source norm. -/
theorem autonomous_localised_norm_le (P₀ : Point) (R p : ℝ) (hR : 0 < R)
    (u f : Point → ℝ) (hu : ContinuousOn u (backwardCylinder P₀ R))
    (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R))) :
    (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R))).toReal ≤
    (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R))).toReal :=
  TheoremA.localized_positive_source_norm_le volume (isOpen_backwardCylinder P₀ R hR)
    u f hu (ENNReal.ofReal p) hLp

/-- The scalar Borel passage applies with the coefficient-uniform smooth constant. -/
theorem autonomous_borel_of_below_four_density
    (hdensity : BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (p : ℝ)
    (hp : criticalP ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩ < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℝ → ℝ),
      Measurable (Function.uncurry a) → (∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (P₀ : Point) (R : ℝ), 0 < R → ∀ (u f : Point → ℝ),
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        autonomousScalarOperator a u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C * R ^ (2 - 6 / p) *
            (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
              (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hsm⟩ := autonomous_smooth_localised_of_below_four_density hdensity
    hH hLE lam Lam hlam hLam p hp
  have hp1 : 1 ≤ p := by linarith only [((criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2 (by simpa using hLam)⟩).1), hp]
  have hsmooth : ∀ a : ℝ → ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry a) →
      (∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (P₀ : Point) (R : ℝ), 0 < R → ∀ u f : Point → ℝ,
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        autonomousScalarOperator a u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C * R ^ (2 - 6 / p) *
            (eLpNorm (borelSource false u f) (ENNReal.ofReal p)
              (volume.restrict (backwardCylinder P₀ R))).toReal := by
    intro a ha hb P₀ R hR u f hcont hreg _hf hLp hsub P hP
    apply (hsm ⟨a, ha, hb⟩ P₀ R hR u f hcont hreg hLp hsub P hP).trans
    apply add_le_add_right
    exact mul_le_mul_of_nonneg_left
      (autonomous_localised_norm_le P₀ R p hR u f hreg.continuousOn hLp)
      (mul_nonneg hC.le (Real.rpow_nonneg hR.le _))
  refine ⟨C, hC, ?_⟩
  intro a ha hb P₀ R hR u f hcont hreg hf hLp hsub
  exact autonomous_abp_smooth_to_borel lam Lam hlam hLam p hp1 (2 - 6 / p) C false
    hsmooth a ha hb P₀ R hR u f hcont hreg hf hLp hsub



/-- Below a supported exit time, changing the named observation lower bound changes no face. -/
theorem enlargedBoundary_restrict_lower_eq (I J : Interval) (s L T : ℝ) (hs : s ≤ L)
    (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, L < p.time) :
    mu.restrict (visitBoundary s T I J) = mu.restrict (visitBoundary L T I J) := by
  apply Measure.restrict_congr_set
  filter_upwards [hmu] with p hp
  simp [visitBoundary, (hs.trans_lt hp), hp]




/-- The actual enlarged count is finite for every valid outer-strip initial pole. -/
theorem enlargedVisitStarts_finite_of_outer_pole
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    IsFiniteMeasure (enlargedVisitStarts hH hLE hlam hLam A c J s T P)  := by
  have enlargedVisitEntrance_eq_clipped (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
      enlargedVisitEntrance hH hLE hlam hLam A c J s T P n =
      visitEntrancePiece hH hLE hlam hLam A c J (s - 1) T P n := by
    have enlargedVisitExit_comp_eq_clipped (H : FiniteIntervalUnion) (mu : Measure Point) (hs : ∀ᵐ p ∂mu, s ≤ p.time) :
        enlargedVisitExitKernel hH hLE hlam hLam A H T ∘ₘ mu =
        visitUnionExitKernel hH hLE hlam hLam A H (s - 1) T ∘ₘ mu := by
      classical
      apply Measure.comp_congr
      filter_upwards [hs] with p hp
      change (if h : p ∈ enlargedVisitPoleSet H T then
        finiteUnionExit hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, h⟩) else 0) =
          (if h : p ∈ visitPoleSet H (s - 1) T then
            finiteUnionExit hH hLE hlam hLam A H T
              (visitPoleInclusion H (s - 1) T ⟨p, h⟩) else 0)
      have he : p ∈ enlargedVisitPoleSet H T ↔ p ∈ visitPoleSet H (s - 1) T := by
        change (p.time < T ∧ p.velocity 0 ∈ H.carrier) ↔
          (s - 1 < p.time ∧ p.time < T ∧ p.velocity 0 ∈ H.carrier)
        constructor
        · intro h
          exact ⟨by linarith, h⟩
        · exact fun h => h.2
      by_cases h : p ∈ enlargedVisitPoleSet H T
      · rw [dite_eq_left h, dite_eq_left (he.mp h)]
        rfl
      · rw [dite_eq_right h, dite_eq_right (fun hh => h (he.mpr hh))]
    have enlargedExitMixture_ae_time_gt_lower (H : FiniteIntervalUnion) (L : ℝ) (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, L ≤ p.time) :
        ∀ᵐ q ∂(enlargedVisitExitKernel hH hLE hlam hLam A H T ∘ₘ mu), L < q.time := by
      apply Measure.ae_comp_of_ae_ae
        (isOpen_lt continuous_const continuous_time).measurableSet
      filter_upwards [hmu] with p hp
      exact (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A H T p).mono
        fun q hq => hp.trans_lt hq
    let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
    have he (H : FiniteIntervalUnion) (mu : Measure Point) (hm : ∀ᵐ p ∂mu, s ≤ p.time) :=
      enlargedVisitExit_comp_eq_clipped H mu hm
    have hb (I : Interval) (mu : Measure Point) (hm : ∀ᵐ p ∂mu, s < p.time) :
        mu.restrict (visitBoundary s T I J) =
          mu.restrict (visitBoundary (s - 1) T I J) :=
      (enlargedBoundary_restrict_lower_eq I J (s - 1) s T (by linarith) mu hm).symm
    induction n with
    | zero =>
      unfold enlargedVisitEntrance visitEntrancePiece visitGamma visitInitial
      split
      · rfl
      · have hm : ∀ᵐ p ∂Measure.dirac P, s ≤ p.time :=
          (ae_dirac_iff (isClosed_le continuous_const continuous_time).measurableSet).mpr hs
        have hx := he (visitWaitingUnion c J) (Measure.dirac P) hm
        simp only [visitKernel_comp_dirac] at hx
        rw [← hx]
        exact hb _ _ ((enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A
          (visitWaitingUnion c J) T P).mono fun _ hp => hs.trans_lt hp)
    | succ n ih =>
      change ((enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T) ∘ₘ ((EA ∘ₘ enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
        (visitBoundary s T (visitActiveInterval c) J))).restrict
          (visitBoundary s T (visitEntranceInterval c) J) = _
      have hg := (enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
        fun _ hp => hp.1
      have hbeta : ∀ᵐ p ∂((EA ∘ₘ enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
          (visitBoundary s T (visitActiveInterval c) J)), s ≤ p.time :=
        (ae_restrict_mem (measurableSet_visitBoundary s T (visitActiveInterval c) J)).mono
          fun _ hp => hp.1.le
      rw [hb _ _ (enlargedExitMixture_ae_time_gt_lower (visitWaitingUnion c J) s _ hbeta), he _ _ hbeta, hb _ _ (enlargedExitMixture_ae_time_gt_lower (visitActiveUnion c J) s _ hg), he _ _ hg, ih]
      rfl
  have he : enlargedVisitStarts hH hLE hlam hLam A c J s T P =
      Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J (s - 1) T P) := by
    unfold enlargedVisitStarts
    congr 1
    funext n
    exact enlargedVisitEntrance_eq_clipped hP.1 hP.2.1 n
  rw [he]
  exact visitCount_isFiniteMeasure hH hLE hlam hLam A c J (s - 1) T (by linarith [hP.1])
    P ⟨by linarith [hP.1], hP.2⟩


/-- Every actual waiting Green kernel gives zero occupation to the core. -/
theorem enlargedWaitingGreenKernel_core_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (p : Point) :
    enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T p
      {q | q.velocity 0 ∈ c.core} = 0 := by
  classical
  change (if hp : p ∈ enlargedVisitPoleSet (visitWaitingUnion c J) T then
    finiteUnionGreen hH hLE hlam hLam A (visitWaitingUnion c J) T
      (enlargedVisitPole _ T ⟨p, hp⟩) else 0) {q | q.velocity 0 ∈ c.core} = 0
  split
  · rename_i hp
    have hz := ae_iff.mp (visitUnionGreen_ae_velocity hH hLE hlam hLam A (visitWaitingUnion c J) T (enlargedVisitPole _ T ⟨p, hp⟩))
    apply le_antisymm _ zero_le
    apply (measure_mono (show {q : Point | q.velocity 0 ∈ c.core} ⊆
        {q | q.velocity 0 ∉ (visitWaitingUnion c J).carrier} from
      fun _ hc hv => Set.disjoint_left.mp (visitWaiting_disjoint_core c J) hv hc)).trans_eq hz
  · rfl




/-- The actual outer core occupation is exactly the sum of its active visit occupations. -/
theorem enlargedOuterGreen_core_identity_of_finite_count
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)
    [IsFiniteMeasure (enlargedVisitStarts hH hLE hlam hLam A c J s T P)] :
    (enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T P).restrict
      {q | q.velocity 0 ∈ c.core} =
    Measure.sum (fun n => (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J)
      T ∘ₘ enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
        {q | q.velocity 0 ∈ c.core})   := by
  have enlargedOuterGreen_remainder_tendsto_zero (_hT : s < T) [IsFiniteMeasure (enlargedVisitStarts hH hLE hlam hLam A c J s T P)] :
      Tendsto (fun n => (enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ
      enlargedVisitEntrance hH hLE hlam hLam A c J s T P n) univ) atTop (𝓝 0) := by
    have he (n : ℕ) := enlargedVisitGreen_comp_eq_clipped hH hLE hlam hLam A
      J.toFiniteUnion s T (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n)
        ((enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hP.1 hP.2.1 n).mono
          fun _ hp => hp.1)
    have : IsFiniteMeasure (Measure.sum
        (enlargedVisitEntrance hH hLE hlam hLam A c J s T P)) := by
      change IsFiniteMeasure (enlargedVisitStarts hH hLE hlam hLam A c J s T P)
      infer_instance
    have hz := visit_green_mixture_remainder_tendsto_zero hH hLE hlam hLam A
      J.toFiniteUnion (s - 1) T (enlargedVisitEntrance hH hLE hlam hLam A c J s T P)
    simpa only [he] using hz
  have enlargedWaitingGreenMixture_core_zero (mu : Measure Point) :
      (enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T ∘ₘ mu)
      {q | q.velocity 0 ∈ c.core} = 0 := by
    have hC : MeasurableSet {q : Point | q.velocity 0 ∈ c.core} :=
      isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
    rw [Measure.bind_apply hC (Kernel.aemeasurable _)]
    simp only [enlargedWaitingGreenKernel_core_zero, lintegral_zero]
  let C : Set Point := {q | q.velocity 0 ∈ c.core}
  let GW := enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
  let GO := enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T
  let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
  let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P
  have hi : (visitInitialGreen P (visitEntranceInterval c) GW).restrict C = 0 := by
    classical
    unfold visitInitialGreen
    split
    · exact Measure.restrict_zero C
    · exact Measure.restrict_eq_zero.mpr
        (enlargedWaitingGreenKernel_core_zero hH hLE hlam hLam A c J T P)
  have hw (n : ℕ) : (GW ∘ₘ beta n).restrict C = 0 :=
    Measure.restrict_eq_zero.mpr
      (enlargedWaitingGreenMixture_core_zero (beta n))
  apply measure_eq_sum_of_remainder_mass_tendsto_zero _ _
    (fun n => (GO ∘ₘ gamma n).restrict C)
  · intro N
    have h := congrArg (fun m : Measure Point => m.restrict C)
      (enlargedAlternating_green hH hLE hlam hLam A c J s T hT P hP N)
    change (GO P).restrict C =
      (visitInitialGreen P (visitEntranceInterval c) GW +
        ∑ n ∈ Finset.range N, ((enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T) ∘ₘ gamma n + GW ∘ₘ beta n) + GO ∘ₘ gamma N).restrict C at h
    simpa [Measure.restrict_add, visit_restrict_finset_sum, hi, hw] using h
  · have hz := enlargedOuterGreen_remainder_tendsto_zero hT
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
      (fun _ => zero_le) (fun n => Measure.restrict_le_self univ)




/-- Core occupation is dominated by the actual all-time Green measure of the full visit count. -/
theorem enlargedOuterGreen_core_domination_of_finite_count
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)
    [IsFiniteMeasure (enlargedVisitStarts hH hLE hlam hLam A c J s T P)] :
    (enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T P).restrict
      {q | q.velocity 0 ∈ c.core} ≤
    (enlargedActiveGreen hH hLE hlam hLam A c
      (Measure.sum (enlargedVisitEntrance hH hLE hlam hLam A c J s T P))).restrict
        {q | q.velocity 0 ∈ c.core}  := by
  have enlargedActiveGreenMixture_le_allTime (mu : Measure Point) :
      enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu ≤
      enlargedActiveGreen hH hLE hlam hLam A c mu := by
    have enlargedActiveGreenKernel_le_allTime (p : Point) :
        enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T p ≤
        enlargedActiveGreenKernel hH hLE hlam hLam A c p := by
      classical
      by_cases hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T
      · have hv : p.velocity 0 ∈ c.active :=
          ((visitActiveUnion_carrier c J).le hp.2).1
        let H := visitActiveUnion c J
        let e := enlargedVisitPole H T ⟨p, hp⟩
        let i := finiteUnionPoleIndex H T e
        have hsub : (H.component i).carrier ⊆ (visitActiveInterval c).carrier := by
          intro v hv'
          exact ((visitActiveUnion_carrier c J).le (H.component_subset i hv')).1
        change (if ht : p ∈ enlargedVisitPoleSet H T then
          finiteUnionGreen hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, ht⟩) else 0) ≤
            (if ht : p.velocity 0 ∈ c.active then
              stripGreen hH hLE hlam hLam A (visitActiveInterval c) ⊤
                (densityClockPole c p ht) else 0)
        rw [dite_eq_left hp, dite_eq_left hv]
        exact stripGreen_mono hH hLE hlam hLam A (H.component i) (visitActiveInterval c) hsub T ⊤ le_top (finiteUnionComponentPole H T e)
      · change (if ht : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T then _ else 0) ≤ _
        rw [dite_eq_right hp]
        intro B
        exact zero_le
    unfold enlargedActiveGreen
    apply Measure.le_iff.mpr
    intro B hB
    rw [Measure.bind_apply hB (Kernel.aemeasurable _),
      Measure.bind_apply hB (Kernel.aemeasurable _)]
    exact lintegral_mono (fun p => enlargedActiveGreenKernel_le_allTime p B)
  let C : Set Point := {q | q.velocity 0 ∈ c.core}
  have hC : MeasurableSet C :=
    isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  rw [enlargedOuterGreen_core_identity_of_finite_count hH hLE hlam hLam A c J s T hT P hP]
  unfold enlargedActiveGreen
  rw [Measure.bind_sum _ _ (Kernel.aemeasurable _), Measure.restrict_sum _ hC]
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.sum_apply _ hB, Measure.sum_apply _ hB]
  apply ENNReal.tsum_le_tsum
  intro n
  exact Measure.restrict_mono_measure
    (enlargedActiveGreenMixture_le_allTime
      (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n)) C B


/-- The core domination statement, including initial poles at the named lower time. -/
theorem coreDominationStatement_holds : CoreDominationStatement := by
  classical
  intro hH hLE lam Lam hlam hLam A c J s T P hP _hbar _hJ hs
  have := enlargedVisitStarts_finite_of_outer_pole hH hLE hlam hLam A c J s T P
    ⟨hs, hP⟩
  have hT : s < T := hs.trans_lt hP.1
  have hi := enlargedOuterGreen_core_identity_of_finite_count hH hLE hlam hLam A c J s T
    hT P ⟨hs, hP⟩
  have hd := enlargedOuterGreen_core_domination_of_finite_count hH hLE hlam hLam A c J s T
    hT P ⟨hs, hP⟩
  have he : enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T P =
      stripGreen hH hLE hlam hLam A J T ⟨P, WithTop.coe_lt_coe.mpr hP.1, hP.2⟩ := by
    change (if hp : P ∈ enlargedVisitPoleSet J.toFiniteUnion T then _ else 0) = _
    rw [dite_eq_left (show P ∈ enlargedVisitPoleSet J.toFiniteUnion T from
      ⟨hP.1, by simpa only [Interval.toFiniteUnion_carrier] using hP.2⟩)]
    rfl
  rw [he] at hi hd
  exact ⟨hi, hd⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set Autonomous TheoremA Parabolic Holder
open scoped ENNReal MatrixOrder

/-- The scalar Borel passage applies with the coefficient-uniform smooth constant. -/
theorem autonomous_localised_borel_of_below_four_density
    (hdensity : BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (p : ℝ)
    (hp : criticalP ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩ < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℝ → ℝ),
      Measurable (Function.uncurry a) → (∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (P₀ : Point) (R : ℝ), 0 < R → ∀ (u f : Point → ℝ),
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        autonomousScalarOperator a u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C * R ^ (2 - 6 / p) *
            (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
              (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hsm⟩ := autonomous_smooth_localised_of_below_four_density hdensity
    hH hLE lam Lam hlam hLam p hp
  have hp1 : 1 ≤ p := by linarith only [((criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2 (by simpa using hLam)⟩).1), hp]
  have hsmooth : ∀ a : ℝ → ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry a) →
      (∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (P₀ : Point) (R : ℝ), 0 < R → ∀ u f : Point → ℝ,
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        autonomousScalarOperator a u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C * R ^ (2 - 6 / p) *
            (eLpNorm (borelSource true u f) (ENNReal.ofReal p)
              (volume.restrict (backwardCylinder P₀ R))).toReal := by
    intro a ha hb P₀ R hR u f hcont hreg _hf hLp hsub P hP
    simpa [borelSource] using (hsm ⟨a, ha, hb⟩ P₀ R hR u f hcont hreg hLp hsub P hP)
  refine ⟨C, hC, ?_⟩
  intro a ha hb P₀ R hR u f hcont hreg hf hLp hsub
  exact autonomous_abp_smooth_to_borel lam Lam hlam hLam p hp1 (2 - 6 / p) C true
    hsmooth a ha hb P₀ R hR u f hcont hreg hf hLp hsub


/-- Localized autonomous estimate relative to the density assertion and the
Hörmander and Lieberman theorems. -/
theorem kinetic_aleksandrov_autonomous_localised_relative_of_below_four_density
    (hdensity : Autonomous.BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint 1) (R : ℝ), 0 < R →
      ∀ (a : ℝ → ℝ → ℝ),
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (f u : KineticPoint 1 → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - 6 / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hborel⟩ := autonomous_localised_borel_of_below_four_density hdensity
    hH hLE lam Lam hlam hLam p hp
  refine ⟨C, hC.le, ?_⟩
  intro P₀ R hR a ha hb f u hf hcont hreg hsub hLp P hP
  have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
  let f₀ := (backwardCylinder P₀ R).indicator f
  have hf₀ : Measurable f₀ := measurable_source_indicator hQ f hf
  have hae := source_indicator_ae_eq hQ f
  have hmax : (fun P => max (f P) 0) =ᵐ[volume.restrict (backwardCylinder P₀ R)]
      (fun P => max (f₀ P) 0) := by
    filter_upwards [hae] with P hP
    change max (f P) 0 = max ((backwardCylinder P₀ R).indicator f P) 0
    rw [hP]
  have hLp₀ := hLp.ae_eq hmax
  have hsub₀ : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      autonomousScalarOperator a u P ≤ f₀ P := by
    filter_upwards [hsub, hae] with P hsub hEq
    change autonomousScalarOperator a u P ≤ (backwardCylinder P₀ R).indicator f P
    rw [hEq]
    exact hsub
  simpa only [f₀, eLpNorm_localized_source_indicator hQ f u] using (hborel a ha hb P₀ R hR u f₀ hcont hreg hf₀ hLp₀ hsub₀ P hP)




/-- The conclusion, conditional on the remaining open steps and the two classical theorems. -/
theorem kinetic_holder_autonomous_relative_of_frontier
    (hfront : Autonomous.AutonomousRemainingFrontier)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ a : ℝ → ℝ → ℝ,
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (Omega : Set (KineticPoint 1)), IsOpen Omega →
      ∀ (u : KineticPoint 1 → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), autonomousScalarOperator a u P = 0) →
      ∀ (K : Set (KineticPoint 1)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha  := by
  have autonomous_admissibility_of_below_four_density :
      ∃ C_A : ℝ,
      ∀ a : ℝ → ℝ → ℝ,
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ Omega : Set (KineticPoint 1), IsOpen Omega →
      ∀ u : KineticPoint 1 → ℝ,
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), autonomousScalarOperator a u P = 0) →
        IsAdmissibleSolution
          (fun _ x v => fun _ _ => a (x 0) (v 0)) Omega 6 C_A u := open HypoellipticAleksandrov Parabolic Autonomous in by
    have hp : 1 + bellmanAdjointExponent (Lam / lam)
        ((le_div_iff₀ hlam).2 (by simpa using hLam)) < 6 := by
      have hc := (criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2
        (by simpa using hLam)⟩).2
      change 1 + bellmanAdjointExponent _ _ < 4 at hc
      linarith only [hc]
    obtain ⟨C_A, _hC, hestimate⟩ :=
      kinetic_aleksandrov_autonomous_localised_relative_of_below_four_density
        (below_four_density_of_frontier hfront hH hLE) hH hLE lam Lam 6 hlam hLam hp
    refine ⟨C_A, ?_⟩
    intro a ha hb Omega _hOmega u _hbounded hu heq
    have hsup (w : Point → ℝ) (hw : IsKineticC112On w Omega)
        (heqw : ∀ᵐ P ∂volume.restrict Omega, autonomousScalarOperator a w P = 0) :
        IsAdmissibleSupersolution (autonomousCoefficient a) Omega 6 C_A w := by
      refine ⟨hw.continuousOn, ?_⟩
      intro P₀ R hR hQ psi hpsi
      obtain ⟨U, _hU, hUQ, hps⟩ := smoothNear_regular hpsi
      have hQQ : backwardCylinder P₀ R ⊆ Omega := subset_closure.trans hQ
      have hpr := comparison_regular_mono hps (subset_closure.trans hUQ)
      have hwr := comparison_regular_mono hw hQQ
      have hneg := comparison_regular_const_mul hwr (-1)
      have hdiff : IsKineticC112On (fun P => psi P - w P) (backwardCylinder P₀ R) := by
        simpa only [neg_one_mul, sub_eq_add_neg] using comparison_regular_add hpr hneg
      have hop : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
          autonomousScalarOperator a (fun Q => psi Q - w Q) P ≤
            autonomousScalarOperator a psi P := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hQQ heqw,
          ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P he hP
        have hadd := autonomous_operator_add hpr hneg a hP
        have hmul := autonomous_operator_const_mul hwr (-1) a hP
        simp only [neg_one_mul, ← sub_eq_add_neg] at hadd hmul
        rw [hadd, hmul, he]
        simp [le_refl]
      obtain ⟨hmeas, hLp⟩ := autonomous_test_source hlam ha hb P₀ R hR hpsi
      have hn : {P | 0 < psi P - w P} = {P | w P < psi P} := by
        ext P
        exact sub_pos
      have hbnd' : ∀ P ∈ closure (backwardCylinder P₀ R), psi P - w P ≤
          sSup ((fun P => max (psi P - w P) 0) '' kineticBoundary P₀ R) +
            C_A * R ^ (2 - (4 * (1 : ℝ) + 2) / 6) *
              (eLpNorm (localizedSource (autonomousCoefficient a) psi w) (ENNReal.ofReal 6)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
        simpa only [hn, localizedSource, backwardOperator_autonomous,
          show 4 * (1 : ℝ) + 2 = 6 by norm_num] using (hestimate P₀ R hR a ha hb (autonomousScalarOperator a psi) (fun P => psi P - w P) hmeas (hpsi.continuousOn.sub (hw.continuousOn.mono hQ)) hdiff hop hLp)
      apply csSup_le
      · exact (backwardCylinder_nonempty P₀ hR).closure.image _
      · rintro y ⟨P, hP, rfl⟩
        simpa only [Nat.cast_one] using hbnd' P hP
    refine ⟨hsup u hu heq, ?_⟩
    have hneg : IsKineticC112On (fun P => -u P) Omega := by
      simpa only [neg_one_mul] using comparison_regular_const_mul hu (-1)
    apply hsup (fun P => -u P) hneg
    filter_upwards [heq, ae_restrict_mem _hOmega.measurableSet] with P he hP
    simpa only [neg_one_mul, he, neg_zero] using (autonomous_operator_const_mul hu (-1) a hP)
  obtain ⟨C_A, hadm⟩ := autonomous_admissibility_of_below_four_density
  obtain ⟨alpha, C, ha, ha1, hholder⟩ := kinetic_holder_of_aleksandrov_aux
    1 (by norm_num) lam Lam 6 C_A hlam hLam (by norm_num)
  refine ⟨alpha, C, ha, ha1, ?_⟩
  intro a hmeas hb Omega hOmega u hbounded hu heq
  have hlo : ∀ᵐ P ∂(volume : Measure (KineticPoint 1)),
      lam • 1 ≤
        fullKineticCoefficientAt (Autonomous.autonomousCoefficient a) P :=
    Filter.Eventually.of_forall (fun P => (Autonomous.autonomous_lift_elliptic hb P).1)
  have hhi : ∀ᵐ P ∂(volume : Measure (KineticPoint 1)),
      fullKineticCoefficientAt (Autonomous.autonomousCoefficient a) P ≤
        Lam • 1 :=
    Filter.Eventually.of_forall (fun P => (Autonomous.autonomous_lift_elliptic hb P).2)
  exact hholder (Autonomous.autonomousCoefficient a)
    (Autonomous.autonomous_lift_measurable hmeas) (Autonomous.autonomous_lift_symm a)
    hlo hhi Omega hOmega u hbounded (hadm a hmeas hb Omega hOmega u hbounded hu heq)


/-- The conclusion, conditional on the remaining open steps and the two classical theorems. -/
theorem kinetic_aleksandrov_autonomous_localised_relative_of_frontier
    (hfront : Autonomous.AutonomousRemainingFrontier)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint 1) (R : ℝ), 0 < R →
      ∀ (a : ℝ → ℝ → ℝ),
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (f u : KineticPoint 1 → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - 6 / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  exact kinetic_aleksandrov_autonomous_localised_relative_of_below_four_density
    (below_four_density_of_frontier hfront hH hLE) hH hLE lam Lam p hlam hLam hp


/-- The conclusion, conditional on the remaining open steps and the two classical theorems. -/
theorem kinetic_aleksandrov_autonomous_relative_of_frontier
    (hfront : Autonomous.AutonomousRemainingFrontier)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint 1) (R : ℝ), 0 < R →
      ∀ (a : ℝ → ℝ → ℝ),
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (f u : KineticPoint 1 → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - 6 / p) *
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal  := by
  obtain ⟨C, hC, hborel⟩ := autonomous_borel_of_below_four_density (below_four_density_of_frontier hfront hH hLE)
    hH hLE lam Lam hlam hLam p hp
  refine ⟨C, hC.le, ?_⟩
  intro P₀ R hR a ha hb f u hf hcont hreg hsub hLp P hP
  have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
  let f₀ := (backwardCylinder P₀ R).indicator f
  have hf₀ : Measurable f₀ := measurable_source_indicator hQ f hf
  have hae := source_indicator_ae_eq hQ f
  have hmax : (fun P => max (f P) 0) =ᵐ[volume.restrict (backwardCylinder P₀ R)]
      (fun P => max (f₀ P) 0) := by
    filter_upwards [hae] with P hP
    change max (f P) 0 = max ((backwardCylinder P₀ R).indicator f P) 0
    rw [hP]
  have hLp₀ := hLp.ae_eq hmax
  have hsub₀ : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      autonomousScalarOperator a u P ≤ f₀ P := by
    filter_upwards [hsub, hae] with P hsub hEq
    change autonomousScalarOperator a u P ≤ (backwardCylinder P₀ R).indicator f P
    rw [hEq]
    exact hsub
  simpa only [f₀, eLpNorm_positive_source_indicator hQ f] using (hborel a ha hb P₀ R hR u f₀ hcont hreg hf₀ hLp₀ hsub₀ P hP)


namespace Autonomous

/-- The enlarged terminal measures satisfy the exact frontier domination statement. -/
theorem terminalDominationStatement_holds : TerminalDominationStatement := by
  intro hH hLE lam Lam hlam hLam A c J T P _hbar hT hJ _hvel N b hb hBT
  exact enlarged_active_terminal_le_fullspace hH hLE hlam hLam A c J
    P.time (P.time + T) P le_rfl (lt_add_of_pos_right P.time hT) hJ N b hb hBT

/-- The exact time-bin count follows from exponent-six admissibility and return. -/
theorem timeBinCountStatement_holds : TimeBinCountStatement := by
  intro hH hLE lam Lam hlam hLam
  exact timeBinCount_holds_of_return_time hH hLE hlam hLam
    (return_time hH hLE lam Lam hlam hLam
      (smoothAutonomousP6_holds hH hLE lam Lam hlam hLam))

/-- All autonomous frontier steps hold relative to the source theorem. -/
theorem autonomousRemainingFrontier_holds : AutonomousRemainingFrontier := by
  exact ⟨timeBinCountStatement_holds,
    positionStartSlabBound_holds terminalDominationStatement_holds,
    terminalDominationStatement_holds, coreDominationStatement_holds⟩

end Autonomous

end HypoellipticAleksandrov.KineticAleksandrov

