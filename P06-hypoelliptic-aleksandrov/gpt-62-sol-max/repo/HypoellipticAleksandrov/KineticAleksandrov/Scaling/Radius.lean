module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Unique
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Fourier
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Structure

/-!
# The source kinetic scaling (companion paper, (2.10), (2.11), Lemma 2.5)

`KineticAffineScaling.ofRadius σ₀ v₀ z₀ b r` is the change of variables
`σ = σ₀ + r² τ`, `v = v₀ + r Y`, `z = z₀ + (σ - σ₀) b(v₀) + r³ Z`.  Its rescaled coefficient and
drift are the source's `B_r` and `b_r` (`SectionTwo.scaledCoefficient`,
`SectionTwo.scaledDrift`), and its change of variables on points is
`SectionTwo.scaledPoint`.  The terminal evolution of the whole space (case W) is transported
to the rescaled whole space.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling

open MeasureTheory Set
open HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
  (scaledCoefficient scaledDrift identityDrift wholeSpace_admissible
    zeroCurve_piecewiseC1 scaledDrift_identity lop RealizesTerminalEvolution
    IsFourierProjection totalVariationNorm scaledDomain wholeSpace HasTransportBounds
    IsSectionTwoCoefficient identityDrift_bounds scaledCoefficient_sectionTwo)

namespace KineticAffineScaling

variable {d : ℕ}

/-- The source kinetic scaling `r ↦ (σ₀ + r² τ, v₀ + r Y, z₀ + (σ - σ₀) b(v₀) + r³ Z)`. -/
def ofRadius (σ₀ : ℝ) (v₀ z₀ : PDE.Vec d) (b : PDE.Vec d → PDE.Vec d)
    (r : {r : ℝ // 0 < r}) : KineticAffineScaling d where
  a := r.1 ^ 2
  c := r.1
  e := r.1 ^ 3
  σ₀ := σ₀
  y₀ := v₀
  z₀ := z₀
  w := b v₀
  a_pos := pow_pos r.2 2
  c_pos := r.2
  e_pos := pow_pos r.2 3

variable (σ₀ : ℝ) (v₀ z₀ : PDE.Vec d) (b : PDE.Vec d → PDE.Vec d) (r : {r : ℝ // 0 < r})

/-- The rescaled coefficient of `ofRadius` is the source `B_r`. -/
theorem ofRadius_coefficient (B : CoefficientField d) :
    (ofRadius σ₀ v₀ z₀ b r).coefficient (zIndependentCoefficient B) =
      zIndependentCoefficient (scaledCoefficient B σ₀ v₀ r) := by
  funext τ Y Z
  have hr : r.1 ^ 2 / r.1 ^ 2 = 1 := div_self (pow_pos r.2 2).ne'
  change (r.1 ^ 2 / r.1 ^ 2) • B (σ₀ + r.1 ^ 2 * τ) (v₀ + r.1 • Y) = _
  rw [hr, one_smul]
  rfl

/-- The rescaled drift of `ofRadius` is the source `b_r`. -/
theorem ofRadius_drift : (ofRadius σ₀ v₀ z₀ b r).drift b = scaledDrift b v₀ r := by
  funext Y
  have hr : r.1 ^ 2 / r.1 ^ 3 = r.1⁻¹ := by
    have := r.2.ne'
    field_simp
  change (r.1 ^ 2 / r.1 ^ 3) • (b (v₀ + r.1 • Y) - b v₀) = _
  rw [hr]
  rfl

end KineticAffineScaling

variable {d : ℕ}

/-- **Kernel transport for the source scaling, case W.**  If `(S, K)` realizes the terminal
evolution on the whole space with identity transport, then `(Ŝ, K̂)` (pushforward by the source
kinetic scaling) realizes it for the rescaled coefficient `B_r`, again with identity
transport. -/
theorem realizes_ofRadius_wholeSpace (σ₀ : ℝ) (v₀ z₀ : PDE.Vec d) (r : {r : ℝ // 0 < r})
    {B : CoefficientField d}
    {S : TerminalOperatorFamily (Set.univ : Set (PDE.Vec d)) (fun _ => (0 : PDE.Vec d))}
    {K : MovingFiberKernel (Set.univ : Set (PDE.Vec d)) (fun _ => (0 : PDE.Vec d))}
    (hreal : RealizesTerminalEvolution Set.univ (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
      (zIndependentCoefficient B) (identityDrift d) S K) :
    RealizesTerminalEvolution Set.univ (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
      (zIndependentCoefficient (scaledCoefficient B σ₀ v₀ r)) (identityDrift d)
      (fiberOperator (KineticAffineScaling.pushKernel
        (KineticAffineScaling.mapsDomain_wholeSpace (KineticAffineScaling.ofRadius σ₀ v₀ z₀
          (identityDrift d) r)) K) MeasurableSet.univ)
      (KineticAffineScaling.pushKernel
        (KineticAffineScaling.mapsDomain_wholeSpace (KineticAffineScaling.ofRadius σ₀ v₀ z₀
          (identityDrift d) r)) K) := by
  have h := KineticAffineScaling.realizes_pushKernel
    (KineticAffineScaling.mapsDomain_wholeSpace (KineticAffineScaling.ofRadius σ₀ v₀ z₀
      (identityDrift d) r)) isOpen_univ continuous_const MeasurableSet.univ hreal
  rw [KineticAffineScaling.ofRadius_coefficient, KineticAffineScaling.ofRadius_drift,
    scaledDrift_identity] at h
  exact h

/-- **Fourier total variation under the source scaling, case W** (companion paper, Lemma 2.5
and (2.12)).  For realizations `(S, K)` of `(B, id)` and `(S', K')` of `(B_r, id)` on the
whole space, a rescaled query `q'` (that is, `(τ, (τ', (Y, Z)))`, corresponding to the
original query `σ = σ₀ + r² τ`, `σ' = σ₀ + r² τ'`, `v = v₀ + r Y`, `z = z₀ + (σ - σ₀) v₀ + r³ Z`),
and Fourier projections `ν` (frequency `ξ`) of `K` and `ν'` (frequency `r³ ξ`) of `K'`:
`ν E = exp (-i r² (τ' - τ) ξ · v₀) ν' (r⁻¹ (E - v₀))` and `‖ν‖_TV = ‖ν'‖_TV`. -/
theorem realizes_ofRadius_fourier_tv (σ₀ : ℝ) (v₀ z₀ : PDE.Vec d) (r : {r : ℝ // 0 < r})
    {B : CoefficientField d}
    {S : TerminalOperatorFamily (Set.univ : Set (PDE.Vec d)) (fun _ => (0 : PDE.Vec d))}
    {K : MovingFiberKernel (Set.univ : Set (PDE.Vec d)) (fun _ => (0 : PDE.Vec d))}
    (hreal : RealizesTerminalEvolution Set.univ (fun _ => (0 : PDE.Vec d))
      (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d))
      (zIndependentCoefficient B) (identityDrift d) S K)
    {S' : TerminalOperatorFamily (Set.univ : Set (PDE.Vec d)) (fun _ => (0 : PDE.Vec d))}
    {K' : MovingFiberKernel (Set.univ : Set (PDE.Vec d)) (fun _ => (0 : PDE.Vec d))}
    (hreal' : RealizesTerminalEvolution Set.univ (fun _ => (0 : PDE.Vec d))
      (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d))
      (zIndependentCoefficient (scaledCoefficient B σ₀ v₀ r)) (identityDrift d) S' K')
    (q' : EvolutionQuery (Set.univ : Set (PDE.Vec d)) (fun _ => (0 : PDE.Vec d)))
    (ξ : PDE.Vec d) (ν ν' : ComplexMeasure (PDE.Vec d))
    (hν : IsFourierProjection K (KineticAffineScaling.queryMap
      (KineticAffineScaling.mapsDomain_wholeSpace
        (KineticAffineScaling.ofRadius σ₀ v₀ z₀ (identityDrift d) r)) q') ξ ν)
    (hν' : IsFourierProjection K' q' (r.1 ^ 3 • ξ) ν') :
    (∀ E : Set (PDE.Vec d), MeasurableSet E →
      ν E = Complex.exp (-Complex.I *
          ((r.1 ^ 2 * (q'.1.2.1 - q'.1.1) * PDE.vecDot ξ v₀ : ℝ) : ℂ)) *
        ν' ((fun Y : PDE.Vec d => v₀ + r.1 • Y) ⁻¹' E)) ∧
      totalVariationNorm ν = totalVariationNorm ν' := by
  have hreal'' : RealizesTerminalEvolution Set.univ (fun _ => (0 : PDE.Vec d))
      (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d))
      ((KineticAffineScaling.ofRadius σ₀ v₀ z₀ (identityDrift d) r).coefficient
        (zIndependentCoefficient B))
      ((KineticAffineScaling.ofRadius σ₀ v₀ z₀ (identityDrift d) r).drift (identityDrift d))
      S' K' := by
    rw [KineticAffineScaling.ofRadius_coefficient, KineticAffineScaling.ofRadius_drift,
      scaledDrift_identity]
    exact hreal'
  exact KineticAffineScaling.realizes_fourier_tv _ (wholeSpace_admissible d)
    (zeroCurve_piecewiseC1 d) (wholeSpace_admissible d) hreal hreal'' q' ξ ν ν' hν hν'

end HypoellipticAleksandrov.KineticAleksandrov.Scaling
