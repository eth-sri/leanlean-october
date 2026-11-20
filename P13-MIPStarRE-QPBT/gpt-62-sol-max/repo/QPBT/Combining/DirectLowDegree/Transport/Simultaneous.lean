module

public import MIPStarRE.LDT.Preliminaries.PolynomialAgreement
public import MIPStarRE.LDT.Test.MainTheorem.MainFormal
public import QPBT.Combining.DirectLowDegree.Transport.Consistency.Defect
public import QPBT.Combining.DirectLowDegree.Transport.Error
public import QPBT.Combining.DirectLowDegree.Transport.PassConversion
public import QPBT.Combining.ActualErrorBounds
public import QPBT.Combining.ErrorBounds
public import QPBT.Combining.PassingError
public import QPBT.ExplicitConstants
public import QPBT.Games.Sandwich.Pasting.Heterogeneous
public import MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.CascadeBounds.SigmaZeta1
public import MIPStarRE.LDT.Test.MainTheorem.SourceScalars
public import QPBT.Upstream
public import MIPStarRE.LDT.Preliminaries.DistanceBounds
public import MIPStarRE.LDT.Preliminaries.Triangles.Core
public import MIPStarRE.LDT.Test.MainTheorem.SourceRoleRegister.Final

/-!
# Simultaneous polynomial measurements for the direct low-degree game

This module applies the quantum soundness theorem of the low individual
degree test to each coordinate of a projective strategy for the directly
indexed low-degree game, transports the Schwartz--Zippel collision estimate
to the direct polynomial representatives, and, for simultaneity parameter
`1`, obtains the polynomial-tuple conclusion of `lem:ld-soundness` from the
coordinate conclusions.

## The simultaneity obstruction

For simultaneity parameter `k ≥ 2` the coordinate conclusions alone do not
determine simultaneous polynomial measurements, so no palindromic combination
of the coordinate measurements can be consistent with a joint point
measurement in general.  Let `q = 2^s`, let the degree be `1`, and let Bob
measure the univariate polynomials `g = g₀ + g₁ x` once in the standard basis
`|g⟩` and once in the Fourier basis attached to the symmetric pairing
`⟨h, g⟩ = h₀ g₁ + h₁ g₀`.  In characteristic two every evaluation functional
`h ↦ h(u)` is represented by an isotropic vector of this pairing, so at every
point `u` the value-level coarse-grainings `Q^{1,u}_{[a]}` (Fourier basis) and
`Q^{2,u}_{[b]}` (standard basis) commute, and on the maximally entangled state
Alice may answer point questions with the joint projective measurement
`P^u_{a,b} = (Q^{1,u}_{[a]} Q^{2,u}_{[b]})ᵀ`.  All coordinate consistencies of
`lem:ld-soundness` then hold with defect `0` and distinct polynomials collide
at a uniform point with probability `1 / q`, but the sandwiched POVM has
`∑_{g₂(u) = b} |g₂⟩⟨g₂| Q^{1,u}_{[a]} |g₂⟩⟨g₂| = q⁻¹ Q^{2,u}_{[b]}`, whose
consistency defect against `P^u` is `1 - 1/q`; more strongly, every
polynomial-pair POVM on Bob's side has defect at least `1 - 2/q` against
`P^u`.  No bound of the form `C k √(δ + m d / q)` holds for a universal `C`.
The source obtains the general case not coordinatewise but by the combining
reduction of Theorem 4.43 in the NEEXP paper, which applies the `k = 1`
theorem once, in dimension `m + k`, to a combined strategy; that reduction is
not formalized here.  The two-measurement pasting estimate (Fact 4.35 there)
does not apply either, since it evaluates the two coordinates at
independently sampled points while the low-degree game evaluates all
coordinates at one point.  The counterexample and the resulting formal
status are recorded in `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`
* `references/neexp-paper/05_quantum_preliminaries.tex:912-1060` and `:1409-1503`
* `references/ldt-paper/test_definition.tex:180-202`
* `lem:ld-soundness` in `blueprint/src/chapter/ch13_qpbt_test.tex`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
* `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-! ## Direct polynomial collision estimate -/

/-- Two distinct direct polynomial representatives agree at a uniformly
sampled direct point with probability at most `m d / q`.

This is the Schwartz--Zippel estimate `polynomialAgreement_avg_le_mdq` of the
low individual degree test, read through the polynomial and point
identifications of the direct low-degree game; it is the collision
hypothesis of blueprint `lem:ld-sandwich`
(paper `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`). -/
theorem directPolynomialAgreement_avg_le_mdq (D : DirectLdParams)
    (g g' : DirectPolynomial D) (hneq : g ≠ g') :
    avgOver (uniformDistribution (DirectPoint D))
        (fun u => if MvPolynomial.eval u g.1 = MvPolynomial.eval u g'.1 then
          (1 : Error) else 0) ≤
      (D.m * D.d : Error) / D.q := by
  letI := D.toLDTFieldModel
  let gLdt := directPolyEquivPolynomial D g
  let g'Ldt := directPolyEquivPolynomial D g'
  have hneqLdt : gLdt ≠ g'Ldt := by
    intro heq
    exact hneq ((directPolyEquivPolynomial D).injective heq)
  calc
    _ =
      avgOver (uniformDistribution (DirectPoint D))
        (fun u => if gLdt (directPointEquiv D u) =
          g'Ldt (directPointEquiv D u) then (1 : Error) else 0) := by
            apply avgOver_congr
            intro u
            simp_all [gLdt, g'Ldt, directPolyEquivPolynomial_apply]
    _ = avgOver (uniformDistribution (Point D.toLDTParameters))
        (fun u : Point D.toLDTParameters =>
          if gLdt u = g'Ldt u then (1 : Error) else 0) := by
      simpa using
        (avgOver_uniform_equiv (directPointEquiv D)
          (fun u : DirectPoint D =>
            if gLdt (directPointEquiv D u) =
              g'Ldt (directPointEquiv D u) then (1 : Error) else 0))
    _ ≤ _ :=
      polynomialAgreement_avg_le_mdq D.toLDTParameters gLdt g'Ldt hneqLdt

/-- A bijective outcome readout preserves the mismatch mass. -/
private theorem bipartiteDefect_postprocess_equiv {X α β I J : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : α ≃ β) (μ : Distribution X) (A : X → Quantum.Measurement α I)
    (B : X → Quantum.Measurement α J) (ψ : EuclideanSpace ℂ (I × J)) :
    bipartiteDefect μ A B ψ =
      bipartiteDefect μ (fun x => (A x).postprocess e) (fun x => (B x).postprocess e) ψ := by
  simp only [bipartiteDefect]
  rw [← consistencyDefect_outcome_equiv μ e (fun x b => heteroKron (((A x).postprocess e).effect b) 1)
    (fun x b => heteroKron 1 (((B x).postprocess e).effect b)) ψ]
  simp only [SandwichProduct.postprocess_effect_of_injective _ _ e.injective]

private theorem postprocess_id {α I : Type*} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I] (A : Quantum.Measurement α I) : A.postprocess (fun a => a) = A :=
  Quantum.Measurement.ext fun a =>
    SandwichProduct.postprocess_effect_of_injective A id Function.injective_id a

set_option maxHeartbeats 800000 in
/-- For one coordinate, the scalar LDT soundness measurements give simultaneous
polynomial measurements by identifying a scalar with its constant tuple. -/
theorem exists_directSimultaneousPolynomialMeasurements_of_k_eq_one
    (D : DirectLdParams) (hk : D.k = 1) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (ε : Error) (hwin : 1 - ε ≤ S.value) :
    let δ := Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε)
    ∃ GA GB, DirectLdConsistency S GA GB δ δ := by
  letI := D.toLDTFieldModel
  letI : Unique (Fin D.k) := ⟨⟨⟨0, by omega⟩⟩, fun i => Fin.ext (by have := i.isLt; omega)⟩
  let r : Fin D.k := default
  obtain ⟨GA, GB, h1, h2, h3⟩ := Test.mainFormal D.toLDTParameters
    (directCoordinateProjStrat D S hS r) (3 * ε)
    (directCoordinate_passes D S hS r ε hwin).soundnessHypothesis
    (directLdAuxParameter D) (four_hundred_mul_le_directLdAuxParameter D)
    (directLdAuxParameter_pos D)
  refine ⟨(directPolynomialMeasurement D GA).postprocess (fun g _ => g),
    (directPolynomialMeasurement D GB).postprocess (fun g _ => g), ?_, ?_, ?_⟩
  · rw [bipartiteDefect_postprocess_equiv (Equiv.funUnique (Fin D.k) (DirectScalarQ D))]
    simpa only [bipartiteDefect, directLdPointReadout, Quantum.Measurement.postprocess_comp,
      Equiv.funUnique_apply, evalDirectPolyTupleAt, directPointCoordinateMeasurementA,
      directPointCoordinateMeasurementB, directPointCoordinateMeasurement,
      directPolynomialEvaluationMeasurement, r] using
      directPointPolynomial_consistencyDefect_le D S hS r GB _ h1
  · rw [bipartiteDefect_postprocess_equiv (Equiv.funUnique (Fin D.k) (DirectScalarQ D))]
    simpa only [bipartiteDefect, directLdPointReadout, Quantum.Measurement.postprocess_comp,
      Equiv.funUnique_apply, evalDirectPolyTupleAt, directPointCoordinateMeasurementA,
      directPointCoordinateMeasurementB, directPointCoordinateMeasurement,
      directPolynomialEvaluationMeasurement, r] using
      directPolynomialPoint_consistencyDefect_le D S hS r GA _ h2
  · rw [bipartiteDefect_postprocess_equiv (Equiv.funUnique (Fin D.k) (DirectPolynomial D))]
    simpa only [Quantum.Measurement.postprocess_comp, Equiv.funUnique_apply, postprocess_id] using
      directPolynomialPolynomial_consistencyDefect_le D S GA GB _ h3

end

end MIPStarRE.QPBT
