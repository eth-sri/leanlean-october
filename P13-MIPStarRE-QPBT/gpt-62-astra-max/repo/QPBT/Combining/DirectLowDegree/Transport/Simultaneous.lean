module

public import MIPStarRE.LDT.Preliminaries.PolynomialAgreement
public import MIPStarRE.LDT.Test.MainTheorem.MainFormal
public import QPBT.Combining.DirectLowDegree.Transport.Consistency.Defect
public import QPBT.Combining.DirectLowDegree.Transport.PassConversion
public import QPBT.Combining.ActualErrorBounds
public import MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.CascadeBounds.SigmaZeta1
public import MIPStarRE.LDT.Test.MainTheorem.SourceScalars
public import MIPStarRE.LDT.Preliminaries.DistanceBounds
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
    (g g' : PolyIndex D.m (DirectScalarQ D) D.d) (hneq : g ≠ g') :
    avgOver (uniformDistribution (DirectPoint D))
        (fun u => if MvPolynomial.eval u g.1 = MvPolynomial.eval u g'.1 then
          (1 : Error) else 0) ≤
      (D.m * D.d : Error) / D.q := by
  letI := D.toLDTFieldModel
  let gLdt := directPolyEquivPolynomial D g
  let g'Ldt := directPolyEquivPolynomial D g'
  calc
    _ =
      avgOver (uniformDistribution (DirectPoint D))
        (fun u => if gLdt (directPointEquiv D u) =
          g'Ldt (directPointEquiv D u) then (1 : Error) else 0) := by
            apply avgOver_congr
            intro u
            simp only [gLdt, g'Ldt, directPolyEquivPolynomial_apply]
            exact if_congr
              ((directScalarEquiv D).injective.eq_iff.symm) rfl rfl
    _ = _ := by
      simpa using
        (avgOver_uniform_equiv (directPointEquiv D)
          (fun u : DirectPoint D =>
            if gLdt (directPointEquiv D u) =
              g'Ldt (directPointEquiv D u) then 1 else 0))
    _ ≤ _ :=
      polynomialAgreement_avg_le_mdq D.toLDTParameters gLdt g'Ldt (by
        intro heq
        exact hneq ((directPolyEquivPolynomial D).injective heq))

/-! ## Coordinatewise low individual degree soundness -/

/-! ## One-coordinate tuples -/

/-- The effect of a tuple-relabeled measurement at a constant tuple over a
one-element index set is the effect of the relabeling by the unique
coordinate. -/
private theorem postprocess_effect_const_tuple
    {alpha beta iota d : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] [Fintype iota] [DecidableEq iota]
    [Unique iota] [Fintype d] [DecidableEq d]
    (M : Quantum.Measurement alpha d) (f : alpha → iota → beta) (b : beta) :
    (M.postprocess f).effect (fun _ => b) =
      (M.postprocess (fun a => f a default)).effect b := by
  exact Finset.sum_congr
    (Finset.filter_congr fun a _ => (funext_iff.trans Unique.forall_iff))
    (fun _ _ => rfl)

/-- Reading a measurement as a one-coordinate tuple measurement does not
change its effects. -/
private theorem postprocess_const_tuple_effect_self
    {alpha iota d : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype iota] [DecidableEq iota] [Unique iota] [Fintype d] [DecidableEq d]
    (M : Quantum.Measurement alpha d) (p : alpha) :
    (M.postprocess (fun a (_ : iota) => a)).effect (fun _ => p) = M.effect p := by
  rw [postprocess_effect_const_tuple]
  simp only [Quantum.Measurement.postprocess_effect, Finset.filter_eq',
    Finset.mem_univ, if_true, Finset.sum_singleton]

variable (D : DirectLdParams) (hk : D.k = 1) (S : Strategy (directLdGame D))
  (hS : S.IsProjective)

include hk in
/-- Transport one-coordinate polynomial measurements to singleton tuples
without changing any of the three consistency bounds. -/
private theorem direct_coordinate_measurements_to_tuple_of_k_eq_one (r : Fin D.k) (bound : ℝ)
    (hcoord :
      letI := D.toLDTFieldModel
      ∃ GA₀ : ProjMeas (Polynomial D.toLDTParameters) S.ιA,
        ∃ GB₀ : ProjMeas (Polynomial D.toLDTParameters) S.ιB,
          ConsRel (directCoordinateProjStrat S hS r).state
              (uniformDistribution (Point D.toLDTParameters))
              (IdxProjMeas.toIdxSubMeas
                (directCoordinateProjStrat S hS r).pointMeasurementA)
              (polynomialEvaluationFamily D.toLDTParameters GB₀.toSubMeas) bound ∧
            ConsRel (directCoordinateProjStrat S hS r).state
              (uniformDistribution (Point D.toLDTParameters))
              (polynomialEvaluationFamily D.toLDTParameters GA₀.toSubMeas)
              (IdxProjMeas.toIdxSubMeas
                (directCoordinateProjStrat S hS r).pointMeasurementB) bound ∧
            ConsRel (directCoordinateProjStrat S hS r).state
              (uniformDistribution Unit)
              (constSubMeasFamily GA₀.toSubMeas)
              (constSubMeasFamily GB₀.toSubMeas) bound) :
    ∃ GA : DirectPolyMeasTuple D S.ιA,
      ∃ GB : DirectPolyMeasTuple D S.ιB,
        bipartiteDefect
            (uniformDistribution (DirectPoint D))
            (fun u => (S.A (directLdPointQuestionOf D u)).postprocess
            (directLdPointValuesOrZero D))
            (fun u => GB.postprocess (evalDirectPolyTupleAt u))
            S.ψ ≤ bound ∧
        bipartiteDefect
            (uniformDistribution (DirectPoint D))
            (fun u => GA.postprocess (evalDirectPolyTupleAt u))
            (fun u => (S.B (directLdPointQuestionOf D u)).postprocess
            (directLdPointValuesOrZero D))
            S.ψ ≤ bound ∧
        bipartiteDefect (uniformDistribution Unit)
            (fun _ => GA)
            (fun _ => GB) S.ψ ≤ bound := by
  letI := D.toLDTFieldModel
  haveI hU : Unique (Fin D.k) :=
    { default := ⟨0, by omega⟩
      uniq := fun i => Fin.ext (by have := i.isLt; omega) }
  have hr : r = default := Subsingleton.elim _ _
  subst r
  obtain ⟨GA₀, GB₀, h1, h2, h3⟩ := hcoord
  refine ⟨(directPolynomialMeasurement GA₀).postprocess (fun g _ => g),
    (directPolynomialMeasurement GB₀).postprocess (fun g _ => g), ?_, ?_, ?_⟩
  · refine ((consistencyDefect_outcome_equiv _
      (Equiv.funUnique (Fin D.k) (DirectScalarQ D)).symm _ _ S.ψ).symm.trans
      (consistencyDefect_congr _ _ _ _ _ S.ψ ?_ ?_)).trans_le (directPointPolynomial_consistencyDefect_le D S hS default GB₀ _ h1)
    · intro u a
      change heteroKron (((S.A (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).effect (fun _ => a)) 1 = _
      rw [postprocess_effect_const_tuple]
      rfl
    · intro u a
      change heteroKron 1 ((((directPolynomialMeasurement GB₀).postprocess
        (fun g _ => g)).postprocess (evalDirectPolyTupleAt u)).effect
          (fun _ => a)) = _
      rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
        postprocess_effect_const_tuple]
      rfl
  · refine ((consistencyDefect_outcome_equiv _
      (Equiv.funUnique (Fin D.k) (DirectScalarQ D)).symm _ _ S.ψ).symm.trans
      (consistencyDefect_congr _ _ _ _ _ S.ψ ?_ ?_)).trans_le (directPolynomialPoint_consistencyDefect_le D S hS default GA₀ _ h2)
    · intro u a
      change heteroKron ((((directPolynomialMeasurement GA₀).postprocess
        (fun g _ => g)).postprocess (evalDirectPolyTupleAt u)).effect
          (fun _ => a)) 1 = _
      rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
        postprocess_effect_const_tuple]
      rfl
    · intro u a
      change heteroKron 1 (((S.B (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).effect (fun _ => a)) = _
      rw [postprocess_effect_const_tuple]
      rfl
  · refine ((consistencyDefect_outcome_equiv _
      (Equiv.funUnique (Fin D.k) (PolyIndex D.m (DirectScalarQ D) D.d)).symm _ _
        S.ψ).symm.trans
      (consistencyDefect_congr _ _ _ _ _ S.ψ ?_ ?_)).trans_le (directPolynomialPolynomial_consistencyDefect_le D S GA₀ GB₀ _ h3)
    · intro _ p
      change heteroKron (((directPolynomialMeasurement GA₀).postprocess
        (fun g _ => g)).effect (fun _ => p)) 1 = _
      rw [postprocess_const_tuple_effect_self]
    · intro _ p
      change heteroKron 1 (((directPolynomialMeasurement GB₀).postprocess
        (fun g _ => g)).effect (fun _ => p)) = _
      rw [postprocess_const_tuple_effect_self]

include hS hk in
/-- The polynomial-tuple conclusion of `lem:ld-soundness` for simultaneity
parameter `1`: the coordinate conclusions of the low individual degree
theorem, read as one-coordinate tuples.

The three consistency defects carry the error of `thm:main-formal` at the
auxiliary parameter `directLdAuxParameter D` and pass bound `3 ε`; its
absorption into the error function `deltaLd` is
`exists_directLdTransportConstants`.  For simultaneity parameter at least `2`
the coordinate conclusions do not determine simultaneous polynomial
measurements; see the module docstring and
`docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`.  Blueprint
`lem:ld-soundness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem exists_directSimultaneousPolynomialMeasurements_of_k_eq_one (ε : Error) (hwin : 1 - ε ≤ S.value) :
    ∃ GA : DirectPolyMeasTuple D S.ιA,
      ∃ GB : DirectPolyMeasTuple D S.ιB,
        bipartiteDefect
            (uniformDistribution (DirectPoint D))
            (fun u => (S.A (directLdPointQuestionOf D u)).postprocess
            (directLdPointValuesOrZero D))
            (fun u => GB.postprocess (evalDirectPolyTupleAt u))
            S.ψ ≤
          Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) ∧
        bipartiteDefect
            (uniformDistribution (DirectPoint D))
            (fun u => GA.postprocess (evalDirectPolyTupleAt u))
            (fun u => (S.B (directLdPointQuestionOf D u)).postprocess
            (directLdPointValuesOrZero D))
            S.ψ ≤
          Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) ∧
        bipartiteDefect (uniformDistribution Unit)
            (fun _ => GA)
            (fun _ => GB)
            S.ψ ≤
          Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) := by
  apply direct_coordinate_measurements_to_tuple_of_k_eq_one <;> try assumption
  letI := D.toLDTFieldModel
  letI := D.toLDTFieldModel
  exact Test.mainFormal D.toLDTParameters
    (directCoordinateProjStrat S hS ⟨0, D.hk⟩) (3 * ε)
    (directCoordinate_passes D S hS _ ε hwin).soundnessHypothesis
    (directLdAuxParameter D) ((Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) (Nat.le_self_pow (by norm_num) D.m)) le_rfl))
    ((by
       have hm := D.hm
       exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos hm 3)) D.hd))

end

end MIPStarRE.QPBT
