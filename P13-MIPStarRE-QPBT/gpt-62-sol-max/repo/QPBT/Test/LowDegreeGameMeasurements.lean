module

public import QPBT.Games.Consistency
public import QPBT.Games.DistributionMarginals
public import QPBT.Games.StrategyClasses
public import QPBT.Games.TypedCondLinear
public import QPBT.Observables.LineDefs
public import QPBT.Test.LowDegreeGame

/-!
# Low-degree sampling and polynomial measurements

The low-degree question laws have uniform point and coordinate-index marginals,
and every sampled line is incident to its paired point.  Polynomial outcomes
are bounded multivariate polynomials. The soundness theorem using these
definitions is proved in `LowDegreeGameTheorems`.

## References

The principal definition and theorem are blueprint `def:ld-meas` and
`lem:ld-soundness`. Their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287,392-480`.
The dimension-divisibility hypothesis is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-!
### Formalization-only auxiliary facts about the ambient low-degree space
-/

/-- Formalization-only auxiliary equivalence splitting an ambient low-degree
vector into its point, seed, and direction blocks. -/
def ldSpaceSplit (L : LdParams) :
    LdSpace L ≃ ((LdPoint L) × ScalarQ L) × (LdPoint L) where
  toFun z := ((LdSpace.point z, LdSpace.seed z), LdSpace.direction z)
  invFun p := fun i =>
    match i with
    | .inl (.inl j) => p.1.1 j
    | .inl (.inr _) => p.1.2
    | .inr j => p.2 j
  left_inv z := by
    funext i
    rcases i with (j | u) | j
    · rfl
    · rfl
    · rfl
  right_inv p := by rfl

/-- The joint point and seed block of a uniform ambient vector is uniform. -/
private theorem uniformDistribution_map_pointSeed (L : LdParams) :
    (uniformDistribution (LdSpace L)).map (fun z => (z.point, z.seed)) =
      uniformDistribution ((LdPoint L) × ScalarQ L) := by
  simpa only [Distribution.map_map, uniformDistribution_map_fst] using!
    congrArg (fun μ => μ.map Prod.fst) (uniformDistribution_map_equiv (ldSpaceSplit L))

/-- The point block of a uniform ambient vector is uniform. -/
private theorem map_uniformDistribution_point (L : LdParams) :
    (uniformDistribution (LdSpace L)).map LdSpace.point =
      uniformDistribution (LdPoint L) := by
  simpa only [Distribution.map_map, uniformDistribution_map_fst] using!
    congrArg (fun μ => μ.map Prod.fst) (uniformDistribution_map_pointSeed L)

/-- The point marginal of either line-point law is uniform. -/
theorem lineKindPointDist_point_marginal_uniform (L : LdParams) (k : LineKind) :
    (lineKindPointDist L k).map Prod.snd = uniformDistribution (LdPoint L) := by
  rw [lineKindPointDist, Distribution.map_map]
  exact map_uniformDistribution_point L

/-- Bounded multivariate polynomials form a finite set over a finite coefficient
semiring. This is the finite outcome set required by blueprint
`def:ld-meas`, paper
`08_classical_and_quantum_low_degree_tests.tex:394-408`. -/
noncomputable instance polyFuncFintype (m : ℕ) (K : Type*)
    [CommSemiring K] [Fintype K] (d : ℕ) : Fintype ↥(polyFunc m K d) := by
  letI : Finite ↥(polyFunc m K d) := Module.finite_of_finite K
  exact Fintype.ofFinite _

/-- A bounded multivariate polynomial outcome over an arbitrary finite
coefficient semiring. -/
noncomputable abbrev PolyIndex (m : ℕ) (K : Type*) [CommSemiring K]
    [Fintype K] (d : ℕ) := ↥(polyFunc m K d)

/-- A POVM indexed by one bounded multivariate polynomial. -/
noncomputable abbrev PolyMeas (m : ℕ) (K : Type*) [CommSemiring K]
    [Fintype K] [DecidableEq K] (d : ℕ) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  MIPStarRE.Quantum.Measurement (PolyIndex m K d) ι

/-- The dependent family in `def:ld-meas`: component `i` may
have its own coefficient field, number of variables, and degree bound.
Blueprint `def:ld-meas`, paper
`08_classical_and_quantum_low_degree_tests.tex:394-408`. -/
noncomputable abbrev PolyMeasFamily (k : ℕ) (K : Fin k → Type*)
    [∀ i, CommSemiring (K i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (K i)] (m d : Fin k → ℕ) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  MIPStarRE.Quantum.Measurement ((i : Fin k) → PolyIndex (m i) (K i) (d i)) ι

/-- A simultaneous tuple of `L.k` bounded polynomial representatives. -/
noncomputable abbrev PolyTuple (L : LdParams) :=
  Fin L.k → PolyIndex L.m (ScalarQ L) L.d

/-- The constant-family specialization used by `lem:ld-soundness`. -/
noncomputable abbrev PolyMeasTuple (L : LdParams) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  PolyMeasFamily L.k (fun _ => ScalarQ L) (fun _ => L.m) (fun _ => L.d) ι

/-- Evaluate every component of a polynomial tuple at a point. -/
def evalPolyTupleAt {L : LdParams} (u : LdPoint L)
    (g : PolyTuple L) : Fin L.k → ScalarQ L :=
  fun j => MvPolynomial.eval u (g j).1

/-- Embed a geometric point into the ambient coefficient space used by a
point question. -/
def pointSpaceOf (L : LdParams) (u : LdPoint L) : LdSpace L :=
  fun i => match i with
  | .inl (.inl j) => u j
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The typed low-degree point question associated with `u`. -/
def ldPointQuestionOf (L : LdParams) (u : LdPoint L) : LdQuestion L :=
  (.point, pointSpaceOf L u)

/-- Read the point component of a low-degree answer, sending answers of the
wrong form to the fixed zero tuple. This total relabeling turns the strategy's
answer measurement into the point POVM used by `lem:ld-soundness`. -/
def ldPointValuesOrZero (L : LdParams) : LdAnswer L → Fin L.k → ScalarQ L
  | .pointVals values => values
  | .alinePolys _ => 0
  | .dlinePolys _ => 0

/-- Evaluate the point-answer measurement, completing answers of the wrong form by zero. -/
noncomputable abbrev ldPointReadout {L : LdParams} {I : Type*} [Fintype I] [DecidableEq I]
    (M : LdQuestion L → MIPStarRE.Quantum.Measurement (LdAnswer L) I) (u : LdPoint L) :=
  (M (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)

/-- The quantitative error function in `lem:ld-soundness`.  Its argument order
is `(a, b, ε, q, m, d, k)`. -/
noncomputable def deltaLd (a b ε : ℝ) (q m d k : ℕ) : ℝ :=
  a * Real.rpow (((d * m * k : ℕ) : ℝ)) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

end

end MIPStarRE.QPBT
