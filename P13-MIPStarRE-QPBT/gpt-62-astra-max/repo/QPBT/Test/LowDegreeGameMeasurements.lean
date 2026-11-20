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
    LdSpace L ≃ ((Fin L.m → ScalarQ L) × ScalarQ L) × (Fin L.m → ScalarQ L) where
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
    · cases u
      rfl
    · rfl
  right_inv p := by
    obtain ⟨⟨a, b⟩, c⟩ := p
    rfl

/-- Formalization-only auxiliary lemma: the point block of a uniformly random
ambient vector is uniform. -/
private theorem map_uniformDistribution_point (L : LdParams) :
    (uniformDistribution (LdSpace L)).map LdSpace.point =
      uniformDistribution (Fin L.m → ScalarQ L) := by
  have hsplit : (uniformDistribution (LdSpace L)).map (ldSpaceSplit L) =
      uniformDistribution (((Fin L.m → ScalarQ L) × ScalarQ L) × (Fin L.m → ScalarQ L)) :=
    uniformDistribution_map_equiv (ldSpaceSplit L)
  calc
    (uniformDistribution (LdSpace L)).map LdSpace.point
        = (((uniformDistribution (LdSpace L)).map (ldSpaceSplit L)).map
            Prod.fst).map Prod.fst := by
          rw [Distribution.map_map, Distribution.map_map]
          rfl
    _ = ((uniformDistribution
          (((Fin L.m → ScalarQ L) × ScalarQ L) × (Fin L.m → ScalarQ L))).map
            Prod.fst).map Prod.fst := by rw [hsplit]
    _ = (uniformDistribution ((Fin L.m → ScalarQ L) × ScalarQ L)).map Prod.fst := by
          rw [uniformDistribution_map_fst]
    _ = uniformDistribution (Fin L.m → ScalarQ L) := uniformDistribution_map_fst

/-- Formalization-only auxiliary lemma: the shared scalar coordinate of a
uniformly random ambient vector is uniform. This is the seed marginal used in
the proof of `lem:alnf`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-257`,
and in blueprint `def:ith-restricted-line`. -/
theorem uniformDistribution_map_ldSeed (L : LdParams) :
    (uniformDistribution (LdSpace L)).map LdSpace.seed =
      uniformDistribution (ScalarQ L) := by
  have hsplit : (uniformDistribution (LdSpace L)).map (ldSpaceSplit L) =
      uniformDistribution (((Fin L.m → ScalarQ L) × ScalarQ L) × (Fin L.m → ScalarQ L)) :=
    uniformDistribution_map_equiv (ldSpaceSplit L)
  calc
    (uniformDistribution (LdSpace L)).map LdSpace.seed
        = (((uniformDistribution (LdSpace L)).map (ldSpaceSplit L)).map
            Prod.fst).map Prod.snd := by
          rw [Distribution.map_map, Distribution.map_map]
          rfl
    _ = ((uniformDistribution
          (((Fin L.m → ScalarQ L) × ScalarQ L) × (Fin L.m → ScalarQ L))).map
            Prod.fst).map Prod.snd := by rw [hsplit]
    _ = (uniformDistribution ((Fin L.m → ScalarQ L) × ScalarQ L)).map Prod.snd := by
          rw [uniformDistribution_map_fst]
    _ = uniformDistribution (ScalarQ L) := uniformDistribution_map_snd

/-- The coordinate index of a uniformly random scalar is uniform.  This is the
balance assertion in `def:ld-question-distribution`, blueprint
`lem:chi-index-uniform`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:215-221`.
-/
theorem uniformDistribution_map_chiIndex (L : LdParams) :
    (uniformDistribution (ScalarQ L)).map (chiIndex L) =
      uniformDistribution (Fin L.m) := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact uniformDistribution_map_fst_of_equiv
    (seedFiberEquiv L) (chiIndex L) fun s => (seedFiberEquiv_fst L s).symm

/-- `lem:alnf`: the point and axis-index marginals of the axis line-point
distribution are uniform. Blueprint `lem:alnf`, paper
`08_classical_and_quantum_low_degree_tests.tex:243-257`. -/
theorem aLinePointDist_point_marginal_uniform (L : LdParams) :
    (aLinePointDist L).map Prod.snd =
        uniformDistribution (Fin L.m → ScalarQ L) ∧
      (aLinePointDist L).map (fun sample => chiIndex L sample.1.seed) =
        uniformDistribution (Fin L.m) := by
  constructor
  · have hmap : (aLinePointDist L).map Prod.snd
        = (uniformDistribution (LdSpace L)).map LdSpace.point := by
      change ((((uniformDistribution (LdSpace L)).map
          fun z => (ldALineCL L z, ldPointCL L z)).map
          fun s => (aLineDescOf L s.1, LdSpace.point s.2)).map Prod.snd) = _
      rw [Distribution.map_map, Distribution.map_map]
      rfl
    rw [hmap, map_uniformDistribution_point]
  · have hmap : (aLinePointDist L).map (fun sample => chiIndex L sample.1.seed)
        = ((uniformDistribution (LdSpace L)).map LdSpace.seed).map (chiIndex L) := by
      change ((((uniformDistribution (LdSpace L)).map
          fun z => (ldALineCL L z, ldPointCL L z)).map
          fun s => (aLineDescOf L s.1, LdSpace.point s.2)).map
          fun sample => chiIndex L sample.1.seed) = _
      rw [Distribution.map_map, Distribution.map_map, Distribution.map_map]
      rfl
    rw [hmap, uniformDistribution_map_ldSeed, uniformDistribution_map_chiIndex]

/-- `lem:dlnf`: the point and prefix-index marginals of the diagonal
line-point distribution are uniform. Blueprint `lem:dlnf`,
paper `08_classical_and_quantum_low_degree_tests.tex:261-272`. -/
theorem dLinePointDist_point_marginal_uniform (L : LdParams) :
    (dLinePointDist L).map Prod.snd =
        uniformDistribution (Fin L.m → ScalarQ L) ∧
      (dLinePointDist L).map (fun sample => chiIndex L sample.1.seed) =
        uniformDistribution (Fin L.m) := by
  constructor
  · have hmap : (dLinePointDist L).map Prod.snd
        = (uniformDistribution (LdSpace L)).map LdSpace.point := by
      change ((((uniformDistribution (LdSpace L)).map
          fun z => (ldDLineCL L z, ldPointCL L z)).map
          fun s => (dLineDescOf L s.1, LdSpace.point s.2)).map Prod.snd) = _
      rw [Distribution.map_map, Distribution.map_map]
      rfl
    rw [hmap, map_uniformDistribution_point]
  · have hmap : (dLinePointDist L).map (fun sample => chiIndex L sample.1.seed)
        = ((uniformDistribution (LdSpace L)).map LdSpace.seed).map (chiIndex L) := by
      change ((((uniformDistribution (LdSpace L)).map
          fun z => (ldDLineCL L z, ldPointCL L z)).map
          fun s => (dLineDescOf L s.1, LdSpace.point s.2)).map
          fun sample => chiIndex L sample.1.seed) = _
      rw [Distribution.map_map, Distribution.map_map, Distribution.map_map]
      rfl
    rw [hmap, uniformDistribution_map_ldSeed, uniformDistribution_map_chiIndex]

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
def evalPolyTupleAt {L : LdParams} (u : Fin L.m → ScalarQ L)
    (g : PolyTuple L) : Fin L.k → ScalarQ L :=
  fun j => MvPolynomial.eval u (g j).1

/-- Embed a geometric point into the ambient coefficient space used by a
point question. -/
def pointSpaceOf (L : LdParams) (u : Fin L.m → ScalarQ L) : LdSpace L :=
  fun i => match i with
  | .inl (.inl j) => u j
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The typed low-degree point question associated with `u`. -/
def ldPointQuestionOf (L : LdParams) (u : Fin L.m → ScalarQ L) : LdQuestion L :=
  (.point, pointSpaceOf L u)

/-- Read the point component of a low-degree answer, sending answers of the
wrong form to the fixed zero tuple. This total relabeling turns the strategy's
answer measurement into the point POVM used by `lem:ld-soundness`. -/
def ldPointValuesOrZero (L : LdParams) : LdAnswer L → Fin L.k → ScalarQ L
  | .pointVals values => values
  | .alinePolys _ => 0
  | .dlinePolys _ => 0

/-- The quantitative error function in `lem:ld-soundness`.  Its argument order
is `(a, b, ε, q, m, d, k)`. -/
noncomputable def deltaLd (a b ε : ℝ) (q m d k : ℕ) : ℝ :=
  a * Real.rpow (((d * m * k : ℕ) : ℝ)) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

end

end MIPStarRE.QPBT
