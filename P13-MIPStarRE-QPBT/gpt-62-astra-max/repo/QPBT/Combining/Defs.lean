module

public import QPBT.Test.LowDegreeGameMeasurements
public import QPBT.Test.PauliBasisTest

/-!
# Polynomial combination and restricted line distributions

This file contains the concrete definitions at the foundation of the
Chapter 15 combining argument.  A pair of bounded individual-degree
polynomials is embedded into the two coordinate blocks of an extended
polynomial.  On lines, explicit affine reparameterizations are composed with
coefficient-list polynomials.  The original-dimensional restricted line laws
are formed before decoding, while their field seed is still present.

## References

The combining map is blueprint
`def:combine-map`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`.
The restricted laws are blueprint `def:ith-restricted-line`,
with paper origin in the same source at lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

section

variable (P : AdmissibleParams) (m : ℕ)

/-- The bounded individual-degree polynomial outcome used by the global
pair measurement.  This is the actual `polyFunc` subtype from
`def:polyfunc`, not a coefficient-box replacement. -/
noncomputable abbrev Poly :=
  ↥(MIPStarRE.LDT.Preliminaries.polyFunc P.m (PauliScalar P) P.d)

/-- Pairs of bounded polynomial representatives returned by the global
measurement in `lem:qld-4-7`. -/
noncomputable abbrev PolyPair := Poly P × Poly P

/-- This equivalence decomposes the extended coordinate set into the `X` block,
    the `Z` block, and the two scalar coordinates.  It supports blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
def finCombineEquiv :
    Fin (2 * m + 2) ≃ ((Fin m ⊕ Fin m) ⊕ Fin 2) :=
  (finCongr (by omega)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl (Fin 2))))

/-- Embed an `X`-block coordinate into the extended coordinate set. -/
def embX : Fin m → Fin (2 * m + 2) :=
  fun i => (finCombineEquiv m).symm (.inl (.inl i))

/-- Embed a `Z`-block coordinate into the extended coordinate set. -/
def embZ : Fin m → Fin (2 * m + 2) :=
  fun i => (finCombineEquiv m).symm (.inl (.inr i))

/-- The extended coordinate occupied by the scalar `alpha`. -/
def alphaVar : Fin (2 * m + 2) :=
  (finCombineEquiv m).symm (.inr 0)

/-- The extended coordinate occupied by the scalar `beta`. -/
def betaVar : Fin (2 * m + 2) :=
  (finCombineEquiv m).symm (.inr 1)

end

section

variable {K : Type*} {m : ℕ} (u : Fin (2 * m + 2) → K)

/-- Project an extended point onto its `X` coordinate block. -/
def projX : Fin m → K :=
  fun i => u (embX m i)

/-- Project an extended point onto its `Z` coordinate block. -/
def projZ : Fin m → K :=
  fun i => u (embZ m i)

end

section

variable {K : Type*} [CommSemiring K] {c m : ℕ} (aX : K) {n d : ℕ} (bX : K) (hd : 1 ≤ d)
  (aZ bZ uα vα uβ vβ : K) (f g : Fin (c + 1) → K)

/-- Combine two multivariate polynomials by the formula
`alpha * f(x) + beta * g(z)` from `def:combine-map`.

Blueprint `def:combine-map`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-983`. -/
noncomputable def combinePoly
    (f g : MvPolynomial (Fin m) K) : MvPolynomial (Fin (2 * m + 2)) K :=
  MvPolynomial.X (alphaVar m) * MvPolynomial.rename (embX m) f +
    MvPolynomial.X (betaVar m) * MvPolynomial.rename (embZ m) g

/-- Evaluation of `combinePoly` is the displayed combining formula. -/
theorem combinePoly_eval
    (f g : MvPolynomial (Fin m) K) (u : Fin (2 * m + 2) → K) :
    MvPolynomial.eval u (combinePoly f g) =
      u (alphaVar m) * MvPolynomial.eval (projX u) f +
        u (betaVar m) * MvPolynomial.eval (projZ u) g := by
  change _ =
    u (alphaVar m) * MvPolynomial.eval (u ∘ embX m) f +
      u (betaVar m) * MvPolynomial.eval (u ∘ embZ m) g
  simp [combinePoly, MvPolynomial.eval_rename]

include hd in
/-- A fresh variable times an injectively renamed bounded polynomial retains
the same individual-degree bound.  This is a formalization-only auxiliary for
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-983`. -/
private theorem x_mul_rename_mem_polyFunc {e : Fin m → Fin n} (he : Function.Injective e)
    {a : Fin n} (ha : ∀ i, e i ≠ a) {p : MvPolynomial (Fin m) K}
    (hp : p ∈ polyFunc m K d) :
    MvPolynomial.X a * MvPolynomial.rename e p ∈ polyFunc n K d := by
  classical
  have hrenOutside {j : Fin n} (hj : j ∉ Set.range e) :
      (MvPolynomial.rename e p).degreeOf j = 0 := by
    apply Nat.le_zero.mp
    rw [MvPolynomial.degreeOf_le_iff]
    intro s hs
    rw [MvPolynomial.support_rename_of_injective he] at hs
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
    simp [Finsupp.mapDomain_notin_range _ _ hj]
  have hrenAll (j : Fin n) : (MvPolynomial.rename e p).degreeOf j ≤ d := by
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      rw [MvPolynomial.degreeOf_rename_of_injective he]
      exact degreeOf_le_of_mem_polyFunc hp i
    · simp [hrenOutside hj]
  have haRange : a ∉ Set.range e := by
    rintro ⟨i, hi⟩
    exact ha i hi
  refine (MvPolynomial.mem_restrictDegree _ _ _).mpr ?_
  intro s hs j
  refine MvPolynomial.degreeOf_le_iff.mp ?_ s hs
  by_cases hj : j = a
  · subst j
    rw [mul_comm]
    exact (MvPolynomial.degreeOf_mul_X_self a _).trans (by
      rw [hrenOutside haRange]
      omega)
  · rw [mul_comm, MvPolynomial.degreeOf_mul_X_of_ne _ hj]
    exact hrenAll j

include hd in
/-- The combining polynomial has individual degree at most `d` when
`hd : 1 ≤ d`.  The coordinate blocks are disjoint: `f` depends only on the
`x` variables and `g` only on the `z` variables, so multiplication by `alpha`
or `beta` preserves the degree bound on those old coordinates and gives degree
one only in the corresponding fresh coordinate.  Thus `hd` supplies exactly
the needed bound on the two fresh coordinates; no `d + 1` bound is introduced.
The statement is the well-definedness assertion in
blueprint
`def:combine-map`, with source context
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-983` and the
boundary-hypothesis discussion in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/
theorem combinePoly_mem_polyFunc {f g : MvPolynomial (Fin m) K}
    (hf : f ∈ polyFunc m K d) (hg : g ∈ polyFunc m K d) :
    combinePoly f g ∈ polyFunc (2 * m + 2) K d := by
  have hsymm :=
    (finCombineEquiv m).symm.injective
  have hX : Function.Injective (embX m) := by
    intro i j hij
    simpa using hsymm hij
  have hZ : Function.Injective (embZ m) := by
    intro i j hij
    simpa using hsymm hij
  have haZ : ∀ i, embZ m i ≠ betaVar m := by
    intro i hi
    simpa using hsymm hi
  refine Submodule.add_mem _ (x_mul_rename_mem_polyFunc hd hX ?_ hf)
    (x_mul_rename_mem_polyFunc hd hZ haZ hg)
  intro i hi
  simpa using hsymm hi

/-- Evaluate one member of a global polynomial pair at a point, selecting the
component by Pauli basis.  This is formalization-only support for
`lem:qld-4-7`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274`. -/
def evalAt {P : AdmissibleParams} (W : PauliKind)
    (u : PauliPoint P) (pair : PolyPair P) : PauliScalar P :=
  match W with
  | .X => MvPolynomial.eval u pair.1.1
  | .Z => MvPolynomial.eval u pair.2.1

/-- The univariate polynomial before coefficient extraction in
`combineLinePoly`.  The four first scalars describe the affine parameters on
the two projected lines; the last four are the affine `alpha` and `beta`
coordinates of the extended line. -/
noncomputable def combineLinePolynomial : Polynomial K :=
  (Polynomial.C uα + Polynomial.C vα * Polynomial.X) *
      (linePolynomialOfCoefficients f).comp
        (Polynomial.C aX + Polynomial.C bX * Polynomial.X) +
    (Polynomial.C uβ + Polynomial.C vβ * Polynomial.X) *
      (linePolynomialOfCoefficients g).comp
        (Polynomial.C aZ + Polynomial.C bZ * Polynomial.X)

/-- The polynomial underlying `combineLinePoly` has degree at most `c + 1`.
This is the degree assertion accompanying Equation `eq:combine-lines` in
blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:984-989`. -/
theorem combineLinePolynomial_natDegree_le :
    (combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).natDegree ≤ c + 1 := by
  have affineDegree : ∀ u v : K,
      (Polynomial.C u + Polynomial.C v * Polynomial.X).natDegree ≤ 1 := by
    intro u v
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · apply Polynomial.natDegree_mul_le.trans
      simpa using Polynomial.natDegree_X_le
  have summandDegree : ∀ (a b u v : K) (h : Fin (c + 1) → K),
      ((Polynomial.C u + Polynomial.C v * Polynomial.X) *
        (linePolynomialOfCoefficients h).comp
          (Polynomial.C a + Polynomial.C b * Polynomial.X)).natDegree ≤ c + 1 := by
    intro a b u v h
    apply Polynomial.natDegree_mul_le.trans
    have hfactor := affineDegree u v
    have hcomp : ((linePolynomialOfCoefficients h).comp
        (Polynomial.C a + Polynomial.C b * Polynomial.X)).natDegree ≤ c := by
      apply Polynomial.natDegree_comp_le.trans
      calc
        _ ≤ c * 1 :=
          Nat.mul_le_mul (linePolynomialOfCoefficients_natDegree_le h) (affineDegree a b)
        _ = c := by ring
    omega
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (summandDegree aX bX uα vα f) (summandDegree aZ bZ uβ vβ g))

/-- Combine two degree-`c` line polynomials using explicit affine
reparameterizations.  Coefficients through degree `c + 1` are extracted from
the genuine composed polynomial, so the definition has no incompatibility
fallback.

This is Equation `eq:combine-lines` in blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:984-989`. -/
noncomputable def combineLinePoly : Fin (c + 1 + 1) → K :=
  fun i => (combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).coeff i.val

end

variable {K : Type*} (L : LdParams) [Field K] (i : Fin L.m) {m c : ℕ}
  (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K) (aX bX aZ bZ uα vα uβ vβ : K)

/-- Compatibility of an extended line with two projected lines and their
explicit affine parameters. These data witness the projection-inclusion
condition preceding Equation `eq:combine-lines`. The theorem
`exists_isCombineLineCompatible_of_projection_mem` in `Combining/LinePolynomial.lean`
constructs them from that condition, including zero directions. Compatibility
alone does not make every coefficient answer a function on a singleton line;
see issue Dengnifer/MIPStarRE-QPBT-bak#695. -/
def IsCombineLineCompatible : Prop :=
  u (alphaVar m) = uα ∧ v (alphaVar m) = vα ∧
    u (betaVar m) = uβ ∧ v (betaVar m) = vβ ∧
    ∀ t : K,
      projX (u + t • v) = uX + (aX + bX * t) • vX ∧
        projZ (u + t • v) = uZ + (aZ + bZ * t) • vZ

/-- Under explicit line compatibility, `combineLinePoly` satisfies the
advertised line equation and the two projected points have the stated affine
parameters.  This is the specification obligation for Equation
blueprint
`eq:combine-lines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:984-989`. -/
theorem combineLinePoly_spec (f g : Fin (c + 1) → K)
    (hcompat : IsCombineLineCompatible u v uX vX uZ vZ
      aX bX aZ bZ uα vα uβ vβ) :
    ∀ t : K,
      projX (u + t • v) = uX + (aX + bX * t) • vX ∧
      projZ (u + t • v) = uZ + (aZ + bZ * t) • vZ ∧
      evalCoefficient
          (combineLinePoly aX bX aZ bZ uα vα uβ vβ f g) t =
        (uα + t * vα) * evalCoefficient f (aX + bX * t) +
          (uβ + t * vβ) * evalCoefficient g (aZ + bZ * t) := by
  intro t
  obtain ⟨-, -, -, -, hlines⟩ := hcompat
  refine ⟨(hlines t).1, (hlines t).2, ?_⟩
  have hdeg := combineLinePolynomial_natDegree_le aX bX aZ bZ uα vα uβ vβ f g
  have heval :
      evalCoefficient (combineLinePoly aX bX aZ bZ uα vα uβ vβ f g) t =
        (combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).eval t := by
    rw [Polynomial.eval_eq_sum_range' (n := c + 1 + 1) (by omega) t]
    exact Fin.sum_univ_eq_sum_range
      (fun k =>
        (combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).coeff k * t ^ k)
      _
  rw [heval, combineLinePolynomial]
  simp [linePolynomialOfCoefficients_eval]
  ring

/-- The seed event defining the `i`-th original-dimensional restricted line
law.  It is applied before the `LineDesc` decoder, since a geometric line does
not determine the retained seed. -/
def restrictedLineSeedEvent
    (sample : LdSpace L × LdSpace L) : Prop :=
  chiIndex L sample.1.seed = i

/-- Decidability of the pre-decoding seed event. -/
instance restrictedLineSeedEvent_decidablePred :
    DecidablePred (restrictedLineSeedEvent L i) := by
  intro sample
  unfold restrictedLineSeedEvent
  infer_instance

/-- Formalization-only auxiliary for `def:ith-restricted-line`: whenever a line
CL map keeps the shared scalar coordinate, the pre-decoding law it generates
against the point map gives positive mass to every coordinate-index event.  The
witness is the constant seed reconstructed from the index by
`seedOfIndexResidue`. -/
private theorem clDistribution_seedEvent_positive
    (CL : LdSpace L → LdSpace L)
    (hseed : ∀ z : LdSpace L, (CL z).seed = z.seed) :
    0 < ∑ sample ∈
        (clDistribution CL (ldPointCL L)).support.filter
          (restrictedLineSeedEvent L i),
      (clDistribution CL (ldPointCL L)).weight sample := by
  set s0 : ScalarQ L := seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩ with hs0
  set z0 : LdSpace L := fun _ => s0 with hz0
  refine Finset.sum_pos'
    (fun a _ => (clDistribution CL (ldPointCL L)).nonnegative a)
    ⟨(CL z0, ldPointCL L z0), Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · refine Finset.mem_image.mpr ⟨z0, ?_, rfl⟩
    simp
  · change _ = i
    rw [hseed]
    apply chiIndex_seedOfIndexResidue
  · refine Finset.sum_pos'
      (fun a _ => (uniformDistribution (LdSpace L)).nonnegative a)
      ⟨z0, Finset.mem_filter.mpr ⟨?_, rfl⟩, ?_⟩
    · simp
    · simp only [uniformDistribution, Distribution.uniformOnFinset_weight,
        Finset.mem_univ, if_true]
      positivity

/-- The axis-line seed event has positive mass.  This named obligation makes
normalization in `restrictedALinePreDist` explicit.  It belongs to
blueprint
`def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem restrictedALineSeedEvent_positive :
    0 < ∑ sample ∈
        (clDistribution (ldALineCL L) (ldPointCL L)).support.filter
          (restrictedLineSeedEvent L i),
      (clDistribution (ldALineCL L) (ldPointCL L)).weight sample :=
  clDistribution_seedEvent_positive L i _ fun _ => rfl

/-- The diagonal-line seed event has positive mass.  This is the corresponding
normalization obligation from blueprint `def:ith-restricted-line`; paper lines
1038--1048. -/
theorem restrictedDLineSeedEvent_positive :
    0 < ∑ sample ∈
        (clDistribution (ldDLineCL L) (ldPointCL L)).support.filter
          (restrictedLineSeedEvent L i),
      (clDistribution (ldDLineCL L) (ldPointCL L)).weight sample :=
  clDistribution_seedEvent_positive L i _ fun _ => rfl

/-- The normalized pre-decoding axis law conditioned on coordinate `i`. -/
noncomputable def restrictedALinePreDist :
    Distribution (LdSpace L × LdSpace L) :=
  Distribution.restrict
    (clDistribution (ldALineCL L) (ldPointCL L))
    (restrictedLineSeedEvent L i)
    (restrictedALineSeedEvent_positive L i)

/-- The normalized pre-decoding diagonal law conditioned on coordinate `i`. -/
noncomputable def restrictedDLinePreDist :
    Distribution (LdSpace L × LdSpace L) :=
  Distribution.restrict
    (clDistribution (ldDLineCL L) (ldPointCL L))
    (restrictedLineSeedEvent L i)
    (restrictedDLineSeedEvent_positive L i)

/-- The `i`-th restricted refined axis-line distribution of blueprint
`def:ith-restricted-line`.  Restriction precedes decoding so the seed fiber is
represented faithfully.

**Formalization-only auxiliary:** the blueprint node is stated over the
refined, seed-bearing axis law, so this is an auxiliary restriction of that
refined law and not a formalization of a source distribution.  The paper
prose at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`
describes the source restriction; identifying this law's push-forward with it
remains an open obligation recorded in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, section
`sec:auxiliary-subline-scalars`. -/
noncomputable def restrictedALineDist :
    Distribution (LineDesc L × (LdPoint L)) :=
  (restrictedALinePreDist L i).map fun sample =>
    (aLineDescOf sample.1, sample.2.point)

/-- The `i`-th restricted refined diagonal-line distribution of blueprint
`def:ith-restricted-line`.  The decoded direction already has all coordinates
preceding `i` set to zero.

**Formalization-only auxiliary:** as for `restrictedALineDist`, the blueprint
node is stated over the refined, seed-bearing diagonal law.  The paper prose
at `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`
describes the source restriction; identifying this law's push-forward with it
remains an open obligation recorded in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, section
`sec:auxiliary-subline-scalars`. -/
noncomputable def restrictedDLineDist :
    Distribution (LineDesc L × (LdPoint L)) :=
  (restrictedDLinePreDist L i).map fun sample =>
    (dLineDescOf sample.1, sample.2.point)

end

end MIPStarRE.QPBT
