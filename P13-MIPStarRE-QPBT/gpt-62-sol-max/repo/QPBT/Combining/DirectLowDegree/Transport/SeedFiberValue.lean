module

public import QPBT.Combining.DirectLowDegree.Transport.Strategy
public import QPBT.Combining.DirectLowDegree.GameValue

/-!
# Value of the seed-fiber dilation

The correlated seed-fiber dilation `ldStrategyToDirect` reads a strategy for
the seed-indexed low-degree game as a strategy for the directly indexed game.
This module shows that the dilation preserves the value exactly.

The direct game asks the canonical questions of a common direct sample.  In
each residue block the dilated strategy asks the original strategy the seeded
canonical questions of that sample; since canonicalizing a canonical sample
changes nothing, these are the seed-indexed questions of the common sample
carrying that residue.  The Born weight of the dilation is the uniform average
of the original Born weights over the residue, the predicates agree after
parsing, and the seed-indexed sample is a direct sample together with a
uniform residue, so the two averages coincide branch by branch, including the
point/point, line/line, and wrong-form clauses and the zero-direction
convention.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, and `lem:dlnf`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- Canonicalizing the seeded embedding of a canonical direct sample gives the
canonical seeded sample of the original direct sample: the seed-indexed
question asked in a residue block of the dilation is the seed-indexed
question of the common sample carrying that residue. -/
theorem ldCL_ldSpaceOfDirectResidue_directLdMap (L : LdParams) (t : LdType)
    (sample : DirectLdSpace L.toDirectLdParams) (residue : SeedResidue L) :
    ldCL L t (ldSpaceOfDirectResidue L
        (directLdMap L.toDirectLdParams t sample) residue) =
      ldCL L t (ldSpaceOfDirectResidue L sample residue) := by
  cases t with
  | point =>
      funext idx
      rcases idx with (j | ⟨⟩) | j <;> rfl
  | aline =>
      funext idx
      rcases idx with (j | ⟨⟩) | j
      · simp only [ldCL, ldALineCL, ldSpaceOfDirectResidue_point,
          ldSpaceOfDirectResidue_seed, directLdMap, chiIndex_seedOfIndexResidue]
        exact congrFun (lineRepMap_apply_self _ _) j
      · rfl
      · rfl
  | dline =>
      funext idx
      rcases idx with (j | ⟨⟩) | j
      · simp only [ldCL, ldDLineCL, ldSpaceOfDirectResidue_point,
          ldSpaceOfDirectResidue_seed, ldSpaceOfDirectResidue_direction, directLdMap,
          chiIndex_seedOfIndexResidue]
        change lineRepMap
            (directPrefixProjection sample.index
              (directPrefixProjection sample.index sample.direction))
            (lineRepMap (directPrefixProjection sample.index sample.direction)
              sample.point) j =
          lineRepMap (directPrefixProjection sample.index sample.direction) sample.point j
        rw [directPrefixProjection_idem]
        exact congrFun (lineRepMap_apply_self _ _) j
      · rfl
      · simp only [ldCL, ldDLineCL, ldSpaceOfDirectResidue_seed,
          ldSpaceOfDirectResidue_direction, directLdMap, chiIndex_seedOfIndexResidue]
        change directPrefixProjection sample.index
            (directPrefixProjection sample.index sample.direction) j =
          directPrefixProjection sample.index sample.direction j
        rw [directPrefixProjection_idem]

section

variable (L : LdParams) (S : Strategy (ldGame L))

/-- Accepted Born mass at a fixed pair of seed-indexed questions. -/
private def ldAcceptedMass
    (x y : LdQuestion L) : ℝ :=
  ∑ a : LdAnswer L, ∑ b : LdAnswer L,
    if ldWinPredicate L x y a b then outcomeWeight S x y a b else 0

/-- Accepted Born mass at a fixed pair of direct questions. -/
private def directAcceptedMass (D : DirectLdParams) (S : Strategy (directLdGame D))
    (x y : DirectLdQuestion D) : ℝ :=
  ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
    if directLdWinPredicate D x y a b then outcomeWeight S x y a b else 0

/-- At the canonical direct questions of a common direct sample, the accepted
mass of the dilation is the uniform residue average of the accepted mass of
the original strategy at the seeded canonical questions. -/
private theorem directAcceptedMass_ldStrategyToDirect (tA tB : LdType)
    (sample : DirectLdSpace L.toDirectLdParams) :
    directAcceptedMass L.toDirectLdParams (ldStrategyToDirect L S)
        (tA, directLdMap L.toDirectLdParams tA sample)
        (tB, directLdMap L.toDirectLdParams tB sample) =
      (Fintype.card (SeedResidue L) : ℝ)⁻¹ * ∑ residue : SeedResidue L,
        ldAcceptedMass L S
          (tA, ldCL L tA (ldSpaceOfDirectResidue L sample residue))
          (tB, ldCL L tB (ldSpaceOfDirectResidue L sample residue)) := by
  classical
  let D := L.toDirectLdParams
  let qa : DirectLdQuestion D := (tA, directLdMap D tA sample)
  let qb : DirectLdQuestion D := (tB, directLdMap D tB sample)
  let e := (ldDirectAnswerEquiv L).symm
  let q (t : LdType) (r : SeedResidue L) : LdQuestion L :=
    (t, ldCL L t (ldSpaceOfDirectResidue L sample r))
  let w r a b := outcomeWeight S (q tA r) (q tB r) (e a) (e b)
  let p a b := directLdWinPredicate D qa qb a b
  have hw r a b : ldWinPredicate L (q tA r) (q tB r) (e a) (e b) = p a b := by
    simp [q, p, qa, qb, D, e, ← ldWinPredicate_parse, parseLdQuestion_ldCL_ofDirectResidue]
  have hq (t : LdType) r : seededLdQuestion L (t, directLdMap D t sample) r = q t r :=
    congrArg (t, ·) (ldCL_ldSpaceOfDirectResidue_directLdMap L t sample r)
  have hm r : ldAcceptedMass L S (q tA r) (q tB r) =
      ∑ a, ∑ b, if p a b then w r a b else 0 := by
    unfold ldAcceptedMass
    rw [← Equiv.sum_comp e]
    exact Finset.sum_congr rfl fun a _ => by rw [← Equiv.sum_comp e]; simp only [hw, w]; rfl
  have hb a b : outcomeWeight (ldStrategyToDirect L S) qa qb a b =
      (Fintype.card (SeedResidue L) : ℝ)⁻¹ * ∑ r, w r a b := by
    rw [ldStrategyToDirect_bornWeight]
    simp only [qa, qb, hq, w, e]
  change (∑ a, ∑ b, if p a b then outcomeWeight (ldStrategyToDirect L S) qa qb a b else 0) =
    (Fintype.card (SeedResidue L) : ℝ)⁻¹ * ∑ r, ldAcceptedMass L S (q tA r) (q tB r)
  simp_rw [hb, hm, Finset.mul_sum, Finset.ite_sum_zero, mul_ite, mul_zero]
  refine Eq.trans (Finset.sum_congr rfl fun a _ => Finset.sum_comm) Finset.sum_comm

/-- The correlated seed-fiber dilation preserves the value exactly: the
direct game's value of `ldStrategyToDirect L S` is the seed-indexed game's
value of `S`.  Both values are averages over the ordered type pair and the
common sample; the direct sample together with a uniform residue is the
seed-indexed sample, and the dilation realizes, in each residue block, the
original strategy at the seed-indexed questions of that sample. -/
theorem ldStrategyToDirect_value_eq :
    (ldStrategyToDirect L S).value = S.value := by
  classical
  letI := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  have hsymm : ∀ b : ((LdType × LdType) × DirectLdSpace L.toDirectLdParams) ×
      SeedResidue L,
      (ldQuestionSeedFiberEquiv L).symm b =
        (b.1.1, ldSpaceOfDirectResidue L b.1.2 b.2) :=
    fun b => rfl
  change avgOver (directLdQuestionDistribution L.toDirectLdParams)
      (fun xy => directAcceptedMass L.toDirectLdParams (ldStrategyToDirect L S) xy.1 xy.2) =
    avgOver (ldQuestionDistribution L) (fun xy => ldAcceptedMass L S xy.1 xy.2)
  unfold directLdQuestionDistribution ldQuestionDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map,
    avgOver_uniform_equiv (ldQuestionSeedFiberEquiv L)]
  simp [hsymm]
  rw [avgOver_uniform_prod (fun (src : (LdType × LdType) × DirectLdSpace L.toDirectLdParams)
      (residue : SeedResidue L) =>
      ldAcceptedMass L S
        (src.1.1, ldCL L src.1.1 (ldSpaceOfDirectResidue L src.2 residue))
        (src.1.2, ldCL L src.1.2 (ldSpaceOfDirectResidue L src.2 residue)))]
  apply avgOver_congr
  intro src
  rw [directAcceptedMass_ldStrategyToDirect, avgOver_uniform_eq_inv_card_mul_sum]

end

end

end MIPStarRE.QPBT
