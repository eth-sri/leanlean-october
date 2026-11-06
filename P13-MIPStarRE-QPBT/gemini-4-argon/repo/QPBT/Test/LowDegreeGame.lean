module

public import QPBT.Algebra.Coefficients
public import QPBT.Algebra.FieldBasis
public import QPBT.Algebra.Lines
public import QPBT.Games.CondLinear
public import QPBT.Games.Defs

/-!
# The low-degree game

The low-degree component of the Pauli basis test has finite question and answer
alphabets.  Its question maps act explicitly on the point, coordinate, and
direction registers of the ambient coefficient space and have recursive
conditionally linear representations of levels one, two, and three.

## References

The source-facing nodes are blueprint `def:ld-game`,
`def:ld-question-distribution`, and `def:ld-win-predicate`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
The exact decomposition of a scalar seed into its coordinate index and its
residue records the balance assertion for the map `chi` in the same source
definition.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Numerical parameters for the low-degree game.  The ambient coefficient
space uses the once-and-for-all model `fixedFieldModel P.q P.hq`, rather than a
model supplied by each parameter record.  This is the Lean carrier for
blueprint
`def:ld-game`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
structure LdParams where
  q : ℕ
  m : ℕ
  d : ℕ
  k : ℕ
  hm : 1 ≤ m
  hd : 1 ≤ d
  hk : 1 ≤ k
  hq : IsAdmissibleSize q
  hdvd : m ∣ q

/-- The positive dimension in `LdParams` supplies the finite coordinate type
used by the uniform axis and prefix-index marginals. -/
instance instNonemptyFinM (L : LdParams) : Nonempty (Fin L.m) :=
  ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one L.hm⟩⟩

/-- The fixed scalar model of a low-degree parameter tuple.  It is a
compatibility view of the global `fixedFieldModel` selector, not an
independently quantified field representation.  Blueprint `def:ld-game`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
@[reducible] noncomputable def LdParams.model (P : LdParams) : FixedFieldModel P.q :=
  fixedFieldModel P.q P.hq

/-- The scalar carrier selected by an `LdParams` record; this is the fixed
field carrier in `def:ld-game`, selected globally by `LdParams.model`.
Blueprint `def:ld-game`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
abbrev ScalarQ (P : LdParams) := (P.model).K

/-- The three low-degree question types of blueprint
`def:ld-game`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
inductive LdType where
  | point
  | aline
  | dline
  deriving DecidableEq, Repr, Inhabited
instance LdType.instFintype : Fintype LdType :=
  ⟨{.point, .aline, .dline}, by intro x; cases x <;> simp⟩
/-- The register index used by the low-degree game (blueprint
`def:ld-game`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
abbrev LdIndex (P : LdParams) := (Fin P.m ⊕ Unit) ⊕ Fin P.m

/-- The full ambient low-degree coefficient space (blueprint
`def:ld-game`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
abbrev LdSpace (P : LdParams) := LdIndex P → ScalarQ P

/-- The point coordinates of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.point {P : LdParams} (z : LdSpace P) : Fin P.m → ScalarQ P :=
  fun i => z (.inl (.inl i))

/-- The shared scalar coordinate of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.seed {P : LdParams} (z : LdSpace P) : ScalarQ P :=
  z (.inl (.inr ()) )

/-- The direction coordinates of an ambient low-degree vector in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def LdSpace.direction {P : LdParams} (z : LdSpace P) : Fin P.m → ScalarQ P :=
  fun i => z (.inr i)

/-- The zero-based coordinate index corresponding to the paper's map `χ`:
`chiIndex P s` represents `χ(s) - 1` in the fixed field representation.  This
is `eq:chi-func` in blueprint `def:ld-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def chiIndex (P : LdParams) (s : ScalarQ P) : Fin P.m := by
  letI : NeZero P.m := ⟨by
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one P.hm)⟩
  exact Fin.ofNat P.m ((binaryRepresentation P.model s).val / (P.q / P.m))

/-! ### Formalization-only coordinate-index fibers

The following decomposition supplies the equal-fiber calculation used in the
uniform coordinate-index law.
-/

/-- The common residue set in a fiber of `chiIndex` is nonempty.  This is part
of the exact seed decomposition supporting the balance assertion in
`def:ld-question-distribution`, blueprint `lem:chi-seed-fibers`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:215-221`.
-/
theorem LdParams.seedFiberCard_pos (L : LdParams) : 0 < L.q / L.m := by
  exact Nat.div_pos (Nat.le_of_dvd (by
    obtain ⟨n, hn, hq⟩ := L.hq
    rw [hq]
    exact Nat.pow_pos (by decide)) L.hdvd) L.hm

/-- Divisibility identifies the scalar cardinality with the product of the
coordinate-index cardinality and the common fiber cardinality.  This supports
`lem:chi-seed-fibers` in blueprint chapter 13. -/
theorem LdParams.seedFiberProduct_eq (L : LdParams) :
    L.q = L.m * (L.q / L.m) :=
  (Nat.mul_div_cancel' L.hdvd).symm

/-- Casting between equal finite cardinalities preserves the underlying
natural-number representative. -/
@[simp] private theorem equivCastFin_val {m n : ℕ} (h : m = n) (i : Fin m) :
    (Equiv.cast (congrArg Fin h) i).val = i.val := by
  subst n
  rfl

/-- A scalar seed is uniquely a coordinate index and a residue in its
`chiIndex` fiber.  This is the exact decomposition underlying
`lem:chi-seed-fibers` in blueprint chapter 13. -/
noncomputable def seedFiberEquiv (L : LdParams) :
    ScalarQ L ≃ Fin L.m × Fin (L.q / L.m) :=
  (binaryRepresentation L.model).trans <|
    (Equiv.cast <| congrArg Fin L.seedFiberProduct_eq).trans
      finProdFinEquiv.symm

/-- The coordinate component of the exact seed decomposition is `chiIndex`. -/
@[simp] theorem seedFiberEquiv_fst (L : LdParams) (s : ScalarQ L) :
    (seedFiberEquiv L s).1 = chiIndex L s := by
  letI : NeZero L.m := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one L.hm)⟩
  have hquot : (binaryRepresentation L.model s).val / (L.q / L.m) < L.m := by
    apply (Nat.div_lt_iff_lt_mul L.seedFiberCard_pos).mpr
    rw [Nat.mul_div_cancel' L.hdvd]
    exact (binaryRepresentation L.model s).isLt
  simp only [seedFiberEquiv, Equiv.trans_apply]
  apply Fin.ext
  change
    (Equiv.cast (congrArg Fin L.seedFiberProduct_eq)
      (binaryRepresentation L.model s)).val / (L.q / L.m) =
      (Fin.ofNat L.m ((binaryRepresentation L.model s).val / (L.q / L.m))).val
  rw [equivCastFin_val]
  · exact (Nat.mod_eq_of_lt hquot).symm
  · exact L.seedFiberProduct_eq

/-- Reconstruct the scalar seed belonging to a coordinate and its fiber
residue. -/
noncomputable def seedOfIndexResidue (L : LdParams)
    (i : Fin L.m) (r : Fin (L.q / L.m)) : ScalarQ L :=
  (seedFiberEquiv L).symm (i, r)

/-- Decomposing a reconstructed seed recovers its coordinate and residue. -/
@[simp] theorem seedFiberEquiv_seedOfIndexResidue (L : LdParams)
    (i : Fin L.m) (r : Fin (L.q / L.m)) :
    seedFiberEquiv L (seedOfIndexResidue L i r) = (i, r) :=
  (seedFiberEquiv L).apply_symm_apply (i, r)

/-- A reconstructed seed belongs to the prescribed `chiIndex` fiber. -/
@[simp] theorem chiIndex_seedOfIndexResidue (L : LdParams)
    (i : Fin L.m) (r : Fin (L.q / L.m)) :
    chiIndex L (seedOfIndexResidue L i r) = i := by
  rw [← seedFiberEquiv_fst]
  simp

/-- The projection used in the diagonal-line map zeroes coordinates before the
chosen index and retains the suffix of the direction vector.  This is the
prefix restriction in blueprint
`def:ld-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def prefixProjection {P : LdParams} (i : Fin P.m) (v : Fin P.m → ScalarQ P) :
    Fin P.m → ScalarQ P :=
  fun j => if j.val < i.val then 0 else v j

/-- Zeroing the coordinates preceding a fixed index is idempotent.  This is a
formalization-only consequence of the prefix restriction in
`def:ld-question-distribution`, recorded as `lem:prefix-projection-idempotent`
in blueprint chapter 13. -/
theorem prefixProjection_idempotent {P : LdParams} (i : Fin P.m)
    (v : Fin P.m → ScalarQ P) :
    prefixProjection i (prefixProjection i v) = prefixProjection i v := by
  funext j
  by_cases h : j.val < i.val
  · simp only [prefixProjection, if_pos h]
  · simp only [prefixProjection, if_neg h]

/-- The point CL map, retaining the point block and clearing the auxiliary
blocks.  It is the map `L_point` of blueprint
`def:ld-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def ldPointCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  fun i => match i with
  | .inl (.inl j) => z (.inl (.inl j))
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The affine-line CL map.  The direction block is put through the canonical
line representative map from `def:line-representative`, while the point block
is retained (blueprint `def:ld-question-distribution`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
noncomputable def ldALineCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  let i := chiIndex P (z.seed)
  let rep := lineRepMap (coordinateDirection i)
  fun i => match i with
  | .inl (.inl j) => (rep (z.point)) j
  | .inl (.inr _) => z (.inl (.inr ()))
  | .inr _ => 0

/-- The diagonal-line CL map applies the canonical line representative map to
the point block and stores the prefix-projected direction in the direction
block.  This is the `L_DLine` clause of
`def:ld-question-distribution` (blueprint
`def:ld-question-distribution`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
noncomputable def ldDLineCL (P : LdParams) (z : LdSpace P) : LdSpace P :=
  let i := chiIndex P (z.seed)
  let direction := prefixProjection i (z.direction)
  let rep := lineRepMap direction
  fun i => match i with
  | .inl (.inl j) => (rep (z.point)) j
  | .inl (.inr _) => z (.inl (.inr ()))
  | .inr j => direction j

/-- The conditionally linear map attached to each low-degree question type.
This is the typed construction in blueprint
`def:ld-question-distribution`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldCL (P : LdParams) : LdType → LdSpace P → LdSpace P
  | .point => ldPointCL P
  | .aline => ldALineCL P
  | .dline => ldDLineCL P

/-- The question alphabet for the low-degree game (blueprint
`def:ld-game`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
abbrev LdQuestion (P : LdParams) := LdType × LdSpace P

/-- The typed CL question distribution.  This is the inlined construction in
blueprint `def:ld-question-distribution`; paper
origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldQuestionDistribution (P : LdParams) :
    Distribution (LdQuestion P × LdQuestion P) :=
  Distribution.map
    (uniformDistribution ((LdType × LdType) × LdSpace P))
    (fun s =>
      ((s.1.1, ldCL P s.1.1 s.2), (s.1.2, ldCL P s.1.2 s.2)))

/-- The coefficient-tuple answer alphabet of the low-degree game.  Polynomial
answers are representatives with exactly the coefficient lengths printed in
the paper, as required by `def:ld-win-predicate` (blueprint
`def:ld-win-predicate`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
inductive LdAnswer (P : LdParams) where
  | pointVals (a : Fin P.k → ScalarQ P)
  | alinePolys (a : Fin P.k → Fin (P.d + 1) → ScalarQ P)
  | dlinePolys (a : Fin P.k → Fin (P.m * P.d + 1) → ScalarQ P)
  deriving DecidableEq

/-- A finite sum code used only to provide the answer alphabet's `Fintype`
instance; the public constructors are those of blueprint
`def:ld-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
abbrev LdAnswerCode (P : LdParams) :=
  (Fin P.k → ScalarQ P) ⊕
    ((Fin P.k → Fin (P.d + 1) → ScalarQ P) ⊕
      (Fin P.k → Fin (P.m * P.d + 1) → ScalarQ P))

/-- The canonical code equivalence for `LdAnswer`, sending point, axis-line,
and diagonal-line answers to the three summands (Lean-only finite-carrier
support for blueprint
`def:ld-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`).
-/
noncomputable def ldAnswerEquiv (P : LdParams) :
    LdAnswer P ≃ LdAnswerCode P where
  toFun
    | .pointVals a => .inl a
    | .alinePolys a => .inr (.inl a)
    | .dlinePolys a => .inr (.inr a)
  invFun
    | .inl a => .pointVals a
    | .inr (.inl a) => .alinePolys a
    | .inr (.inr a) => .dlinePolys a
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl a => rfl
    | inr x =>
        cases x with
        | inl a => rfl
        | inr a => rfl

noncomputable instance instFintypeLdAnswer (P : LdParams) : Fintype (LdAnswer P) :=
  Fintype.ofEquiv (LdAnswerCode P) (ldAnswerEquiv P).symm

/-- Check that an answer has the constructor prescribed by its question type;
Lean encoding of the rejection clause in blueprint
`def:ld-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def validLdAnswer {P : LdParams} (t : LdType) (a : LdAnswer P) : Bool :=
  match t, a with
  | .point, .pointVals _ => true
  | .aline, .alinePolys _ => true
  | .dline, .dlinePolys _ => true
  | _, _ => false

/-- The axis-parallel line/point relation in blueprint
`def:ld-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def alinePointCondition (P : LdParams) (line point : LdSpace P)
    (f : Fin P.k → Fin (P.d + 1) → ScalarQ P)
    (a : Fin P.k → ScalarQ P) : Prop :=
  -- Universal quantification follows the zero-direction convention in
  -- `rem:ld-win-zero-direction`.
  ∀ t : ScalarQ P,
    point.point = line.point + t • coordinateDirection (chiIndex P line.seed) →
      ∀ j : Fin P.k, evalCoefficient (f j) t = a j

/-- The diagonal line/point relation in blueprint
`def:ld-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
def dlinePointCondition (P : LdParams) (line point : LdSpace P)
    (f : Fin P.k → Fin (P.m * P.d + 1) → ScalarQ P)
    (a : Fin P.k → ScalarQ P) : Prop :=
  ∀ t : ScalarQ P,
    point.point = line.point + t • line.direction →
      ∀ j : Fin P.k, evalCoefficient (f j) t = a j

/-- The low-degree consistency predicate, rejecting answers of the wrong
constructor shape.  This is blueprint
`def:ld-win-predicate`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldWinPredicate (P : LdParams) :
    LdQuestion P → LdQuestion P → LdAnswer P → LdAnswer P → Bool :=
  open Classical in
  fun (tA, xA) (tB, xB) a b =>
      if validLdAnswer tA a && validLdAnswer tB b then
        match tA, tB, a, b with
        | .point, .point, .pointVals u, .pointVals v => decide (u = v)
        | .aline, .point, .alinePolys f, .pointVals u =>
            decide (alinePointCondition P xA xB f u)
        | .point, .aline, .pointVals u, .alinePolys f =>
            decide (alinePointCondition P xB xA f u)
        | .dline, .point, .dlinePolys f, .pointVals u =>
            decide (dlinePointCondition P xA xB f u)
        | .point, .dline, .pointVals u, .dlinePolys f =>
            decide (dlinePointCondition P xB xA f u)
        | .aline, .aline, .alinePolys f, .alinePolys g => decide (f = g)
        | .dline, .dline, .dlinePolys f, .dlinePolys g => decide (f = g)
        | _, _, _, _ => true
      else false

/-- The low-degree game determined by its question distribution and win
predicate. This is blueprint
`def:ld-game`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
noncomputable def ldGame (P : LdParams) : Game where
  QuestionA := LdQuestion P
  QuestionB := LdQuestion P
  AnswerA := LdAnswer P
  AnswerB := LdAnswer P
  μ := ldQuestionDistribution P
  μ_prob := by
    exact Distribution.IsProbability.map
      (uniformDistribution_isProbability ((LdType × LdType) × LdSpace P)) _
  decide := ldWinPredicate P

end

end MIPStarRE.QPBT
