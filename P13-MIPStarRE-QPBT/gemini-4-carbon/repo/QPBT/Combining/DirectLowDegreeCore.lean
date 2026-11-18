module

public import QPBT.Observables.LineDefs
public import QPBT.Games.DistributionMarginals
public import QPBT.Games.DistanceTheorems.TensorSupport
public import QPBT.Games.Sandwich.Pasting.Heterogeneous
public import QPBT.Test.PauliBasisTest
public import QPBT.Test.LowDegreeGameMeasurements
public import QPBT.ExplicitConstants
public import QPBT.State
public import QPBT.Upstream
public import MIPStarRE.LDT.Basic.DistributionAvg
public import MIPStarRE.LDT.Preliminaries.PolynomialAgreement
public import MIPStarRE.LDT.Preliminaries.DistanceBounds
public import MIPStarRE.LDT.Preliminaries.Triangles.Core
public import MIPStarRE.LDT.Test.StrategyCore
public import MIPStarRE.LDT.Test.StrategyBiProj.Measurements
public import MIPStarRE.LDT.Test.StrategyRole.Algebra
public import MIPStarRE.LDT.Test.MainTheorem.MainFormal
public import MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.EnvelopeBounds
public import MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.CascadeBounds.SigmaZeta1
public import MIPStarRE.LDT.Test.MainTheorem.SourceScalars
public import MIPStarRE.LDT.Test.MainTheorem.SourceRoleRegister.Final
public import MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal

/-! # Consolidated direct low-degree geometry, game, and LDT/seed-fiber transport -/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-! ## Swap helpers on bipartite states and consistency defects -/

theorem stateQForm_prodComm_heteroKron {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : Op ιA) (B : Op ιB) :
    DistanceCalculus.stateQForm (reindexState (Equiv.prodComm ιA ιB) ψ) (heteroKron B A) =
      DistanceCalculus.stateQForm ψ (heteroKron A B) := by
  unfold DistanceCalculus.stateQForm applyOperatorToState heteroKron Matrix.kronecker reindexState
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  apply congrArg Complex.re
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [← (Equiv.prodComm ιA ιB).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun ⟨i, j⟩ => ?_
  dsimp only [ContinuousLinearEquiv.apply_symm_apply, Equiv.prodComm, Equiv.coe_fn_symm_mk,
    Equiv.coe_fn_mk, Matrix.kroneckerMap_apply]
  congr 1
  rw [← (Equiv.prodComm ιA ιB).symm.sum_comp]
  exact Fintype.sum_congr _ _ fun ⟨i', j'⟩ => by
    change B i i' * A j j' * ψ.ofLp (j', i') = A j j' * B i i' * ψ.ofLp (j', i')
    ring

theorem consistencyDefect_prodComm_heteroKron {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → α → Op ιA) (B : X → α → Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect μ (fun x a => heteroKron (B x a) 1) (fun x a => heteroKron 1 (A x a))
        (reindexState (Equiv.prodComm ιA ιB) ψ) =
      consistencyDefect μ (fun x a => heteroKron (A x a) 1) (fun x a => heteroKron 1 (B x a)) ψ := by
  unfold consistencyDefect avgOver
  simp_rw [DistanceCalculus.consistency_term_eq_stateQForm,
    DistanceCalculus.placed_product_stateQForm_eq]
  refine Finset.sum_congr rfl fun x _ => congrArg _ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b = a
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), stateQForm_prodComm_heteroKron]

/-! ## Geometry and directly indexed game -/

structure DirectLdParams where
  q : ℕ
  m : ℕ
  d : ℕ
  k : ℕ
  hm : 1 ≤ m
  hd : 1 ≤ d
  hk : 1 ≤ k
  hq : IsAdmissibleSize q

@[reducible] noncomputable def DirectLdParams.model (D : DirectLdParams) : FixedFieldModel D.q :=
  fixedFieldModel D.q D.hq

abbrev DirectScalarQ (D : DirectLdParams) := D.model.K

def DirectLdParams.firstIndex (D : DirectLdParams) : Fin D.m :=
  ⟨0, lt_of_lt_of_le Nat.zero_lt_one D.hm⟩

instance instNonemptyFinM_1 (D : DirectLdParams) : Nonempty (Fin D.m) := ⟨D.firstIndex⟩

@[reducible] def AdmissibleParams.extendedDirectLd (P : AdmissibleParams) : DirectLdParams where
  q := P.q
  m := 2 * P.m + 2
  d := P.d
  k := 1
  hm := by omega
  hd := P.hd
  hk := by decide
  hq := P.hq

structure DirectLdSpace (D : DirectLdParams) where
  point : Fin D.m → DirectScalarQ D
  index : Fin D.m
  direction : Fin D.m → DirectScalarQ D
  deriving DecidableEq, Fintype

instance instNonemptyDirectLdSpace (D : DirectLdParams) : Nonempty (DirectLdSpace D) :=
  ⟨⟨0, D.firstIndex, 0⟩⟩

def directLdSpacePointEquiv (D : DirectLdParams) :
    DirectLdSpace D ≃ (Fin D.m → DirectScalarQ D) × (Fin D.m × (Fin D.m → DirectScalarQ D)) where
  toFun s := (s.point, s.index, s.direction)
  invFun s := ⟨s.1, s.2.1, s.2.2⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

def directLdSpaceIndexEquiv (D : DirectLdParams) :
    DirectLdSpace D ≃ Fin D.m × ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)) where
  toFun s := (s.index, s.point, s.direction)
  invFun s := ⟨s.2.1, s.1, s.2.2⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

def directLdSpaceSplitEquiv (D : DirectLdParams) :
    DirectLdSpace D ≃ ((Fin D.m → DirectScalarQ D) × Fin D.m) × (Fin D.m → DirectScalarQ D) where
  toFun s := ((s.point, s.index), s.direction)
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv s := by cases s; rfl
  right_inv _ := rfl

def directPrefixProjection {D : DirectLdParams} (i : Fin D.m)
    (v : Fin D.m → DirectScalarQ D) : Fin D.m → DirectScalarQ D :=
  fun j => if j.val < i.val then 0 else v j

theorem directPrefixProjection_idem (D : DirectLdParams) (i : Fin D.m)
    (v : Fin D.m → DirectScalarQ D) :
    directPrefixProjection i (directPrefixProjection i v) = directPrefixProjection i v := by
  funext j; unfold directPrefixProjection; split_ifs <;> rfl

inductive DirectLineDesc (D : DirectLdParams) where
  | axis (base : Fin D.m → DirectScalarQ D) (index : Fin D.m)
      (baseFixed : lineRepMap (coordinateDirection index) base = base)
  | diagonal (base : Fin D.m → DirectScalarQ D) (index : Fin D.m)
      (direction : Fin D.m → DirectScalarQ D)
      (baseFixed : lineRepMap direction base = base)
      (prefixZero : ∀ j : Fin D.m, j.val < index.val → direction j = 0)
  deriving DecidableEq

def directLineDescCode (D : DirectLdParams) :
    DirectLineDesc D → ((Fin D.m → DirectScalarQ D) × Fin D.m) ⊕
      ((Fin D.m → DirectScalarQ D) × Fin D.m × (Fin D.m → DirectScalarQ D))
  | .axis base index _ => .inl (base, index)
  | .diagonal base index direction _ _ => .inr (base, index, direction)

noncomputable instance directLineDescFintype (D : DirectLdParams) : Fintype (DirectLineDesc D) :=
  Fintype.ofInjective (directLineDescCode D) fun l l' h => by
    cases l <;> cases l' <;> simp only [directLineDescCode, Sum.inl.injEq, Sum.inr.injEq,
      Prod.mk.injEq, reduceCtorEq] at h
    · rcases h with ⟨rfl, rfl⟩; rfl
    · rcases h with ⟨rfl, rfl, rfl⟩; rfl

def DirectLineDesc.kind {D : DirectLdParams} : DirectLineDesc D → LineKind
  | .axis _ _ _ => .axis
  | .diagonal _ _ _ _ _ => .diagonal

def DirectLineDesc.index {D : DirectLdParams} : DirectLineDesc D → Fin D.m
  | .axis _ index _ => index
  | .diagonal _ index _ _ _ => index

def DirectLineDesc.base {D : DirectLdParams} : DirectLineDesc D → Fin D.m → DirectScalarQ D
  | .axis base _ _ => base
  | .diagonal base _ _ _ _ => base

def DirectLineDesc.direction {D : DirectLdParams} : DirectLineDesc D → Fin D.m → DirectScalarQ D
  | .axis _ index _ => coordinateDirection index
  | .diagonal _ _ direction _ _ => direction

noncomputable def DirectLineDesc.pointSet {D : DirectLdParams}
    (line : DirectLineDesc D) : Set (Fin D.m → DirectScalarQ D) :=
  linePoints line.base line.direction

noncomputable def directALineDescOf (D : DirectLdParams) (s : DirectLdSpace D) : DirectLineDesc D :=
  .axis (lineRepMap (coordinateDirection s.index) s.point) s.index (lineRepMap_apply_self _ _)

noncomputable def directDLineDescOf (D : DirectLdParams) (s : DirectLdSpace D) : DirectLineDesc D :=
  let dir := directPrefixProjection s.index s.direction
  .diagonal (lineRepMap dir s.point) s.index dir (lineRepMap_apply_self _ _)
    fun j hj => by simp [dir, directPrefixProjection, hj]

noncomputable def directALinePointDist (D : DirectLdParams) :
    Distribution (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) :=
  (uniformDistribution (DirectLdSpace D)).map fun s => (directALineDescOf D s, s.point)

noncomputable def directDLinePointDist (D : DirectLdParams) :
    Distribution (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) :=
  (uniformDistribution (DirectLdSpace D)).map fun s => (directDLineDescOf D s, s.point)

noncomputable def directLinePointDist (D : DirectLdParams) :
    Distribution (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) :=
  Distribution.mix (1 / 2) (by norm_num) (by norm_num)
    (directALinePointDist D) (directDLinePointDist D)

theorem directALinePointDist_isProbability (D : DirectLdParams) :
    (directALinePointDist D).IsProbability :=
  (uniformDistribution_isProbability _).map _

theorem directDLinePointDist_isProbability (D : DirectLdParams) :
    (directDLinePointDist D).IsProbability :=
  (uniformDistribution_isProbability _).map _

theorem directLinePointDist_isProbability (D : DirectLdParams) :
    (directLinePointDist D).IsProbability :=
  Distribution.mix_isProbability _ _ _
    (directALinePointDist_isProbability D) (directDLinePointDist_isProbability D)
    (by norm_num) (by norm_num)

abbrev DirectDegPoly (D : DirectLdParams) (c : ℕ) := Fin (c + 1) → DirectScalarQ D

def DirectEvaluatesTo {D : DirectLdParams} {c : ℕ} (line : DirectLineDesc D)
    (f : DirectDegPoly D c) (u : Fin D.m → DirectScalarQ D) (a : DirectScalarQ D) : Prop :=
  (∃ t : DirectScalarQ D, u = line.base + t • line.direction) ∧
    ∀ t : DirectScalarQ D, u = line.base + t • line.direction → evalCoefficient f t = a

noncomputable def directEvalOpt {D : DirectLdParams} {c : ℕ}
    (line : DirectLineDesc D) (u : Fin D.m → DirectScalarQ D)
    (f : DirectDegPoly D c) : Option (DirectScalarQ D) := by
  classical
  exact if h : ∃ a : DirectScalarQ D, DirectEvaluatesTo line f u a then
    some (Classical.choose h) else none

abbrev DirectLdQuestion (D : DirectLdParams) := LdType × DirectLdSpace D

noncomputable def directLdMap (D : DirectLdParams) : LdType → DirectLdSpace D → DirectLdSpace D
  | .point, s => ⟨s.point, D.firstIndex, 0⟩
  | .aline, s => ⟨lineRepMap (coordinateDirection s.index) s.point, s.index, 0⟩
  | .dline, s =>
      let dir := directPrefixProjection s.index s.direction
      ⟨lineRepMap dir s.point, s.index, dir⟩

noncomputable def directLdQuestionDistribution (D : DirectLdParams) :
    Distribution (DirectLdQuestion D × DirectLdQuestion D) :=
  (uniformDistribution ((LdType × LdType) × DirectLdSpace D)).map fun s =>
    ((s.1.1, directLdMap D s.1.1 s.2), (s.1.2, directLdMap D s.1.2 s.2))

theorem directLdQuestionDistribution_isProbability (D : DirectLdParams) :
    (directLdQuestionDistribution D).IsProbability :=
  (uniformDistribution_isProbability _).map _

inductive DirectLdAnswer (D : DirectLdParams) where
  | pointVals (a : Fin D.k → DirectScalarQ D)
  | alinePolys (a : Fin D.k → Fin (D.d + 1) → DirectScalarQ D)
  | dlinePolys (a : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
  deriving DecidableEq

noncomputable def directLdAnswerEquiv (D : DirectLdParams) :
    DirectLdAnswer D ≃ (Fin D.k → DirectScalarQ D) ⊕
      ((Fin D.k → Fin (D.d + 1) → DirectScalarQ D) ⊕
        (Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)) where
  toFun | .pointVals a => .inl a | .alinePolys a => .inr (.inl a) | .dlinePolys a => .inr (.inr a)
  invFun | .inl a => .pointVals a | .inr (.inl a) => .alinePolys a | .inr (.inr a) => .dlinePolys a
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with a | (a | a) <;> rfl

instance instInhabitedDirectLdAnswer (D : DirectLdParams) : Inhabited (DirectLdAnswer D) :=
  ⟨.pointVals 0⟩

noncomputable instance instFintypeDirectLdAnswer (D : DirectLdParams) :
    Fintype (DirectLdAnswer D) :=
  Fintype.ofEquiv _ (directLdAnswerEquiv D).symm

def validDirectLdAnswer {D : DirectLdParams} : LdType → DirectLdAnswer D → Bool
  | .point, .pointVals _ => true
  | .aline, .alinePolys _ => true
  | .dline, .dlinePolys _ => true
  | _, _ => false

def directAlinePointCondition (D : DirectLdParams) (line point : DirectLdSpace D)
    (f : Fin D.k → Fin (D.d + 1) → DirectScalarQ D) (a : Fin D.k → DirectScalarQ D) : Prop :=
  ∀ t : DirectScalarQ D,
    point.point = line.point + t • coordinateDirection line.index →
      ∀ j : Fin D.k, evalCoefficient (f j) t = a j

def directDlinePointCondition (D : DirectLdParams) (line point : DirectLdSpace D)
    (f : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D) (a : Fin D.k → DirectScalarQ D) : Prop :=
  ∀ t : DirectScalarQ D,
    point.point = line.point + t • line.direction →
      ∀ j : Fin D.k, evalCoefficient (f j) t = a j

noncomputable def directLdWinPredicate (D : DirectLdParams) :
    DirectLdQuestion D → DirectLdQuestion D → DirectLdAnswer D → DirectLdAnswer D → Bool :=
  open Classical in
  fun (tA, xA) (tB, xB) a b =>
    if validDirectLdAnswer tA a && validDirectLdAnswer tB b then
      match tA, tB, a, b with
      | .point, .point, .pointVals u, .pointVals v => decide (u = v)
      | .aline, .point, .alinePolys f, .pointVals u => decide (directAlinePointCondition D xA xB f u)
      | .point, .aline, .pointVals u, .alinePolys f => decide (directAlinePointCondition D xB xA f u)
      | .dline, .point, .dlinePolys f, .pointVals u => decide (directDlinePointCondition D xA xB f u)
      | .point, .dline, .pointVals u, .dlinePolys f => decide (directDlinePointCondition D xB xA f u)
      | .aline, .aline, .alinePolys f, .alinePolys g => decide (f = g)
      | .dline, .dline, .dlinePolys f, .dlinePolys g => decide (f = g)
      | _, _, _, _ => true
    else false

theorem directLdWinPredicate_symm (D : DirectLdParams) (x y : DirectLdQuestion D)
    (a b : DirectLdAnswer D) :
    directLdWinPredicate D x y a b = directLdWinPredicate D y x b a := by
  rcases x with ⟨tA, xA⟩; rcases y with ⟨tB, xB⟩
  cases tA <;> cases tB <;> cases a <;> cases b <;>
    simp [directLdWinPredicate, validDirectLdAnswer, eq_comm]

@[reducible] noncomputable def directLdGame (D : DirectLdParams) : Game where
  QuestionA := DirectLdQuestion D
  QuestionB := DirectLdQuestion D
  AnswerA := DirectLdAnswer D
  AnswerB := DirectLdAnswer D
  μ := directLdQuestionDistribution D
  μ_prob := directLdQuestionDistribution_isProbability D
  decide := directLdWinPredicate D

def directLdPointQuestionOf (D : DirectLdParams) (u : Fin D.m → DirectScalarQ D) :
    DirectLdQuestion D := (.point, ⟨u, D.firstIndex, 0⟩)

def directLdPointValuesOrZero (D : DirectLdParams) :
    DirectLdAnswer D → Fin D.k → DirectScalarQ D
  | .pointVals values => values
  | .alinePolys _ => 0
  | .dlinePolys _ => 0

noncomputable abbrev DirectPolyTuple (D : DirectLdParams) :=
  Fin D.k → PolyIndex D.m (DirectScalarQ D) D.d

noncomputable abbrev DirectPolyMeasTuple (D : DirectLdParams) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  MIPStarRE.Quantum.Measurement (DirectPolyTuple D) ι

def evalDirectPolyTupleAt {D : DirectLdParams}
    (u : Fin D.m → DirectScalarQ D) (g : DirectPolyTuple D) : Fin D.k → DirectScalarQ D :=
  fun j => MvPolynomial.eval u (g j).1

/-! ## Game value and rejection probabilities -/

def directRejectedMass (D : DirectLdParams) (S : Strategy (directLdGame D))
    (x y : DirectLdQuestion D) : ℝ :=
  ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
    if directLdWinPredicate D x y a b then 0 else outcomeWeight S x y a b

theorem directRejectedMass_nonneg (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (x y : DirectLdQuestion D) :
    0 ≤ directRejectedMass D S x y :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs
    · exact le_rfl
    · exact outcomeWeight_nonneg S x y a b

noncomputable def directLdBranchRejectionProbability
    (D : DirectLdParams) (S : Strategy (directLdGame D)) (types : LdType × LdType) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace D)) fun sample =>
    directRejectedMass D S
      (types.1, directLdMap D types.1 sample)
      (types.2, directLdMap D types.2 sample)

theorem directLdBranchRejectionProbability_eq_avgOver (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (types : LdType × LdType) :
    directLdBranchRejectionProbability D S types =
      avgOver (uniformDistribution (DirectLdSpace D)) fun sample =>
        directRejectedMass D S
          (types.1, directLdMap D types.1 sample)
          (types.2, directLdMap D types.2 sample) := rfl

noncomputable def directLdRejectionProbability
    (D : DirectLdParams) (S : Strategy (directLdGame D)) : ℝ :=
  avgOver (uniformDistribution (LdType × LdType)) (directLdBranchRejectionProbability D S)

theorem sum_ldType (f : LdType → ℝ) :
    ∑ t : LdType, f t = f .point + f .aline + f .dline := by
  change (Finset.univ : Finset LdType).sum f = _
  rw [show (Finset.univ : Finset LdType) = {.point, .aline, .dline} by decide]
  simp [add_assoc]

theorem avgOver_ldType_pair (f : LdType × LdType → ℝ) :
    avgOver (uniformDistribution (LdType × LdType)) f =
      (f (.point, .point) + f (.point, .aline) + f (.point, .dline) +
        (f (.aline, .point) + f (.aline, .aline) + f (.aline, .dline)) +
        (f (.dline, .point) + f (.dline, .aline) + f (.dline, .dline))) / 9 := by
  unfold avgOver uniformDistribution Distribution.uniformOnFinset
  simp only [Finset.mem_univ, if_true, Finset.card_univ, Fintype.card_prod,
    show Fintype.card LdType = 3 by decide, Fintype.sum_prod_type]
  simp_rw [sum_ldType]; ring

theorem directLdBranchRejectionProbability_nonneg
    (D : DirectLdParams) (S : Strategy (directLdGame D)) (types : LdType × LdType) :
    0 ≤ directLdBranchRejectionProbability D S types :=
  avgOver_nonneg _ _ fun _ => directRejectedMass_nonneg D S _ _

theorem directLdRejectionProbability_eq_one_sub_value
    (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    directLdRejectionProbability D S = 1 - S.value := by
  let acc (types : LdType × LdType) (s : DirectLdSpace D) : ℝ :=
    ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
      if directLdWinPredicate D (types.1, directLdMap D types.1 s)
          (types.2, directLdMap D types.2 s) a b then
        outcomeWeight S (types.1, directLdMap D types.1 s) (types.2, directLdMap D types.2 s) a b
      else 0
  have hsum (types : LdType × LdType) (s : DirectLdSpace D) :
      acc types s + directRejectedMass D S (types.1, directLdMap D types.1 s)
        (types.2, directLdMap D types.2 s) = 1 := by
    dsimp only [acc, directRejectedMass]
    rw [← Finset.sum_add_distrib, ← outcomeWeight_sum_eq_one S
      (types.1, directLdMap D types.1 s) (types.2, directLdMap D types.2 s)]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib.symm.trans
      (Finset.sum_congr rfl fun b _ => by split_ifs <;> simp)
  have hb (types : LdType × LdType) :
      directLdBranchRejectionProbability D S types =
        1 - avgOver (uniformDistribution (DirectLdSpace D)) (acc types) := by
    rw [show directLdBranchRejectionProbability D S types =
        avgOver (uniformDistribution (DirectLdSpace D)) (fun s => 1 - acc types s) from
      avgOver_congr _ _ _ fun s => by linarith [hsum types s],
      avgOver_sub, avgOver_uniform_const]
  unfold directLdRejectionProbability
  rw [avgOver_congr _ _ _ hb, avgOver_sub, avgOver_uniform_const]
  congr 1; symm
  rw [Strategy.value]
  change avgOver (directLdQuestionDistribution D) _ = _
  rw [directLdQuestionDistribution, Distribution.avgOver_map]
  exact avgOver_uniform_prod (f := acc)

namespace Strategy

theorem value_nonneg {G : Game} (S : Strategy G) : 0 ≤ S.value :=
  avgOver_nonneg _ _ fun q => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split
    · exact outcomeWeight_nonneg S q.1 q.2 a b
    · exact le_rfl

end Strategy

theorem directLdRejectionProbability_le_one
    (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    directLdRejectionProbability D S ≤ 1 := by
  rw [directLdRejectionProbability_eq_one_sub_value]; linarith [S.value_nonneg]

/-! ## Parameter/field correspondence, line rebasing, and line-point resampling -/

@[reducible] def DirectLdParams.toLDTParameters (D : DirectLdParams) : Parameters where
  m := D.m
  q := D.q
  d := D.d
  hm := lt_of_lt_of_le Nat.zero_lt_one D.hm
  hq := by obtain ⟨n, _, hq⟩ := D.hq; rw [hq]; exact Nat.pow_pos (by decide)
  hqPrimePower := by obtain ⟨n, hn, hq⟩ := D.hq; exact ⟨2, n, Nat.prime_two, hn.pos, hq⟩

instance instNeZeroNatQ (D : DirectLdParams) : NeZero D.q :=
  ⟨Nat.ne_of_gt D.toLDTParameters.hq⟩

@[reducible] noncomputable def DirectLdParams.toLDTFieldModel (D : DirectLdParams) :
    FieldModel D.toLDTParameters.q := D.model.toFieldModel

noncomputable def directScalarEquiv (D : DirectLdParams) :
    DirectScalarQ D ≃ Fq D.toLDTParameters := binaryRepresentation D.model

noncomputable def directPointEquiv (D : DirectLdParams) :
    (Fin D.m → DirectScalarQ D) ≃ Point D.toLDTParameters where
  toFun u i := directScalarEquiv D (u (Fin.rev i))
  invFun u j := (directScalarEquiv D).symm (u (Fin.rev j))
  left_inv u := by funext j; simp
  right_inv u := by funext i; simp

@[simp] theorem directPointEquiv_apply (D : DirectLdParams)
    (u : Fin D.m → DirectScalarQ D) (i : Fin D.m) :
    directPointEquiv D u i = directScalarEquiv D (u (Fin.rev i)) := rfl

@[simp] theorem directPointEquiv_symm_apply (D : DirectLdParams)
    (u : Point D.toLDTParameters) (j : Fin D.m) :
    (directPointEquiv D).symm u j = (directScalarEquiv D).symm (u (Fin.rev j)) := rfl

noncomputable def coefficientPolynomial {K : Type*} [Field K] (n : ℕ)
    (c : Fin (n + 1) → K) : Polynomial K :=
  ((Polynomial.degreeLTEquiv K (n + 1)).symm c).1

theorem coefficientPolynomial_degree_le {K : Type*} [Field K] (n : ℕ)
    (c : Fin (n + 1) → K) : (coefficientPolynomial n c).natDegree ≤ n := by
  let p := (Polynomial.degreeLTEquiv K (n + 1)).symm c
  have hp : p.1 ∈ Polynomial.degreeLE K n := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]; exact p.2
  by_cases h0 : p.1 = 0
  · simp [coefficientPolynomial, p, h0]
  · exact Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hp)

@[simp] theorem coefficientPolynomial_coeff {K : Type*} [Field K] (n : ℕ)
    (c : Fin (n + 1) → K) (i : Fin (n + 1)) :
    (coefficientPolynomial n c).coeff i = c i :=
  congrFun ((Polynomial.degreeLTEquiv K (n + 1)).apply_symm_apply c) i

theorem coefficientPolynomial_eval {K : Type*} [Field K] (n : ℕ)
    (c : Fin (n + 1) → K) (t : K) :
    (coefficientPolynomial n c).eval t = evalCoefficient c t := by
  simpa [coefficientPolynomial, evalCoefficient] using
    Polynomial.eval_eq_sum_degreeLTEquiv (((Polynomial.degreeLTEquiv K (n + 1)).symm c).2) t

noncomputable def directAxisAnswerEquiv (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    DirectDegPoly D D.d ≃ AxisLinePolynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  exact
    { toFun := fun c => ⟨coefficientPolynomial D.d c, coefficientPolynomial_degree_le D.d c⟩
      invFun := fun f i => f.poly.coeff i
      left_inv := fun c => funext (coefficientPolynomial_coeff D.d c)
      right_inv := fun f => AxisLinePolynomial.ext <|
        linePolynomial_coeff_fin_injective D.toLDTParameters
          (coefficientPolynomial_degree_le D.d _) f.degreeBounded
          (coefficientPolynomial_coeff D.d _) }

noncomputable def directDiagonalAnswerEquiv (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    DirectDegPoly D (D.m * D.d) ≃ DiagonalLinePolynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  exact
    { toFun := fun c => ⟨coefficientPolynomial (D.m * D.d) c,
        coefficientPolynomial_degree_le (D.m * D.d) c⟩
      invFun := fun f i => f.poly.coeff i
      left_inv := fun c => funext (coefficientPolynomial_coeff (D.m * D.d) c)
      right_inv := fun f => DiagonalLinePolynomial.ext <|
        linePolynomial_coeff_fin_injective D.toLDTParameters
          (coefficientPolynomial_degree_le (D.m * D.d) _) f.degreeBounded
          (coefficientPolynomial_coeff (D.m * D.d) _) }

theorem directAxisAnswerEquiv_apply (D : DirectLdParams)
    (c : DirectDegPoly D D.d) (t : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    directAxisAnswerEquiv D c (directScalarEquiv D t) =
      directScalarEquiv D (evalCoefficient c t) := by
  letI := D.toLDTFieldModel
  simp only [directAxisAnswerEquiv, AxisLinePolynomial.toFun, evalLinePolynomialModel]
  rw [show decodeScalar (directScalarEquiv D t) = t from
    (FieldModel.equiv (q := D.q)).symm_apply_apply t]
  exact congrArg (FieldModel.equiv (q := D.q)) (coefficientPolynomial_eval D.d c t)

theorem directDiagonalAnswerEquiv_apply (D : DirectLdParams)
    (c : DirectDegPoly D (D.m * D.d)) (t : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerEquiv D c (directScalarEquiv D t) =
      directScalarEquiv D (evalCoefficient c t) := by
  letI := D.toLDTFieldModel
  simp only [directDiagonalAnswerEquiv, DiagonalLinePolynomial.toFun, evalLinePolynomialModel]
  rw [show decodeScalar (directScalarEquiv D t) = t from
    (FieldModel.equiv (q := D.q)).symm_apply_apply t]
  exact congrArg (FieldModel.equiv (q := D.q)) (coefficientPolynomial_eval (D.m * D.d) c t)

@[reducible] def LdParams.toDirectLdParams (L : LdParams) : DirectLdParams where
  q := L.q
  m := L.m
  d := L.d
  k := L.k
  hm := L.hm
  hd := L.hd
  hk := L.hk
  hq := L.hq

@[simp] theorem LdParams.toDirectLdParams_model (L : LdParams) :
    L.toDirectLdParams.model = L.model := by
  unfold DirectLdParams.model LdParams.model LdParams.toDirectLdParams; congr

noncomputable def ldDirectAnswerEquiv (L : LdParams) :
    LdAnswer L ≃ DirectLdAnswer L.toDirectLdParams where
  toFun | .pointVals a => .pointVals a | .alinePolys a => .alinePolys a | .dlinePolys a => .dlinePolys a
  invFun | .pointVals a => .pointVals a | .alinePolys a => .alinePolys a | .dlinePolys a => .dlinePolys a
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

noncomputable def parseLdQuestion (L : LdParams) :
    LdQuestion L → DirectLdQuestion L.toDirectLdParams
  | (.point, z) => (.point, ⟨z.point, L.toDirectLdParams.firstIndex, 0⟩)
  | (.aline, z) => (.aline, ⟨z.point, chiIndex L z.seed, 0⟩)
  | (.dline, z) => (.dline, ⟨z.point, chiIndex L z.seed, z.direction⟩)

noncomputable def ldSpaceOfDirectResidue (L : LdParams)
    (sample : DirectLdSpace L.toDirectLdParams) (residue : Fin (L.q / L.m)) : LdSpace L
  | .inl (.inl i) => sample.point i
  | .inl (.inr _) => seedOfIndexResidue L sample.index residue
  | .inr i => sample.direction i

@[simp] theorem ldSpaceOfDirectResidue_point (L : LdParams)
    (s : DirectLdSpace L.toDirectLdParams) (r : Fin (L.q / L.m)) :
    (ldSpaceOfDirectResidue L s r).point = s.point := rfl

@[simp] theorem ldSpaceOfDirectResidue_seed (L : LdParams)
    (s : DirectLdSpace L.toDirectLdParams) (r : Fin (L.q / L.m)) :
    (ldSpaceOfDirectResidue L s r).seed = seedOfIndexResidue L s.index r := rfl

@[simp] theorem ldSpaceOfDirectResidue_direction (L : LdParams)
    (s : DirectLdSpace L.toDirectLdParams) (r : Fin (L.q / L.m)) :
    (ldSpaceOfDirectResidue L s r).direction = s.direction := rfl

noncomputable def ldSpaceSeedFiberEquiv (L : LdParams) :
    LdSpace L ≃ DirectLdSpace L.toDirectLdParams × Fin (L.q / L.m) where
  toFun z := (⟨z.point, (seedFiberEquiv L z.seed).1, z.direction⟩, (seedFiberEquiv L z.seed).2)
  invFun x := ldSpaceOfDirectResidue L x.1 x.2
  left_inv z := by
    funext i; rcases i with (i | ⟨⟩) | i
    · rfl
    · exact (seedFiberEquiv L).symm_apply_apply z.seed
    · rfl
  right_inv := fun ⟨⟨pt, idx, dir⟩, r⟩ => Prod.ext
    (by simp [seedFiberEquiv_seedOfIndexResidue]) (by simp [seedOfIndexResidue])

theorem parseLdQuestion_ldCL_ofDirectResidue (L : LdParams) (t : LdType)
    (s : DirectLdSpace L.toDirectLdParams) (r : Fin (L.q / L.m)) :
    parseLdQuestion L (t, ldCL L t (ldSpaceOfDirectResidue L s r)) =
      (t, directLdMap L.toDirectLdParams t s) := by
  cases t
  · rfl
  · ext <;> simp only [parseLdQuestion, ldCL, ldALineCL, directLdMap, ldSpaceOfDirectResidue,
      ldSpaceOfDirectResidue_point, LdSpace.seed, chiIndex_seedOfIndexResidue]; rfl
  · ext <;> simp only [parseLdQuestion, ldCL, ldDLineCL, directLdMap, ldSpaceOfDirectResidue,
      ldSpaceOfDirectResidue_point, ldSpaceOfDirectResidue_direction, LdSpace.seed,
      LdSpace.direction, chiIndex_seedOfIndexResidue, prefixProjection]; rfl

theorem ldWinPredicate_parse (L : LdParams) (x y : LdQuestion L) (a b : LdAnswer L) :
    directLdWinPredicate L.toDirectLdParams (parseLdQuestion L x) (parseLdQuestion L y)
        (ldDirectAnswerEquiv L a) (ldDirectAnswerEquiv L b) =
      ldWinPredicate L x y a b := by
  rcases x with ⟨tx, x⟩; rcases y with ⟨ty, y⟩
  cases tx <;> cases ty <;> cases a <;> cases b <;> rfl

noncomputable def ldQuestionSeedFiberEquiv (L : LdParams) :
    ((LdType × LdType) × LdSpace L) ≃
      (((LdType × LdType) × DirectLdSpace L.toDirectLdParams) × Fin (L.q / L.m)) :=
  (Equiv.prodCongr (Equiv.refl _) (ldSpaceSeedFiberEquiv L)).trans (Equiv.prodAssoc _ _ _).symm

noncomputable def directLineRepParameter {K : Type*} [Field K] {m : ℕ} (v u : Fin m → K) : K :=
  Classical.choose (mem_linePoints_lineRepMap v u)

theorem directLineRepParameter_spec {K : Type*} [Field K] {m : ℕ} (v u : Fin m → K) :
    u = lineRepMap v u + directLineRepParameter v u • v :=
  Classical.choose_spec (mem_linePoints_lineRepMap v u)

theorem lineRepMap_add_smul {K : Type*} [Field K] {m : ℕ} (v u : Fin m → K) (t : K) :
    lineRepMap v (u + t • v) = lineRepMap v u := by
  let W : Submodule K (Fin m → K) := Submodule.span K ({v} : Set (Fin m → K))
  have hv : v ∈ W := Submodule.subset_span (Set.mem_singleton v)
  have hzero : lineRepMap v v = 0 := by
    simp [lineRepMap, canonicalProjOfKernel, W, LinearMap.comp_apply,
      Submodule.projectionOnto_apply_of_mem_right
        (isCompl_registerSubmodule_canonicalComplement W).symm hv]
  simp [map_add, map_smul, hzero]

theorem directLineRepParameter_eq_of_nonzero {K : Type*} [Field K] {m : ℕ}
    {v u : Fin m → K} (hv : v ≠ 0) {t : K} (ht : u = lineRepMap v u + t • v) :
    directLineRepParameter v u = t := by
  have hfun : directLineRepParameter v u • v = t • v :=
    add_left_cancel ((directLineRepParameter_spec v u).symm.trans ht)
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; exact hv (funext fun i => by simpa using not_exists.mp h i)
  exact mul_right_cancel₀ hi (by simpa using congrFun hfun i)

theorem directLineRepParameter_add_smul {K : Type*} [Field K] {m : ℕ}
    {v u : Fin m → K} (hv : v ≠ 0) (t : K) :
    directLineRepParameter v (u + t • v) = directLineRepParameter v u + t := by
  apply directLineRepParameter_eq_of_nonzero hv
  rw [lineRepMap_add_smul]
  conv_lhs => rw [directLineRepParameter_spec v u]
  module

theorem avgOver_directLinePoint_resample (D : DirectLdParams)
    (dirOf : Fin D.m → (Fin D.m → DirectScalarQ D) → (Fin D.m → DirectScalarQ D))
    (lineOf : DirectLdSpace D → DirectLineDesc D)
    (hbase : ∀ s, (lineOf s).base = lineRepMap (dirOf s.index s.direction) s.point)
    (hdir : ∀ s, (lineOf s).direction = dirOf s.index s.direction)
    (hline : ∀ (s : DirectLdSpace D) (t : DirectScalarQ D),
      lineOf ⟨s.point + t • dirOf s.index s.direction, s.index, s.direction⟩ = lineOf s)
    (F : (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) → Error) :
    avgOver (uniformDistribution (DirectLdSpace D)) (fun s =>
        avgOver (uniformDistribution (DirectScalarQ D)) fun t =>
          F (lineOf s, (lineOf s).base + t • (lineOf s).direction)) =
      avgOver (uniformDistribution (DirectLdSpace D)) fun s => F (lineOf s, s.point) := by
  let tr (t : DirectScalarQ D) : DirectLdSpace D ≃ DirectLdSpace D :=
    { toFun := fun s => ⟨s.point + t • dirOf s.index s.direction, s.index, s.direction⟩
      invFun := fun s => ⟨s.point + (-t) • dirOf s.index s.direction, s.index, s.direction⟩
      left_inv := fun ⟨_, _, _⟩ => by simp [add_assoc]
      right_inv := fun ⟨_, _, _⟩ => by simp [add_assoc] }
  have hp (s : DirectLdSpace D) :
      avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
        F (lineOf s, (lineOf s).base + t • (lineOf s).direction)) =
      avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
        F (lineOf s, s.point + t • dirOf s.index s.direction)) := by
    let r := directLineRepParameter (dirOf s.index s.direction) s.point
    refine (avgOver_uniform_equiv (Equiv.addRight (-r)) _).trans (avgOver_congr _ _ _ fun t => ?_)
    congr 2
    rw [hdir, hbase, show (Equiv.addRight (-r)).symm t = t + r by simp,
      add_comm t r, add_smul, ← add_assoc, ← directLineRepParameter_spec]
  rw [avgOver_congr _ _ _ hp, avgOver_uniform_comm]
  refine (avgOver_congr _ _ _ fun t => ?_).trans (avgOver_uniform_const _)
  refine (avgOver_uniform_equiv (tr t) _).trans (avgOver_congr _ _ _ fun s => ?_)
  congr 2
  · exact hline s (-t)
  · simp [tr, add_assoc]

theorem avgOver_directALinePointDist_resample (D : DirectLdParams)
    (F : (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) → Error) :
    avgOver ((directALinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) fun t =>
          F (line, line.base + t • line.direction)) =
      avgOver (directALinePointDist D) F := by
  simp only [directALinePointDist, Distribution.avgOver_map]
  exact avgOver_directLinePoint_resample D (fun i _ => coordinateDirection i) (directALineDescOf D)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => by simp [directALineDescOf, lineRepMap_add_smul]) F

theorem avgOver_directDLinePointDist_resample (D : DirectLdParams)
    (F : (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) → Error) :
    avgOver ((directDLinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) fun t =>
          F (line, line.base + t • line.direction)) =
      avgOver (directDLinePointDist D) F := by
  simp only [directDLinePointDist, Distribution.avgOver_map]
  exact avgOver_directLinePoint_resample D directPrefixProjection (directDLineDescOf D)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => by simp [directDLineDescOf, lineRepMap_add_smul]) F

/-! ## LDT question/answer transport -/

def directionSupport (D : DirectLdParams) (v : Fin D.m → DirectScalarQ D) : Finset (Fin D.m) :=
  Finset.univ.filter fun j => v j ≠ 0

noncomputable def directDiagonalIndexOf (D : DirectLdParams)
    (v : Fin D.m → DirectScalarQ D) : Fin D.m :=
  if h : (directionSupport D v).Nonempty then (directionSupport D v).min' h else Fin.rev D.firstIndex

theorem directDiagonalIndexOf_prefixProjection (D : DirectLdParams)
    (i : Fin D.m) (v : Fin D.m → DirectScalarQ D) (hi : v i ≠ 0) :
    directDiagonalIndexOf D (directPrefixProjection i v) = i := by
  have hmem : i ∈ directionSupport D (directPrefixProjection i v) := by
    simp [directionSupport, directPrefixProjection, hi]
  unfold directDiagonalIndexOf
  rw [dif_pos ⟨i, hmem⟩]
  refine le_antisymm (Finset.min'_le _ _ hmem) (Finset.le_min' _ _ _ fun j hj => ?_)
  by_contra hlt
  have hj0 : directPrefixProjection i v j = 0 := by
    simp [directPrefixProjection, Fin.lt_def.mp (not_le.mp hlt)]
  exact (Finset.mem_filter.mp hj).2 hj0

abbrev ldtPointToDirect (D : DirectLdParams) :
    Point D.toLDTParameters → Fin D.m → DirectScalarQ D := (directPointEquiv D).symm

noncomputable def directAxisQuestionOf (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters) : DirectLdQuestion D :=
  let i := Fin.rev line.direction
  (.aline, ⟨lineRepMap (coordinateDirection i) (ldtPointToDirect D line.base), i, 0⟩)

noncomputable def directDiagonalQuestionOf (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters) : DirectLdQuestion D :=
  let v := ldtPointToDirect D line.direction
  (.dline, ⟨lineRepMap v (ldtPointToDirect D line.base), directDiagonalIndexOf D v, v⟩)

noncomputable def directPointQuestionOf (D : DirectLdParams)
    (u : Point D.toLDTParameters) : DirectLdQuestion D :=
  directLdPointQuestionOf D (ldtPointToDirect D u)

@[simp] theorem directPointQuestionOf_directPointEquiv (D : DirectLdParams)
    (u : Fin D.m → DirectScalarQ D) :
    directPointQuestionOf D (directPointEquiv D u) = directLdPointQuestionOf D u := by
  simp [directPointQuestionOf, ldtPointToDirect]

def ldtDiagonalLineOf (D : DirectLdParams) (s : DirectLdSpace D) :
    DiagonalLine D.toLDTParameters :=
  { base := directPointEquiv D s.point, direction := directPointEquiv D s.direction }

theorem ldtPointToDirect_axis_rebase (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters) (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    ldtPointToDirect D (line.rebaseAt t).base =
      ldtPointToDirect D line.base +
        (directScalarEquiv D).symm t • coordinateDirection (Fin.rev line.direction) := by
  letI := D.toLDTFieldModel
  funext i
  simp only [ldtPointToDirect, directPointEquiv_symm_apply, AxisParallelLine.rebaseAt,
    AxisParallelLine.pointAt, Pi.add_apply, Pi.smul_apply]
  by_cases hi : i = Fin.rev line.direction
  · subst hi; simp only [coordinateDirection, Fin.rev_rev, if_pos, smul_eq_mul,
      Pi.single_eq_same, mul_one]
    exact (FieldModel.equiv (q := D.q)).symm_apply_apply _
  · have hrev : Fin.rev i ≠ line.direction := fun h => hi (by rw [← h, Fin.rev_rev])
    simp [hi, hrev, coordinateDirection]

theorem ldtPointToDirect_diagonal_rebase (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters) (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    ldtPointToDirect D (line.rebaseAt t).base =
      ldtPointToDirect D line.base +
        (directScalarEquiv D).symm t • ldtPointToDirect D line.direction := by
  letI := D.toLDTFieldModel
  funext i
  change decodeScalar (addCoord (line.base (Fin.rev i)) (mulCoord t (line.direction (Fin.rev i)))) =
    decodeScalar (line.base (Fin.rev i)) + decodeScalar t * decodeScalar (line.direction (Fin.rev i))
  simp [addCoord, mulCoord]

theorem directAxisQuestionOf_rebase (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters) (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    directAxisQuestionOf D (line.rebaseAt t) = directAxisQuestionOf D line := by
  letI := D.toLDTFieldModel
  simp only [directAxisQuestionOf, AxisParallelLine.rebaseAt_direction]
  rw [ldtPointToDirect_axis_rebase, lineRepMap_add_smul]

theorem directDiagonalQuestionOf_rebase (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters) (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    directDiagonalQuestionOf D (line.rebaseAt t) = directDiagonalQuestionOf D line := by
  letI := D.toLDTFieldModel
  simp only [directDiagonalQuestionOf, DiagonalLine.rebaseAt]
  have h := ldtPointToDirect_diagonal_rebase D line t
  change ldtPointToDirect D (line.pointAt t) = _ at h
  rw [h, lineRepMap_add_smul]

theorem directScalarEquiv_add (D : DirectLdParams) (x y : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    directScalarEquiv D (x + y) = addCoord (directScalarEquiv D x) (directScalarEquiv D y) := by
  letI := D.toLDTFieldModel
  change FieldModel.equiv (x + y) =
    FieldModel.equiv (FieldModel.equiv.symm (FieldModel.equiv x) +
      FieldModel.equiv.symm (FieldModel.equiv y))
  rw [FieldModel.equiv.symm_apply_apply, FieldModel.equiv.symm_apply_apply]

noncomputable def directAxisRebaseParameter (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters) : DirectScalarQ D :=
  directLineRepParameter (coordinateDirection (Fin.rev line.direction)) (ldtPointToDirect D line.base)

noncomputable def directDiagonalRebaseParameter (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters) : DirectScalarQ D :=
  directLineRepParameter (ldtPointToDirect D line.direction) (ldtPointToDirect D line.base)

noncomputable def constantDiagonalAnswer (D : DirectLdParams) (x : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    DiagonalLinePolynomial D.toLDTParameters :=
  letI := D.toLDTFieldModel
  { poly := Polynomial.C x, degreeBounded := by simp }

theorem constantDiagonalAnswer_apply (D : DirectLdParams) (x : DirectScalarQ D)
    (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    constantDiagonalAnswer D x t = directScalarEquiv D x := by
  letI := D.toLDTFieldModel
  change encodeScalar ((Polynomial.C x).eval (decodeScalar t)) = directScalarEquiv D x
  rw [Polynomial.eval_C]; rfl

noncomputable def directPointAnswerReadout (D : DirectLdParams) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    DirectLdAnswer D → Fq D.toLDTParameters :=
  letI := D.toLDTFieldModel
  fun a => directScalarEquiv D (directLdPointValuesOrZero D a r)

noncomputable def directAxisAnswerReadout (D : DirectLdParams) (r : Fin D.k)
    (line : AxisParallelLine D.toLDTParameters) :
    letI := D.toLDTFieldModel
    DirectLdAnswer D → AxisLinePolynomial D.toLDTParameters :=
  letI := D.toLDTFieldModel
  fun
    | .alinePolys a => AxisLinePolynomial.reparamAt (directAxisAnswerEquiv D (a r))
        (directScalarEquiv D (directAxisRebaseParameter D line))
    | _ => default

noncomputable def directDiagonalAnswerReadout (D : DirectLdParams) (r : Fin D.k)
    (line : DiagonalLine D.toLDTParameters) :
    letI := D.toLDTFieldModel
    DirectLdAnswer D → DiagonalLinePolynomial D.toLDTParameters :=
  letI := D.toLDTFieldModel
  fun
    | .dlinePolys a =>
        if ldtPointToDirect D line.direction = 0 then
          constantDiagonalAnswer D (evalCoefficient (a r) 0)
        else
          DiagonalLinePolynomial.reparamAt (directDiagonalAnswerEquiv D (a r))
            (directScalarEquiv D (directDiagonalRebaseParameter D line))
    | _ => default

theorem directAxisAnswerReadout_rebase (D : DirectLdParams) (r : Fin D.k)
    (line : AxisParallelLine D.toLDTParameters) (t : Fq D.toLDTParameters)
    (answer : DirectLdAnswer D) :
    letI := D.toLDTFieldModel
    directAxisAnswerReadout D r (line.rebaseAt t) answer =
      AxisLinePolynomial.reparamAt (directAxisAnswerReadout D r line answer) t := by
  letI := D.toLDTFieldModel
  cases answer with
  | pointVals _ | dlinePolys _ => simp [directAxisAnswerReadout]
  | alinePolys a =>
      have hc0 : (coordinateDirection (Fin.rev line.direction) : Fin D.m → DirectScalarQ D) ≠ 0 :=
        fun h => by simpa [coordinateDirection] using congrFun h (Fin.rev line.direction)
      simp only [directAxisAnswerReadout, directAxisRebaseParameter, AxisParallelLine.rebaseAt_direction]
      rw [ldtPointToDirect_axis_rebase, directLineRepParameter_add_smul hc0,
        directScalarEquiv_add, (directScalarEquiv D).apply_symm_apply]
      exact (AxisLinePolynomial.reparamAt_reparamAt _ _ _).symm

theorem directDiagonalAnswerReadout_rebase (D : DirectLdParams) (r : Fin D.k)
    (line : DiagonalLine D.toLDTParameters) (t : Fq D.toLDTParameters)
    (answer : DirectLdAnswer D) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerReadout D r (line.rebaseAt t) answer =
      DiagonalLinePolynomial.reparamAt (directDiagonalAnswerReadout D r line answer) t := by
  letI := D.toLDTFieldModel
  cases answer with
  | pointVals _ | alinePolys _ => simp [directDiagonalAnswerReadout]
  | dlinePolys a =>
      have hdir_reb : ldtPointToDirect D (line.rebaseAt t).direction =
          ldtPointToDirect D line.direction := rfl
      by_cases hdir : ldtPointToDirect D line.direction = 0
      · simp only [directDiagonalAnswerReadout, hdir_reb, hdir, ↓reduceIte]
        apply DiagonalLinePolynomial.ext
        simp [constantDiagonalAnswer, DiagonalLinePolynomial.reparamAt]
      · simp only [directDiagonalAnswerReadout, hdir_reb, hdir, ↓reduceIte,
          directDiagonalRebaseParameter]
        rw [ldtPointToDirect_diagonal_rebase, directLineRepParameter_add_smul hdir,
          directScalarEquiv_add, (directScalarEquiv D).apply_symm_apply]
        exact (DiagonalLinePolynomial.reparamAt_reparamAt _ _ _).symm

/-! ## Seed-fiber dilation, strategy transport, and value equality -/

noncomputable def matrixMeasurementTransport {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (M : MIPStarRE.Quantum.Measurement α ι) :
    MIPStarRE.Quantum.Measurement β ι :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun b => M.effect (e.symm b)) (fun b => M.pos (e.symm b))
    ((Equiv.sum_comp e.symm M.effect).trans M.sum_eq_one)

@[simp] theorem matrixMeasurementTransport_effect {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (M : MIPStarRE.Quantum.Measurement α ι) (b : β) :
    (matrixMeasurementTransport e M).effect b = M.effect (e.symm b) := rfl

noncomputable def blockDiagonalMeasurement {α ι blk : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype blk] [DecidableEq blk]
    (M : blk → MIPStarRE.Quantum.Measurement α ι) :
    MIPStarRE.Quantum.Measurement α (ι × blk) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => Matrix.blockDiagonal fun r => (M r).effect a)
    (fun a => Matrix.blockDiagonal_nonneg _ fun r => (M r).pos a)
    (by
      ext ⟨i, r⟩ ⟨j, s⟩
      simp only [Matrix.sum_apply, Matrix.blockDiagonal_apply]
      by_cases hrs : r = s
      · subst s; simp only [if_pos]
        simpa [Matrix.sum_apply, Matrix.one_apply] using congrFun (congrFun (M r).sum_eq_one i) j
      · simp [hrs])

@[simp] theorem blockDiagonalMeasurement_effect {α ι blk : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype blk] [DecidableEq blk]
    (M : blk → MIPStarRE.Quantum.Measurement α ι) (a : α) :
    (blockDiagonalMeasurement M).effect a = Matrix.blockDiagonal fun r => (M r).effect a := rfl

theorem blockDiagonalMeasurement_isProjective {α ι blk : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype blk] [DecidableEq blk]
    (M : blk → MIPStarRE.Quantum.Measurement α ι)
    (hM : ∀ r, MIPStarRE.QPBT.Measurement.IsProjective (M r)) :
    MIPStarRE.QPBT.Measurement.IsProjective (blockDiagonalMeasurement M) := by
  intro a
  constructor
  · change Matrix.blockDiagonal (fun r => (M r).effect a) *
        Matrix.blockDiagonal (fun r => (M r).effect a) =
      Matrix.blockDiagonal (fun r => (M r).effect a)
    rw [← Matrix.blockDiagonal_mul]
    exact congrArg _ (funext fun r => (hM r a).isIdempotentElem.eq)
  · rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, blockDiagonalMeasurement_effect,
      Matrix.blockDiagonal_conjTranspose]
    exact congrArg _ (funext fun r => (hM r a).isSelfAdjoint.star_eq)

noncomputable def seedResidueAncilla (L : LdParams) :
    EuclideanSpace ℂ (Fin (L.q / L.m) × Fin (L.q / L.m)) :=
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  eprState (Fin (L.q / L.m))

noncomputable def seedFiberLiftedState {G : Game} (S : Strategy G) (L : LdParams) :
    EuclideanSpace ℂ ((S.ιA × Fin (L.q / L.m)) × (S.ιB × Fin (L.q / L.m))) :=
  reindexState prodShuffle (vecTensor S.ψ (seedResidueAncilla L))

theorem seedFiberLiftedState_norm {G : Game} (S : Strategy G) (L : LdParams) :
    ‖seedFiberLiftedState S L‖ = 1 := by
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  rw [seedFiberLiftedState, reindexState_norm_eq, vecTensor_norm_eq, S.ψ_norm,
    seedResidueAncilla, eprState_norm, one_mul]

noncomputable def seededLdQuestion (L : LdParams)
    (q : DirectLdQuestion L.toDirectLdParams) (residue : Fin (L.q / L.m)) : LdQuestion L :=
  (q.1, ldCL L q.1 (ldSpaceOfDirectResidue L q.2 residue))

noncomputable def ldStrategyToDirect (L : LdParams)
    (S : Strategy (ldGame L)) : Strategy (directLdGame L.toDirectLdParams) where
  ιA := S.ιA × Fin (L.q / L.m)
  ιB := S.ιB × Fin (L.q / L.m)
  ψ := seedFiberLiftedState S L
  ψ_norm := seedFiberLiftedState_norm S L
  A q := blockDiagonalMeasurement fun r =>
    matrixMeasurementTransport (ldDirectAnswerEquiv L) (S.A (seededLdQuestion L q r))
  B q := blockDiagonalMeasurement fun r =>
    matrixMeasurementTransport (ldDirectAnswerEquiv L) (S.B (seededLdQuestion L q r))

theorem ldStrategyToDirect_isProjective (L : LdParams)
    (S : Strategy (ldGame L)) (hS : S.IsProjective) :
    (ldStrategyToDirect L S).IsProjective :=
  ⟨fun _ => blockDiagonalMeasurement_isProjective _ fun _ b => hS.1 _ ((ldDirectAnswerEquiv L).symm b),
   fun _ => blockDiagonalMeasurement_isProjective _ fun _ b => hS.2 _ ((ldDirectAnswerEquiv L).symm b)⟩

theorem seedFiberLiftedState_apply {G : Game} (S : Strategy G) (L : LdParams)
    (i : S.ιA) (j : S.ιB) (r s : Fin (L.q / L.m)) :
    seedFiberLiftedState S L ((i, r), (j, s)) =
      if r = s then S.ψ (i, j) * (Real.sqrt (Fintype.card (Fin (L.q / L.m)) : ℝ) : ℂ)⁻¹ else 0 := by
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  simp [seedFiberLiftedState, reindexState, vecTensor, seedResidueAncilla, eprState, prodShuffle]

noncomputable def matrixMeasurementToLDTProjMeas {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι) (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.LDT.ProjMeas α ι where
  toMeasurement := {
    toSubMeas := {
      outcome := M.effect, total := 1, outcome_pos := M.pos,
      sum_eq_total := M.sum_eq_one, total_le_one := le_rfl }
    total_eq_one := rfl }
  proj a := (hM a).isIdempotentElem.eq

@[simp] theorem matrixMeasurementToLDTProjMeas_outcome {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι) (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (a : α) :
    (matrixMeasurementToLDTProjMeas M hM).outcome a = M.effect a := rfl

theorem strategy_carrier_nonempty {G : Game} (S : Strategy G) : Nonempty (S.ιA × S.ιB) := by
  by_contra h; rw [not_nonempty_iff] at h; letI := h
  have hnorm := S.ψ_norm; rw [Subsingleton.elim S.ψ 0, norm_zero] at hnorm; exact zero_ne_one hnorm

noncomputable def strategyPureState {G : Game} (S : Strategy G)
    [Nonempty (S.ιA × S.ιB)] : PureState (S.ιA × S.ιB) where
  vector := S.ψ
  unit := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, S.ψ_norm]; norm_num

noncomputable def strategyQuantumState {G : Game} (S : Strategy G) :
    QuantumState (S.ιA × S.ιB) :=
  letI := strategy_carrier_nonempty S
  PureState.toQuantumState (strategyPureState S)

theorem strategyQuantumState_isNormalized {G : Game} (S : Strategy G) :
    (strategyQuantumState S).IsNormalized := by
  letI := strategy_carrier_nonempty S
  simpa [strategyQuantumState] using PureState.toQuantumState_isNormalized (strategyPureState S)

theorem strategyQuantumState_ev_eq_stateQForm {G : Game} (S : Strategy G)
    (A : Op S.ιA) (B : Op S.ιB) :
    ev (strategyQuantumState S) (opTensor A B) =
      DistanceCalculus.stateQForm S.ψ (heteroKron A B) := by
  letI := strategy_carrier_nonempty S
  rw [show strategyQuantumState S = PureState.toQuantumState (strategyPureState S) from rfl,
    PureState.ev_eq_re_inner]
  unfold DistanceCalculus.stateQForm applyOperatorToState heteroKron opTensor
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  exact congrArg Complex.re (dotProduct_comm _ _)

theorem directPostprocessBornWeight (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (x y : DirectLdQuestion D) (readA : DirectLdAnswer D → α) (readB : DirectLdAnswer D → β)
    (a : α) (b : β) :
    ev (strategyQuantumState S)
        (opTensor
          ((ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).outcome a)
          ((ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).outcome b)) =
      ∑ dA ∈ Finset.univ.filter (fun ans => readA ans = a),
        ∑ dB ∈ Finset.univ.filter (fun ans => readB ans = b),
          outcomeWeight S x y dA dB := by
  rw [strategyQuantumState_ev_eq_stateQForm]
  simp only [ProjMeas.postprocess, SubMeas.postprocess_outcome, matrixMeasurementToLDTProjMeas_outcome,
    DistanceCalculus.heteroKron_finset_sum_left, DistanceCalculus.stateQForm_finset_sum]
  refine Finset.sum_congr rfl fun dA _ => ?_
  rw [DistanceCalculus.heteroKron_finset_sum_right, DistanceCalculus.stateQForm_finset_sum]
  rfl

theorem ldStrategyToDirect_bornWeight (L : LdParams) (S : Strategy (ldGame L))
    (x y : DirectLdQuestion L.toDirectLdParams) (a b : DirectLdAnswer L.toDirectLdParams) :
    outcomeWeight (ldStrategyToDirect L S) x y a b =
      (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ * ∑ residue,
        outcomeWeight S (seededLdQuestion L x residue) (seededLdQuestion L y residue)
          ((ldDirectAnswerEquiv L).symm a) ((ldDirectAnswerEquiv L).symm b) := by
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  let EA (r : Fin (L.q / L.m)) :=
    (S.A (seededLdQuestion L x r)).effect ((ldDirectAnswerEquiv L).symm a)
  let EB (r : Fin (L.q / L.m)) :=
    (S.B (seededLdQuestion L y r)).effect ((ldDirectAnswerEquiv L).symm b)
  suffices h : (inner ℂ (seedFiberLiftedState S L)
      (applyOperatorToState (heteroKron (Matrix.blockDiagonal EA) (Matrix.blockDiagonal EB))
        (seedFiberLiftedState S L)) : ℂ) =
      (Fintype.card (Fin (L.q / L.m)) : ℂ)⁻¹ * ∑ r,
        inner ℂ S.ψ (applyOperatorToState (heteroKron (EA r) (EB r)) S.ψ) by
    change (inner ℂ (seedFiberLiftedState S L)
      (applyOperatorToState (heteroKron (Matrix.blockDiagonal EA) (Matrix.blockDiagonal EB))
        (seedFiberLiftedState S L))).re = _
    rw [h]; simp [Complex.mul_re, Complex.inv_re, Complex.inv_im]; exact Or.inl rfl
  unfold applyOperatorToState heteroKron Matrix.kronecker
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [seedFiberLiftedState_apply, Matrix.blockDiagonal_apply, mul_assoc, mul_comm]
  ring_nf
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring_nf
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [Finset.sum_comm, ← mul_assoc]
  congr 1
  exact inv_sqrt_natCast_mul_self (L.q / L.m)

noncomputable def directCoordinateProjStrat (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ProjStrat D.toLDTParameters S.ιA S.ιB := by
  letI := D.toLDTFieldModel
  have hax {ι : Type} [Fintype ι] [DecidableEq ι]
      (M : DirectLdQuestion D → MIPStarRE.Quantum.Measurement (DirectLdAnswer D) ι)
      (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
      AxisParallelMeasurementReparamInvariant D.toLDTParameters
        (fun line => ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas (M (directAxisQuestionOf D line)) (hM _))
          (directAxisAnswerReadout D r line)) := by
    intro line t f
    simp only [ProjMeas.postprocess, SubMeas.postprocess_outcome, matrixMeasurementToLDTProjMeas_outcome]
    rw [directAxisQuestionOf_rebase]
    congr 1; ext ans; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [directAxisAnswerReadout_rebase]
    exact (AxisLinePolynomial.reparamAtEquiv t).injective.eq_iff
  have hdg {ι : Type} [Fintype ι] [DecidableEq ι]
      (M : DirectLdQuestion D → MIPStarRE.Quantum.Measurement (DirectLdAnswer D) ι)
      (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
      DiagonalMeasurementReparamInvariant D.toLDTParameters
        (fun line => ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas (M (directDiagonalQuestionOf D line)) (hM _))
          (directDiagonalAnswerReadout D r line)) := by
    classical
    intro line t f
    simp only [ProjMeas.postprocess, SubMeas.postprocess_outcome, matrixMeasurementToLDTProjMeas_outcome]
    rw [directDiagonalQuestionOf_rebase]
    congr 1; ext ans
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [directDiagonalAnswerReadout_rebase]
    exact (DiagonalLinePolynomial.reparamAtEquiv t).injective.eq_iff
  exact
    { state := strategyQuantumState S
      isNormalized := strategyQuantumState_isNormalized S
      pointMeasurementA := fun u => ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas (S.A (directPointQuestionOf D u)) (hS.1 _))
        (directPointAnswerReadout D r)
      axisParallelMeasurementA := fun line => ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas (S.A (directAxisQuestionOf D line)) (hS.1 _))
        (directAxisAnswerReadout D r line)
      axisParallelReparamInvariantA := hax S.A hS.1
      diagonalMeasurementA := fun line => ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas (S.A (directDiagonalQuestionOf D line)) (hS.1 _))
        (directDiagonalAnswerReadout D r line)
      diagonalReparamInvariantA := hdg S.A hS.1
      pointMeasurementB := fun u => ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas (S.B (directPointQuestionOf D u)) (hS.2 _))
        (directPointAnswerReadout D r)
      axisParallelMeasurementB := fun line => ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas (S.B (directAxisQuestionOf D line)) (hS.2 _))
        (directAxisAnswerReadout D r line)
      axisParallelReparamInvariantB := hax S.B hS.2
      diagonalMeasurementB := fun line => ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas (S.B (directDiagonalQuestionOf D line)) (hS.2 _))
        (directDiagonalAnswerReadout D r line)
      diagonalReparamInvariantB := hdg S.B hS.2 }

theorem ldStrategyToDirect_value_eq (L : LdParams) (S : Strategy (ldGame L)) :
    (ldStrategyToDirect L S).value = S.value := by
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  have hcl (t : LdType) (s : DirectLdSpace L.toDirectLdParams) (r : Fin (L.q / L.m)) :
      ldCL L t (ldSpaceOfDirectResidue L (directLdMap L.toDirectLdParams t s) r) =
        ldCL L t (ldSpaceOfDirectResidue L s r) := by
    cases t <;> funext idx <;> rcases idx with (j | ⟨⟩) | j
    · rfl
    · rfl
    · rfl
    · simp only [ldCL, ldALineCL, ldSpaceOfDirectResidue_point, ldSpaceOfDirectResidue_seed,
        directLdMap, chiIndex_seedOfIndexResidue]
      exact congrFun (lineRepMap_apply_self _ _) j
    · rfl
    · rfl
    · simp only [ldCL, ldDLineCL, ldSpaceOfDirectResidue_point, ldSpaceOfDirectResidue_seed,
        ldSpaceOfDirectResidue_direction, directLdMap, chiIndex_seedOfIndexResidue]
      change lineRepMap (directPrefixProjection s.index (directPrefixProjection s.index s.direction))
          (lineRepMap (directPrefixProjection s.index s.direction) s.point) j = _
      rw [directPrefixProjection_idem]
      exact congrFun (lineRepMap_apply_self _ _) j
    · rfl
    · simp only [ldCL, ldDLineCL, ldSpaceOfDirectResidue_seed, ldSpaceOfDirectResidue_direction,
        directLdMap, chiIndex_seedOfIndexResidue]
      exact congrFun (directPrefixProjection_idem L.toDirectLdParams s.index s.direction) j
  let ldAcc (x y : LdQuestion L) : ℝ :=
    ∑ a : LdAnswer L, ∑ b : LdAnswer L, if ldWinPredicate L x y a b then outcomeWeight S x y a b else 0
  let dirAcc (x y : DirectLdQuestion L.toDirectLdParams) : ℝ :=
    ∑ a, ∑ b, if directLdWinPredicate L.toDirectLdParams x y a b then
      outcomeWeight (ldStrategyToDirect L S) x y a b else 0
  change avgOver (directLdQuestionDistribution L.toDirectLdParams) (fun xy => dirAcc xy.1 xy.2) =
    avgOver (ldQuestionDistribution L) (fun xy => ldAcc xy.1 xy.2)
  unfold directLdQuestionDistribution ldQuestionDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map, avgOver_uniform_equiv (ldQuestionSeedFiberEquiv L)]
  have hsymm (b : ((LdType × LdType) × DirectLdSpace L.toDirectLdParams) × Fin (L.q / L.m)) :
      (ldQuestionSeedFiberEquiv L).symm b = (b.1.1, ldSpaceOfDirectResidue L b.1.2 b.2) := rfl
  simp only [hsymm]
  rw [avgOver_uniform_prod (fun (src : (LdType × LdType) × DirectLdSpace L.toDirectLdParams)
      (r : Fin (L.q / L.m)) =>
      ldAcc (src.1.1, ldCL L src.1.1 (ldSpaceOfDirectResidue L src.2 r))
        (src.1.2, ldCL L src.1.2 (ldSpaceOfDirectResidue L src.2 r)))]
  refine avgOver_congr _ _ _ fun ⟨⟨tA, tB⟩, s⟩ => ?_
  rw [avgOver_uniform_eq_inv_card_mul_sum]
  dsimp only [dirAcc, ldAcc]
  have hwin (r : Fin (L.q / L.m)) (a b : DirectLdAnswer L.toDirectLdParams) :
      directLdWinPredicate L.toDirectLdParams (tA, directLdMap L.toDirectLdParams tA s)
          (tB, directLdMap L.toDirectLdParams tB s) a b =
        ldWinPredicate L (tA, ldCL L tA (ldSpaceOfDirectResidue L s r))
          (tB, ldCL L tB (ldSpaceOfDirectResidue L s r))
          ((ldDirectAnswerEquiv L).symm a) ((ldDirectAnswerEquiv L).symm b) := by
    rw [← ldWinPredicate_parse, parseLdQuestion_ldCL_ofDirectResidue,
      parseLdQuestion_ldCL_ofDirectResidue, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hrhs (r : Fin (L.q / L.m)) :
      (∑ a : LdAnswer L, ∑ b : LdAnswer L,
        if ldWinPredicate L (tA, ldCL L tA (ldSpaceOfDirectResidue L s r))
            (tB, ldCL L tB (ldSpaceOfDirectResidue L s r)) a b then
          outcomeWeight S (tA, ldCL L tA (ldSpaceOfDirectResidue L s r))
            (tB, ldCL L tB (ldSpaceOfDirectResidue L s r)) a b else 0) =
      ∑ a' : DirectLdAnswer L.toDirectLdParams, ∑ b' : DirectLdAnswer L.toDirectLdParams,
        if directLdWinPredicate L.toDirectLdParams (tA, directLdMap L.toDirectLdParams tA s)
            (tB, directLdMap L.toDirectLdParams tB s) a' b' then
          outcomeWeight S (tA, ldCL L tA (ldSpaceOfDirectResidue L s r))
            (tB, ldCL L tB (ldSpaceOfDirectResidue L s r))
            ((ldDirectAnswerEquiv L).symm a') ((ldDirectAnswerEquiv L).symm b') else 0 := by
    rw [← Equiv.sum_comp (ldDirectAnswerEquiv L).symm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← Equiv.sum_comp (ldDirectAnswerEquiv L).symm]
    exact Finset.sum_congr rfl fun b' _ => by rw [hwin]
  have hsd (t : LdType) (r : Fin (L.q / L.m)) :
      seededLdQuestion L (t, directLdMap L.toDirectLdParams t s) r =
        ((t, ldCL L t (ldSpaceOfDirectResidue L s r)) : (ldGame L).QuestionA) :=
    congrArg (t, ·) (hcl t s r)
  have hsdB (t : LdType) (r : Fin (L.q / L.m)) :
      seededLdQuestion L (t, directLdMap L.toDirectLdParams t s) r =
        ((t, ldCL L t (ldSpaceOfDirectResidue L s r)) : (ldGame L).QuestionB) :=
    congrArg (t, ·) (hcl t s r)
  have hbw (a' b' : DirectLdAnswer L.toDirectLdParams) (r : Fin (L.q / L.m)) :
      outcomeWeight S (seededLdQuestion L (tA, directLdMap L.toDirectLdParams tA s) r)
          (seededLdQuestion L (tB, directLdMap L.toDirectLdParams tB s) r)
          ((ldDirectAnswerEquiv L).symm a') ((ldDirectAnswerEquiv L).symm b') =
        outcomeWeight S (tA, ldCL L tA (ldSpaceOfDirectResidue L s r))
          (tB, ldCL L tB (ldSpaceOfDirectResidue L s r))
          ((ldDirectAnswerEquiv L).symm a') ((ldDirectAnswerEquiv L).symm b') := by
    rw [hsd, hsdB]
  rw [Finset.sum_congr rfl fun r _ => hrhs r, Finset.mul_sum]
  calc
    (∑ a', ∑ b', if directLdWinPredicate L.toDirectLdParams (tA, directLdMap L.toDirectLdParams tA s)
          (tB, directLdMap L.toDirectLdParams tB s) a' b' then
        outcomeWeight (ldStrategyToDirect L S) (tA, directLdMap L.toDirectLdParams tA s)
          (tB, directLdMap L.toDirectLdParams tB s) a' b' else 0) =
      ∑ a', ∑ b', ∑ r : Fin (L.q / L.m),
        (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
          if directLdWinPredicate L.toDirectLdParams (tA, directLdMap L.toDirectLdParams tA s)
              (tB, directLdMap L.toDirectLdParams tB s) a' b' then
            outcomeWeight S (tA, ldCL L tA (ldSpaceOfDirectResidue L s r))
              (tB, ldCL L tB (ldSpaceOfDirectResidue L s r))
              ((ldDirectAnswerEquiv L).symm a') ((ldDirectAnswerEquiv L).symm b') else 0 :=
        Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => by
          by_cases hc : directLdWinPredicate L.toDirectLdParams (tA, directLdMap L.toDirectLdParams tA s)
              (tB, directLdMap L.toDirectLdParams tB s) a' b' = true
          · rw [if_pos hc]
            simp_rw [if_pos hc]
            rw [← Finset.mul_sum, ldStrategyToDirect_bornWeight]
            congr 1; exact Finset.sum_congr rfl fun r _ => hbw a' b' r
          · rw [if_neg hc]; symm
            exact Finset.sum_eq_zero fun _ _ => by rw [if_neg hc, mul_zero]
    _ = _ := by
      rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm

/-! ## Branch comparison, diagonal recursion, and pass conversion -/

theorem qBipartiteConsDefect_le_directRejectedMass
    (D : DirectLdParams) (S : Strategy (directLdGame D)) (hS : S.IsProjective)
    {Outcome : Type*} [Fintype Outcome] (x y : DirectLdQuestion D)
    (readA readB : DirectLdAnswer D → Outcome)
    (hwin : ∀ a b, directLdWinPredicate D x y a b = true → readA a = readB b) :
    qBipartiteConsDefect (strategyQuantumState S)
        (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas
        (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas ≤
      directRejectedMass D S x y := by
  classical
  have hmatch : qBipartiteMatchMass (strategyQuantumState S)
        (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas
        (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas =
      ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
        if readA a = readB b then outcomeWeight S x y a b else 0 := by
    unfold qBipartiteMatchMass
    simp_rw [directPostprocessBornWeight D S hS x y readA readB, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    exact Finset.sum_congr rfl fun b _ => by by_cases h : readA a = readB b <;> simp [h, eq_comm]
  have htot : ev (strategyQuantumState S)
      (opTensor
        (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas.total
        (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas.total) = 1 := by
    change ev (strategyQuantumState S) (Matrix.kroneckerMap (· * ·) (1 : Op S.ιA) (1 : Op S.ιB)) = 1
    rw [Matrix.one_kronecker_one]
    exact ev_one_of_isNormalized _ (strategyQuantumState_isNormalized S)
  simp only [qBipartiteConsDefect]
  refine max_le (directRejectedMass_nonneg D S x y) ?_
  rw [htot, hmatch, ← outcomeWeight_sum_eq_one S x y, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have hw := outcomeWeight_nonneg S x y a b
  by_cases hacc : directLdWinPredicate D x y a b = true
  · simp [hacc, hwin a b hacc]
  · rw [if_neg hacc]; split_ifs <;> linarith

theorem directLdPointValuesOrZero_eq_of_win (D : DirectLdParams)
    (p : Fin D.m → DirectScalarQ D) (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directLdPointQuestionOf D p) (directLdPointQuestionOf D p) a b = true) :
    directLdPointValuesOrZero D a = directLdPointValuesOrZero D b := by
  cases a <;> cases b <;>
    simp_all [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer, directLdPointValuesOrZero]

theorem directAxisAnswerReadout_zeroCoord_eq_of_win (D : DirectLdParams) (r : Fin D.k)
    (line : AxisParallelLine D.toLDTParameters) (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directAxisQuestionOf D line) (directPointQuestionOf D line.base) a b = true) :
    letI := D.toLDTFieldModel
    directAxisAnswerReadout D r line a zeroCoord = directPointAnswerReadout D r b := by
  letI := D.toLDTFieldModel
  cases a with
  | pointVals _ | dlinePolys _ =>
      simp [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer] at hwin
  | alinePolys f =>
    cases b with
    | alinePolys _ | dlinePolys _ =>
        simp [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
          directLdPointQuestionOf, validDirectLdAnswer] at hwin
    | pointVals c =>
      simp only [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer, Bool.and_self, ↓reduceIte] at hwin
      have hcond := @of_decide_eq_true _ (Classical.propDecidable _) hwin
      have hev := hcond (directAxisRebaseParameter D line) (directLineRepParameter_spec _ _) r
      simp only [directAxisAnswerReadout, directPointAnswerReadout, directLdPointValuesOrZero]
      rw [AxisLinePolynomial.reparamAt_apply_zero, directAxisAnswerEquiv_apply, hev]

theorem directPointAnswerReadout_eq_axis_zeroCoord_of_win (D : DirectLdParams) (r : Fin D.k)
    (line : AxisParallelLine D.toLDTParameters) (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directPointQuestionOf D line.base) (directAxisQuestionOf D line) a b = true) :
    letI := D.toLDTFieldModel
    directPointAnswerReadout D r a = directAxisAnswerReadout D r line b zeroCoord :=
  (directAxisAnswerReadout_zeroCoord_eq_of_win D r line b a
    ((directLdWinPredicate_symm D _ _ b a).trans hwin)).symm

theorem directDiagonalAnswerReadout_zeroCoord_eq_of_win (D : DirectLdParams) (r : Fin D.k)
    (line : DiagonalLine D.toLDTParameters) (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directDiagonalQuestionOf D line) (directPointQuestionOf D line.base) a b = true) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerReadout D r line a zeroCoord = directPointAnswerReadout D r b := by
  letI := D.toLDTFieldModel
  cases a with
  | pointVals _ | alinePolys _ =>
      simp [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer] at hwin
  | dlinePolys f =>
    cases b with
    | alinePolys _ | dlinePolys _ =>
        simp [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
          directLdPointQuestionOf, validDirectLdAnswer] at hwin
    | pointVals c =>
      simp only [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer, Bool.and_self, ↓reduceIte] at hwin
      have hcond := @of_decide_eq_true _ (Classical.propDecidable _) hwin
      simp only [directDiagonalAnswerReadout, directPointAnswerReadout, directLdPointValuesOrZero]
      by_cases hdir : ldtPointToDirect D line.direction = 0
      · have hbase := directLineRepParameter_spec (ldtPointToDirect D line.direction) (ldtPointToDirect D line.base)
        rw [hdir, smul_zero, add_zero] at hbase
        rw [hdir] at hcond
        have hev : evalCoefficient (f r) 0 = c r :=
          hcond 0 (by dsimp only; rw [smul_zero, add_zero]; exact hbase) r
        simp only [hdir, ↓reduceIte]
        rw [constantDiagonalAnswer_apply, hev]
      · have hev := hcond (directDiagonalRebaseParameter D line) (directLineRepParameter_spec _ _) r
        simp only [hdir, ↓reduceIte]
        rw [DiagonalLinePolynomial.reparamAt_apply_zero, directDiagonalAnswerEquiv_apply, hev]

theorem directPointAnswerReadout_eq_diagonal_zeroCoord_of_win (D : DirectLdParams) (r : Fin D.k)
    (line : DiagonalLine D.toLDTParameters) (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directPointQuestionOf D line.base) (directDiagonalQuestionOf D line) a b = true) :
    letI := D.toLDTFieldModel
    directPointAnswerReadout D r a = directDiagonalAnswerReadout D r line b zeroCoord :=
  (directDiagonalAnswerReadout_zeroCoord_eq_of_win D r line b a
    ((directLdWinPredicate_symm D _ _ b a).trans hwin)).symm

section BranchBounds

variable (D : DirectLdParams) (S : Strategy (directLdGame D)) (hS : S.IsProjective) (r : Fin D.k)

theorem directCoordinate_point_agreement_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).pointAgreementFailureProbability ≤
      directLdBranchRejectionProbability D S (.point, .point) := by
  letI := D.toLDTFieldModel
  unfold ProjStrat.pointAgreementFailureProbability bipartiteConsError
  rw [directLdBranchRejectionProbability_eq_avgOver]
  refine (avgOver_mono _ _ _ fun u => qBipartiteConsDefect_le_directRejectedMass D S hS
    (directPointQuestionOf D u) (directPointQuestionOf D u)
    (directPointAnswerReadout D r) (directPointAnswerReadout D r)
    fun a b hab => congrArg (fun v => directScalarEquiv D (v r))
      (directLdPointValuesOrZero_eq_of_win D (ldtPointToDirect D u) a b hab)).trans_eq ?_
  let f := fun p => directRejectedMass D S (directLdPointQuestionOf D p) (directLdPointQuestionOf D p)
  exact (avgOver_uniform_equiv (directPointEquiv D) f).symm.trans
    ((avgOver_uniform_fst f).symm.trans
      ((avgOver_uniform_equiv_fst (directLdSpaceSplitEquiv D) fun pi => f pi.1).symm.trans
        (avgOver_congr _ _ _ fun _ => rfl)))

theorem avgOver_axis_sample_eq (f : (Fin D.m → DirectScalarQ D) × Fin D.m → ℝ) :
    avgOver (uniformDistribution (AxisParallelTestSample D.toLDTParameters))
        (fun s => f (ldtPointToDirect D s.1, Fin.rev s.2)) =
      avgOver (uniformDistribution (DirectLdSpace D)) (fun s => f (s.point, s.index)) := by
  refine (avgOver_uniform_equiv ((directPointEquiv D).prodCongr Fin.revPerm) f).symm.trans ?_
  exact (avgOver_uniform_equiv_fst (directLdSpaceSplitEquiv D) f).symm.trans
    (avgOver_congr _ _ _ fun _ => rfl)

theorem directCoordinate_axis_line_point_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).axisParallelLineLeftPointRightFailureProbability ≤
      directLdBranchRejectionProbability D S (.aline, .point) := by
  letI := D.toLDTFieldModel
  unfold ProjStrat.axisParallelLineLeftPointRightFailureProbability bipartiteConsError
  rw [directLdBranchRejectionProbability_eq_avgOver]
  refine (avgOver_mono _ _ _ fun s => ?_).trans_eq
    (avgOver_axis_sample_eq D fun pi => directRejectedMass D S
      (.aline, ⟨lineRepMap (coordinateDirection pi.2) pi.1, pi.2, 0⟩) (directLdPointQuestionOf D pi.1))
  have h := qBipartiteConsDefect_le_directRejectedMass D S hS
    (directAxisQuestionOf D ⟨s.1, s.2⟩) (directPointQuestionOf D s.1)
    (fun a => directAxisAnswerReadout D r ⟨s.1, s.2⟩ a zeroCoord) (directPointAnswerReadout D r)
    (directAxisAnswerReadout_zeroCoord_eq_of_win D r ⟨s.1, s.2⟩)
  change qBipartiteConsDefect (strategyQuantumState S)
    (postprocess (ProjMeas.postprocess
      (matrixMeasurementToLDTProjMeas (S.A (directAxisQuestionOf D ⟨s.1, s.2⟩)) (hS.1 _))
      (directAxisAnswerReadout D r ⟨s.1, s.2⟩)).toSubMeas (fun g => g zeroCoord))
    (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.B (directPointQuestionOf D s.1)) (hS.2 _))
      (directPointAnswerReadout D r)).toSubMeas ≤ _
  simp only [ProjMeas.postprocess_toSubMeas, SubMeas.postprocess_comp] at h ⊢
  exact h

theorem directCoordinate_axis_point_line_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).axisParallelPointLeftLineRightFailureProbability ≤
      directLdBranchRejectionProbability D S (.point, .aline) := by
  letI := D.toLDTFieldModel
  unfold ProjStrat.axisParallelPointLeftLineRightFailureProbability bipartiteConsError
  rw [directLdBranchRejectionProbability_eq_avgOver]
  refine (avgOver_mono _ _ _ fun s => ?_).trans_eq
    (avgOver_axis_sample_eq D fun pi => directRejectedMass D S
      (directLdPointQuestionOf D pi.1) (.aline, ⟨lineRepMap (coordinateDirection pi.2) pi.1, pi.2, 0⟩))
  have h := qBipartiteConsDefect_le_directRejectedMass D S hS
    (directPointQuestionOf D s.1) (directAxisQuestionOf D ⟨s.1, s.2⟩)
    (directPointAnswerReadout D r) (fun b => directAxisAnswerReadout D r ⟨s.1, s.2⟩ b zeroCoord)
    (directPointAnswerReadout_eq_axis_zeroCoord_of_win D r ⟨s.1, s.2⟩)
  change qBipartiteConsDefect (strategyQuantumState S)
    (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.A (directPointQuestionOf D s.1)) (hS.1 _))
      (directPointAnswerReadout D r)).toSubMeas
    (postprocess (ProjMeas.postprocess
      (matrixMeasurementToLDTProjMeas (S.B (directAxisQuestionOf D ⟨s.1, s.2⟩)) (hS.2 _))
      (directAxisAnswerReadout D r ⟨s.1, s.2⟩)).toSubMeas (fun g => g zeroCoord)) ≤ _
  simp only [ProjMeas.postprocess_toSubMeas, SubMeas.postprocess_comp] at h ⊢
  exact h

def restrictedDirectionEquiv (j : Fin D.m) :
    (Fin D.m → DirectScalarQ D) ≃
      (Fin (j.val + 1) → Fq D.toLDTParameters) × (Fin (Fin.rev j).val → DirectScalarQ D) where
  toFun v :=
    (fun c => directScalarEquiv D (v ⟨D.m - 1 - c.val, by have := D.hm; omega⟩),
     fun c => v ⟨c.val, by have := c.isLt; have := Fin.val_rev j; omega⟩)
  invFun x c :=
    if h : c.val < (Fin.rev j).val then x.2 ⟨c.val, h⟩
    else (directScalarEquiv D).symm (x.1 ⟨D.m - 1 - c.val, by
      have := c.isLt; have := j.isLt; have := Fin.val_rev j; omega⟩)
  left_inv v := by
    funext c; by_cases h : c.val < (Fin.rev j).val
    · simp only [dif_pos h, Fin.eta]
    · simp only [dif_neg h, Equiv.symm_apply_apply]
      exact congrArg v (Fin.ext (by change D.m - 1 - (D.m - 1 - c.val) = c.val; have := c.isLt; have := D.hm; omega))
  right_inv x := Prod.ext
    (funext fun c => by
      have := c.isLt; have := j.isLt; have := Fin.val_rev j
      have hc : ¬ (D.m - 1 - c.val < (Fin.rev j).val) := by omega
      simp only [dif_neg hc, Equiv.apply_symm_apply]
      exact congrArg x.1 (Fin.ext (by change D.m - 1 - (D.m - 1 - c.val) = c.val; omega)))
    (funext fun c => by simp only [dif_pos c.isLt, Fin.eta])

theorem avgOver_restrictedDiagonalSample_eq (j : Fin D.m)
    (H : (Fin D.m → DirectScalarQ D) → (Fin D.m → DirectScalarQ D) → ℝ) :
    letI := D.toLDTFieldModel
    avgOver (uniformDistribution (RestrictedDiagonalSample D.toLDTParameters j))
        (fun s => H (ldtPointToDirect D s.1) (ldtPointToDirect D (extendRestrictedDirection j s.2))) =
      avgOver (uniformDistribution ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
        (fun pv => H pv.1 (directPrefixProjection (Fin.rev j) pv.2)) := by
  letI := D.toLDTFieldModel
  rw [avgOver_uniform_prod (fun u free => H (ldtPointToDirect D u) (ldtPointToDirect D (extendRestrictedDirection j free))),
    avgOver_uniform_prod (fun p v => H p (directPrefixProjection (Fin.rev j) v)),
    avgOver_uniform_equiv (directPointEquiv D)]
  refine avgOver_congr _ _ _ fun u => ?_
  rw [← avgOver_uniform_equiv_fst (restrictedDirectionEquiv D j)
    (fun free => H (ldtPointToDirect D u) (ldtPointToDirect D (extendRestrictedDirection j free)))]
  refine avgOver_congr _ _ _ fun v => congrArg (H (ldtPointToDirect D u)) (funext fun c => ?_)
  by_cases hc : c.val < (Fin.rev j).val
  · have := j.isLt
    have hgt : ¬ (Fin.rev c).val ≤ j.val := by rw [Fin.val_rev] at hc ⊢; omega
    simp only [ldtPointToDirect, directPointEquiv_symm_apply, extendRestrictedDirection,
      dif_neg hgt, directPrefixProjection, if_pos hc]
    exact (FieldModel.equiv (q := D.q)).symm_apply_apply 0
  · have := Fin.val_rev j; have := Fin.val_rev c; have := c.isLt; have := D.hm
    have hle : (Fin.rev c).val ≤ j.val := by omega
    simp only [ldtPointToDirect, directPointEquiv_symm_apply, extendRestrictedDirection,
      dif_pos hle, restrictedDirectionEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply,
      directPrefixProjection, if_neg hc]
    exact congrArg v (Fin.ext (by change D.m - 1 - (Fin.rev c).val = c.val; omega))

theorem diagonal_sum_le (dd : (Fin D.m → DirectScalarQ D) → ℝ)
    (rj : Fin D.m → (Fin D.m → DirectScalarQ D) → ℝ)
    (hdd0 : ∀ v, 0 ≤ dd v) (hrj : ∀ i v, 0 ≤ rj i v)
    (hdd : ∀ v, dd v ≤ rj (directDiagonalIndexOf D v) v) :
    ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun v => dd (directPrefixProjection i v)) ≤
      2 * ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun v => rj i (directPrefixProjection i v)) := by
  let q : ℝ := Fintype.card (DirectScalarQ D)
  have hqNat : 2 ≤ Fintype.card (DirectScalarQ D) := Fintype.one_lt_card
  have hq : 2 ≤ q := by dsimp [q]; exact_mod_cast hqNat
  have hq0 : 0 < q := by linarith
  have hqinv : q⁻¹ ≤ 1 / 2 := (inv_anti₀ (by norm_num) hq).trans_eq (by norm_num)
  let t (i : Fin D.m) := avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
    fun v => dd (directPrefixProjection i v)
  let r' (i : Fin D.m) := avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
    fun v => rj i (directPrefixProjection i v)
  have hstep (i i' : Fin D.m) (hi : i'.val = i.val + 1) : t i ≤ r' i + q⁻¹ * t i' := by
    have hcz : avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun v => if v i = 0 then dd (directPrefixProjection i' v) else 0) = q⁻¹ * t i' := by
      have hsh (c : DirectScalarQ D) :
          (∑ v : Fin D.m → DirectScalarQ D, if v i = c then dd (directPrefixProjection i' v) else 0) =
          ∑ v : Fin D.m → DirectScalarQ D, if v i = 0 then dd (directPrefixProjection i' v) else 0 := by
        refine Fintype.sum_equiv (Equiv.addRight ((-c) • Pi.single i (1 : DirectScalarQ D))) _ _ fun v => ?_
        have hp : directPrefixProjection i' (v + (-c) • Pi.single i 1) = directPrefixProjection i' v := by
          funext j; unfold directPrefixProjection
          by_cases hj : j.val < i'.val
          · simp [hj]
          · simp [hj, Pi.single_eq_of_ne (show j ≠ i from fun h => hj (by omega))]
        rw [Equiv.coe_addRight, hp]
        simp [add_neg_eq_zero]
      have htot : (∑ v : Fin D.m → DirectScalarQ D, dd (directPrefixProjection i' v)) =
          q * ∑ v, if v i = 0 then dd (directPrefixProjection i' v) else 0 := by
        calc _ = ∑ v, ∑ c : DirectScalarQ D, if v i = c then dd (directPrefixProjection i' v) else 0 :=
              Finset.sum_congr rfl fun v _ => by rw [Finset.sum_ite_eq]; simp
          _ = ∑ c, ∑ v, if v i = c then dd (directPrefixProjection i' v) else 0 := Finset.sum_comm
          _ = ∑ _c : DirectScalarQ D, ∑ v, if v i = 0 then dd (directPrefixProjection i' v) else 0 :=
              Finset.sum_congr rfl fun c _ => hsh c
          _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [t, q] at htot hq0 ⊢
      rw [avgOver_uniform_eq_inv_card_mul_sum, avgOver_uniform_eq_inv_card_mul_sum, htot]
      field_simp [hq0.ne']
    have hsp (v : Fin D.m → DirectScalarQ D) : dd (directPrefixProjection i v) =
        (if v i = 0 then 0 else dd (directPrefixProjection i v)) +
        (if v i = 0 then dd (directPrefixProjection i' v) else 0) := by
      by_cases hv : v i = 0
      · rw [if_pos hv, if_pos hv, zero_add]
        congr 1; funext j; unfold directPrefixProjection
        by_cases hj : j.val < i.val
        · rw [if_pos hj, if_pos (by omega)]
        · by_cases hj' : j.val < i'.val
          · rw [if_neg hj, if_pos hj', show j = i from Fin.ext (by omega), hv]
          · rw [if_neg hj, if_neg hj']
      · simp [hv]
    dsimp only [t, r']
    rw [avgOver_congr _ _ _ hsp, avgOver_add, hcz]
    refine add_le_add (avgOver_mono _ _ _ fun v => ?_) le_rfl
    by_cases hv : v i = 0
    · rw [if_pos hv]; exact hrj i _
    · rw [if_neg hv]
      exact (hdd _).trans_eq (by rw [directDiagonalIndexOf_prefixProjection D i v hv])
  have hlast (i : Fin D.m) (hi : i.val + 1 = D.m) : t i ≤ r' i := by
    refine avgOver_mono _ _ _ fun v => (hdd _).trans_eq ?_
    suffices h : directDiagonalIndexOf D (directPrefixProjection i v) = i by rw [h]
    by_cases hv : v i = 0
    · have hz : directPrefixProjection i v = 0 := by
        funext j; unfold directPrefixProjection
        split_ifs with hj
        · rfl
        · rw [show j = i from Fin.ext (by have := j.isLt; omega), hv]; rfl
      have hne : ¬ (directionSupport D 0).Nonempty := fun ⟨j, hj⟩ => (Finset.mem_filter.mp hj).2 rfl
      rw [hz]; unfold directDiagonalIndexOf; rw [dif_neg hne]
      exact Fin.ext (by rw [Fin.val_rev]; simp [DirectLdParams.firstIndex]; omega)
    · exact directDiagonalIndexOf_prefixProjection D i v hv
  let succSum (i : Fin D.m) : ℝ := ∑ i' : Fin D.m, if i'.val = i.val + 1 then t i' else 0
  have hbnd (i : Fin D.m) : t i ≤ r' i + q⁻¹ * succSum i := by
    by_cases h : i.val + 1 < D.m
    · have hs : succSum i = t ⟨i.val + 1, h⟩ := by
        dsimp only [succSum]
        rw [Finset.sum_eq_single ⟨i.val + 1, h⟩
          (fun b _ hb => if_neg fun hb' => hb (Fin.ext hb'))
          (fun ha => absurd (Finset.mem_univ _) ha)]
        simp
      rw [hs]; exact hstep i ⟨i.val + 1, h⟩ rfl
    · have hs : succSum i = 0 := Finset.sum_eq_zero fun i' _ =>
        if_neg fun h' => by have := i.isLt; have := i'.isLt; omega
      rw [hs, mul_zero, add_zero]; exact hlast i (by have := i.isLt; omega)
  have ht0 (i) : 0 ≤ t i := avgOver_nonneg _ _ fun _ => hdd0 _
  have hss : ∑ i, succSum i ≤ ∑ i, t i := by
    dsimp only [succSum]; rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i' _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : (Finset.univ.filter fun i : Fin D.m => i'.val = i.val + 1).card ≤ 1 := by
      rw [Finset.card_le_one]; intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact Fin.ext (by omega)
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (ht0 i')).trans_eq (one_mul _)
  have htot : ∑ i, t i ≤ ∑ i, r' i + q⁻¹ * ∑ i, t i :=
    (Finset.sum_le_sum fun i _ => hbnd i).trans
      (by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; linarith [mul_le_mul_of_nonneg_left hss (inv_nonneg.mpr hq0.le)])
  have hhalf : q⁻¹ * ∑ i, t i ≤ (1 / 2) * ∑ i, t i :=
    mul_le_mul_of_nonneg_right hqinv (Finset.sum_nonneg fun i _ => ht0 i)
  dsimp only [t, r'] at htot hhalf; linarith

theorem sum_rev_avgOver_eq
    (F : (Fin D.m → DirectScalarQ D) → Fin D.m → (Fin D.m → DirectScalarQ D) → ℝ) :
    ∑ j : Fin D.m, avgOver (uniformDistribution ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
        (fun pv => F pv.1 (Fin.rev j) (directPrefixProjection (Fin.rev j) pv.2)) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun p =>
        ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun v => F p i (directPrefixProjection i v)) := by
  rw [avgOver_sum, ← Equiv.sum_comp Fin.revPerm (fun i =>
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun p =>
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun v => F p i (directPrefixProjection i v))]
  exact Finset.sum_congr rfl fun j _ =>
    avgOver_uniform_prod (fun p v => F p (Fin.rev j) (directPrefixProjection (Fin.rev j) v))

theorem avgOver_branch_index_eq (types : LdType × LdType) :
    directLdBranchRejectionProbability D S types =
      (D.m : ℝ)⁻¹ * avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun p =>
        ∑ i : Fin D.m, avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun v =>
          directRejectedMass D S (types.1, directLdMap D types.1 ⟨p, i, v⟩)
            (types.2, directLdMap D types.2 ⟨p, i, v⟩) := by
  rw [directLdBranchRejectionProbability_eq_avgOver, avgOver_uniform_equiv_prod (directLdSpaceIndexEquiv D),
    avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_fin, avgOver_sum]
  exact congrArg _ (Finset.sum_congr rfl fun i _ =>
    avgOver_uniform_prod (fun p v => directRejectedMass D S
      (types.1, directLdMap D types.1 ⟨p, i, v⟩) (types.2, directLdMap D types.2 ⟨p, i, v⟩)))

theorem directCoordinate_diagonal_line_point_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).diagonalLineLeftPointRightFailureProbability ≤
      2 * directLdBranchRejectionProbability D S (.dline, .point) := by
  letI := D.toLDTFieldModel
  let dd (p v : Fin D.m → DirectScalarQ D) : ℝ :=
    qBipartiteConsDefect (directCoordinateProjStrat D S hS r).state
      (postprocess ((directCoordinateProjStrat D S hS r).diagonalMeasurementA
        (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩)).toSubMeas (fun g => g zeroCoord))
      ((directCoordinateProjStrat D S hS r).pointMeasurementB (directPointEquiv D p)).toSubMeas
  have hdd (p v) : dd p v ≤ directRejectedMass D S (.dline, ⟨lineRepMap v p, directDiagonalIndexOf D v, v⟩)
      (directLdPointQuestionOf D p) := by
    have h := qBipartiteConsDefect_le_directRejectedMass D S hS
      (directDiagonalQuestionOf D (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))
      (directPointQuestionOf D (directPointEquiv D p))
      (fun a => directDiagonalAnswerReadout D r (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩) a zeroCoord)
      (directPointAnswerReadout D r)
      (directDiagonalAnswerReadout_zeroCoord_eq_of_win D r _)
    dsimp only [dd]
    change qBipartiteConsDefect (strategyQuantumState S)
      (postprocess (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas
          (S.A (directDiagonalQuestionOf D (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))) (hS.1 _))
        (directDiagonalAnswerReadout D r (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))).toSubMeas
        (fun g => g zeroCoord))
      (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas (S.B (directPointQuestionOf D (directPointEquiv D p))) (hS.2 _))
        (directPointAnswerReadout D r)).toSubMeas ≤ _
    simp only [ProjMeas.postprocess_toSubMeas, SubMeas.postprocess_comp] at h ⊢
    exact h.trans_eq (by simp [directDiagonalQuestionOf, ldtDiagonalLineOf, ldtPointToDirect])
  have hterm (j : Fin D.m) :
      bipartiteConsError (directCoordinateProjStrat D S hS r).state
          (uniformDistribution (RestrictedDiagonalSample D.toLDTParameters j))
          ((directCoordinateProjStrat D S hS r).diagonalLineAnswerFamilyA j)
          ((directCoordinateProjStrat D S hS r).diagonalPointAnswerFamilyB j) =
        avgOver (uniformDistribution ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
          fun pv => dd pv.1 (directPrefixProjection (Fin.rev j) pv.2) := by
    rw [← avgOver_restrictedDiagonalSample_eq D j dd]
    exact avgOver_congr _ _ _ fun s => by
      dsimp only [dd]; simp [ldtDiagonalLineOf, ldtPointToDirect]; rfl
  unfold ProjStrat.diagonalLineLeftPointRightFailureProbability
  rw [avgOver_branch_index_eq, Finset.sum_congr rfl fun j _ => hterm j,
    sum_rev_avgOver_eq D fun p _ v => dd p v, one_div]
  have hm := avgOver_mono (uniformDistribution (Fin D.m → DirectScalarQ D)) _ _ fun p =>
    diagonal_sum_le D (dd p) (fun i v => directRejectedMass D S (.dline, ⟨lineRepMap v p, i, v⟩) (directLdPointQuestionOf D p))
      (fun _ => qBipartiteConsDefect_nonneg _ _ _) (fun _ _ => directRejectedMass_nonneg D S _ _) (hdd p)
  rw [avgOver_const_mul] at hm
  exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
    (by simp only [directLdMap, directLdPointQuestionOf]; ring)

theorem directCoordinate_diagonal_point_line_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).diagonalPointLeftLineRightFailureProbability ≤
      2 * directLdBranchRejectionProbability D S (.point, .dline) := by
  letI := D.toLDTFieldModel
  let dd (p v : Fin D.m → DirectScalarQ D) : ℝ :=
    qBipartiteConsDefect (directCoordinateProjStrat D S hS r).state
      ((directCoordinateProjStrat D S hS r).pointMeasurementA (directPointEquiv D p)).toSubMeas
      (postprocess ((directCoordinateProjStrat D S hS r).diagonalMeasurementB
        (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩)).toSubMeas (fun g => g zeroCoord))
  have hdd (p v) : dd p v ≤ directRejectedMass D S (directLdPointQuestionOf D p)
      (.dline, ⟨lineRepMap v p, directDiagonalIndexOf D v, v⟩) := by
    have h := qBipartiteConsDefect_le_directRejectedMass D S hS
      (directPointQuestionOf D (directPointEquiv D p))
      (directDiagonalQuestionOf D (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))
      (directPointAnswerReadout D r)
      (fun b => directDiagonalAnswerReadout D r (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩) b zeroCoord)
      (directPointAnswerReadout_eq_diagonal_zeroCoord_of_win D r _)
    dsimp only [dd]
    change qBipartiteConsDefect (strategyQuantumState S)
      (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas (S.A (directPointQuestionOf D (directPointEquiv D p))) (hS.1 _))
        (directPointAnswerReadout D r)).toSubMeas
      (postprocess (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas
          (S.B (directDiagonalQuestionOf D (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))) (hS.2 _))
        (directDiagonalAnswerReadout D r (ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))).toSubMeas
        (fun g => g zeroCoord)) ≤ _
    simp only [ProjMeas.postprocess_toSubMeas, SubMeas.postprocess_comp] at h ⊢
    exact h.trans_eq (by simp [directDiagonalQuestionOf, ldtDiagonalLineOf, ldtPointToDirect])
  have hterm (j : Fin D.m) :
      bipartiteConsError (directCoordinateProjStrat D S hS r).state
          (uniformDistribution (RestrictedDiagonalSample D.toLDTParameters j))
          ((directCoordinateProjStrat D S hS r).diagonalPointAnswerFamilyA j)
          ((directCoordinateProjStrat D S hS r).diagonalLineAnswerFamilyB j) =
        avgOver (uniformDistribution ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
          fun pv => dd pv.1 (directPrefixProjection (Fin.rev j) pv.2) := by
    rw [← avgOver_restrictedDiagonalSample_eq D j dd]
    exact avgOver_congr _ _ _ fun s => by
      dsimp only [dd]; simp [ldtDiagonalLineOf, ldtPointToDirect]; rfl
  unfold ProjStrat.diagonalPointLeftLineRightFailureProbability
  rw [avgOver_branch_index_eq, Finset.sum_congr rfl fun j _ => hterm j,
    sum_rev_avgOver_eq D fun p _ v => dd p v, one_div]
  have hm := avgOver_mono (uniformDistribution (Fin D.m → DirectScalarQ D)) _ _ fun p =>
    diagonal_sum_le D (dd p) (fun i v => directRejectedMass D S (directLdPointQuestionOf D p) (.dline, ⟨lineRepMap v p, i, v⟩))
      (fun _ => qBipartiteConsDefect_nonneg _ _ _) (fun _ _ => directRejectedMass_nonneg D S _ _) (hdd p)
  rw [avgOver_const_mul] at hm
  exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
    (by simp only [directLdMap, directLdPointQuestionOf]; ring)

theorem directCoordinate_passes (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).PassesLowIndividualDegreeTest (3 * ε) := by
  letI := D.toLDTFieldModel
  refine ⟨?_⟩
  rw [ProjStrat.lowIndividualDegreeFailureProbability_eq_role_averages]
  unfold ProjStrat.axisParallelRoleAverage ProjStrat.diagonalRoleAverage
  have hrej : directLdRejectionProbability D S ≤ ε := by
    rw [directLdRejectionProbability_eq_one_sub_value]; linarith
  rw [directLdRejectionProbability, avgOver_ldType_pair] at hrej
  have hnn := directLdBranchRejectionProbability_nonneg D S
  linarith [directCoordinate_axis_line_point_le D S hS r,
    directCoordinate_axis_point_line_le D S hS r,
    directCoordinate_point_agreement_le D S hS r,
    directCoordinate_diagonal_line_point_le D S hS r,
    directCoordinate_diagonal_point_line_le D S hS r,
    hnn (.point, .point), hnn (.point, .aline), hnn (.point, .dline),
    hnn (.aline, .point), hnn (.aline, .aline), hnn (.aline, .dline),
    hnn (.dline, .point), hnn (.dline, .aline), hnn (.dline, .dline)]

end BranchBounds

/-! ## Scalar transport errors and seed-compression error bounds -/

def directLdAuxParameter (D : DirectLdParams) : ℕ := 2560000 * D.m ^ 3 * D.d

theorem directLdAuxParameter_pos (D : DirectLdParams) : 0 < directLdAuxParameter D :=
  Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos D.hm 3)) D.hd

theorem four_hundred_mul_le_directLdAuxParameter (D : DirectLdParams) :
    400 * D.toLDTParameters.m * D.toLDTParameters.d ≤ directLdAuxParameter D :=
  Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) (Nat.le_self_pow (by norm_num) D.m)) le_rfl

noncomputable def transportEnvelope (D : DirectLdParams) (ε : ℝ) : ℝ :=
  Real.rpow ε (1 / 80000) + Real.rpow (D.q : ℝ) (-(1 / 80000)) +
    Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ)))

theorem transportEnvelope_nonneg (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ transportEnvelope D ε := by
  unfold transportEnvelope
  exact add_nonneg (add_nonneg (Real.rpow_nonneg hε _) (Real.rpow_nonneg (by positivity) _))
    (Real.rpow_nonneg (by norm_num) _)

theorem direct_ld_transport_constants_explicit (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    1 ≤ 2500000000 * C₀ ∧ 0 < (1 / 80000 : ℝ) ∧ (1 / 80000 : ℝ) ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
        C₀ * (D.k : ℝ) *
            Real.sqrt (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
              ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) ≤
          deltaLd (2500000000 * C₀) (1 / 80000) ε D.q D.m D.d D.k := by
  refine ⟨by linarith, by norm_num, by norm_num, fun D ε hε0 hε1 => ?_⟩
  have hm1 : (1 : ℝ) ≤ D.m := by exact_mod_cast D.hm
  have hd1 : (1 : ℝ) ≤ D.d := by exact_mod_cast D.hd
  have hk1 : (1 : ℝ) ≤ D.k := by exact_mod_cast D.hk
  have hq1 : (1 : ℝ) ≤ D.q := by exact_mod_cast D.toLDTParameters.hq
  have hT := transportEnvelope_nonneg D hε0.le
  have hx := Real.rpow_nonneg hε0.le (1 / 80000 : ℝ)
  have hy := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ D.q) (-(1 / 80000) : ℝ)
  have hz := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ)))
  have hexp_arg : (directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ 2)) = (D.m : ℝ) * D.d := by
    have hne : (2560000 : ℝ) * ((D.m : ℝ) ^ 2) ≠ 0 := by positivity
    unfold directLdAuxParameter; push_cast; rw [div_eq_iff hne]; ring
  have hpre : Real.sqrt (100000 * ((directLdAuxParameter D : ℝ) ^ 2) * ((D.m : ℝ) ^ 4)) ≤
      820000000 * (D.m : ℝ) ^ 5 * D.d := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 820000000 * (D.m : ℝ) ^ 5 * D.d by positivity)]
    apply Real.sqrt_le_sqrt
    have hK : (directLdAuxParameter D : ℝ) = 2560000 * (D.m : ℝ) ^ 3 * D.d := by
      unfold directLdAuxParameter; push_cast; ring
    rw [hK]
    nlinarith [show (0 : ℝ) ≤ (D.m : ℝ) ^ 10 * (D.d : ℝ) ^ 2 by positivity]
  have henv : Real.sqrt (Real.rpow (3 * ε) (1 / 40000) +
      Real.rpow ((D.d : ℝ) / D.q) (1 / 40000) +
      Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ 2))))) ≤
      3 * (D.d : ℝ) * transportEnvelope D ε := by
    have hb1 : Real.sqrt (Real.rpow (3 * ε) (1 / 40000)) ≤ 3 * Real.rpow ε (1 / 80000) := by
      have e : Real.sqrt (Real.rpow (3 * ε) (1 / 40000)) = Real.rpow (3 * ε) (1 / 80000) := by
        rw [Test.sqrt_rpow_one_div (by linarith) (by norm_num)]; norm_num
      rw [e]; simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow (by norm_num) hε0.le]
      exact mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)).trans_eq (Real.rpow_one 3))
        (Real.rpow_nonneg hε0.le _)
    have hb2 : Real.sqrt (Real.rpow ((D.d : ℝ) / D.q) (1 / 40000)) ≤
        (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) := by
      have e : Real.sqrt (Real.rpow ((D.d : ℝ) / D.q) (1 / 40000)) = Real.rpow ((D.d : ℝ) / D.q) (1 / 80000) := by
        rw [Test.sqrt_rpow_one_div (by positivity) (by norm_num)]; norm_num
      rw [e]; simp only [Real.rpow_eq_pow]
      rw [Real.div_rpow (by linarith) (by linarith), div_eq_mul_inv, ← Real.rpow_neg (by linarith)]
      exact mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)).trans_eq (Real.rpow_one _))
        (Real.rpow_nonneg (by linarith) _)
    have hb3 : Real.sqrt (Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ 2))))) ≤
        Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) := by
      have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [hexp_arg, ← Real.exp_half, show ((D.m * D.d : ℕ) : ℝ) = (D.m : ℝ) * D.d by push_cast; ring]
      simp only [Real.rpow_eq_pow]; rw [Real.rpow_def_of_pos (by norm_num)]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ (D.m : ℝ) * D.d)])
    refine (MIPStarRE.LDT.sqrt_add3_le_add3_sqrt (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le).trans ?_
    unfold transportEnvelope
    simp only [Real.rpow_eq_pow] at hx hy hz hb1 hb2 hb3 ⊢
    nlinarith [mul_nonneg (by linarith : 0 ≤ (D.d : ℝ) - 1) hx, mul_nonneg (by linarith : 0 ≤ (D.d : ℝ)) hy,
      mul_nonneg (by linarith : 0 ≤ 3 * (D.d : ℝ) - 1) hz]
  have hsE : Real.sqrt (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε)) ≤
      2460000000 * (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2 * transportEnvelope D ε := by
    change Real.sqrt (100000 * ((directLdAuxParameter D : ℝ) ^ 2) * ((D.m : ℝ) ^ 4) * _) ≤ _
    rw [Real.sqrt_mul (by positivity)]
    exact (mul_le_mul hpre henv (Real.sqrt_nonneg _) (by positivity)).trans_eq (by ring)
  have hsmd : Real.sqrt (((D.m : ℝ) * D.d) / D.q) ≤ (D.m : ℝ) * D.d * transportEnvelope D ε := by
    have h1 : Real.sqrt (((D.m : ℝ) * D.d) / D.q) ≤ (D.m : ℝ) * D.d * Real.rpow (D.q : ℝ) (-(1 / 80000)) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.sqrt_eq_rpow, Real.div_rpow (by positivity) (by linarith), div_eq_mul_inv,
        ← Real.rpow_neg (by linarith)]
      exact mul_le_mul
        ((Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by norm_num)).trans_eq (Real.rpow_one _))
        (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num))
        (Real.rpow_nonneg (by linarith) _) (by positivity)
    exact h1.trans (mul_le_mul_of_nonneg_left
      (by unfold transportEnvelope; simp only [Real.rpow_eq_pow] at hx hz ⊢; linarith) (by positivity))
  have hsε : Real.sqrt ε ≤ transportEnvelope D ε := by
    have h1 : Real.sqrt ε ≤ Real.rpow ε (1 / 80000) := by
      simp only [Real.rpow_eq_pow]; rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
    unfold transportEnvelope; simp only [Real.rpow_eq_pow] at h1 hy hz ⊢; linarith
  have hE0 : 0 ≤ Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) :=
    mul_nonneg (by positivity) (add_nonneg (add_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le)
  have hP : (D.m : ℝ) * D.d ≤ (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2 :=
    mul_le_mul (by simpa using pow_le_pow_right₀ hm1 (by norm_num : 1 ≤ 5))
      (by simpa using pow_le_pow_right₀ hd1 (by norm_num : 1 ≤ 2)) (by linarith) (by positivity)
  have hP1 : (1 : ℝ) ≤ (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2 := by
    nlinarith [one_le_pow₀ hm1 (n := 5), one_le_pow₀ hd1 (n := 2)]
  have htot : Real.sqrt (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
      ((D.m : ℝ) * D.d) / D.q + ε) ≤
      2500000000 * (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2 * transportEnvelope D ε := by
    refine (MIPStarRE.LDT.sqrt_add3_le_add3_sqrt hE0 (by positivity) hε0.le).trans ?_
    nlinarith [mul_le_mul_of_nonneg_right hP hT, mul_le_mul_of_nonneg_right hP1 hT]
  have hmono : (D.k : ℝ) * (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2 ≤ ((D.d * D.m * D.k : ℕ) : ℝ) ^ (8 : ℕ) := by
    push_cast
    calc (D.k : ℝ) * (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2
        ≤ (D.k : ℝ) ^ 8 * (D.m : ℝ) ^ 8 * (D.d : ℝ) ^ 8 :=
          mul_le_mul (mul_le_mul (by simpa using pow_le_pow_right₀ hk1 (by norm_num : 1 ≤ 8))
            (pow_le_pow_right₀ hm1 (by norm_num)) (by positivity) (by positivity))
            (pow_le_pow_right₀ hd1 (by norm_num)) (by positivity) (by positivity)
      _ = _ := by ring
  have hbase : (1 : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk
  have hpow : ((D.d * D.m * D.k : ℕ) : ℝ) ^ (8 : ℕ) ≤
      Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) (2500000000 * C₀) := by
    simp only [Real.rpow_eq_pow]; rw [← Real.rpow_natCast _ 8]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by push_cast; linarith)
  change _ ≤ 2500000000 * C₀ * Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) (2500000000 * C₀) * transportEnvelope D ε
  calc C₀ * (D.k : ℝ) * Real.sqrt _
      ≤ C₀ * (D.k : ℝ) * (2500000000 * (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2 * transportEnvelope D ε) :=
        mul_le_mul_of_nonneg_left htot (by positivity)
    _ = 2500000000 * C₀ * ((D.k : ℝ) * (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2) * transportEnvelope D ε := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hmono.trans hpow) (by linarith)) hT

theorem one_le_deltaLd_of_one_le_error {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hε : 1 ≤ ε) {q m d k : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    1 ≤ deltaLd a b ε q m d k := by
  have hbase : (1 : ℝ) ≤ ((d * m * k : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (Nat.mul_pos hd hm) hk
  have hX : (1 : ℝ) ≤ Real.rpow ((d * m * k : ℕ) : ℝ) a := by
    simp only [Real.rpow_eq_pow]; exact Real.one_le_rpow hbase (by linarith)
  have hY : (1 : ℝ) ≤ Real.rpow ε b := by
    simp only [Real.rpow_eq_pow]; exact Real.one_le_rpow hε hb
  have hZ : (0 : ℝ) ≤ Real.rpow (q : ℝ) (-b) := Real.rpow_nonneg (by positivity) _
  have hW : (0 : ℝ) ≤ Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))) := Real.rpow_nonneg (by norm_num) _
  unfold deltaLd
  exact (by norm_num : (1 : ℝ) = 1 * 1).trans_le
    (mul_le_mul (by nlinarith) (by linarith) (by norm_num) (by nlinarith))

theorem consistencyDefect_heteroKron_le_one {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A : X → Quantum.Measurement α ιA) (B : X → Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ 1 := by
  have hEq : consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ =
      1 - avgOver μ (fun x => ∑ a : α,
        DistanceCalculus.stateQForm ψ (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a))) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
      (fun x => DistanceCalculus.leftPlacedMeasurement (A x))
      (fun x => DistanceCalculus.rightPlacedMeasurement (B x)) ψ hμ hψ
  rw [hEq]
  have hnn : 0 ≤ avgOver μ (fun x => ∑ a : α,
      DistanceCalculus.stateQForm ψ (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a))) :=
    avgOver_nonneg μ _ fun x => Finset.sum_nonneg fun a _ => by
      rw [DistanceCalculus.placed_product_stateQForm_eq]
      exact DistanceCalculus.stateQForm_nonneg ψ (kronecker_nonneg ((A x).pos a) ((B x).pos a))
  linarith

theorem ten_sqrt_deltaLd_le (D : DirectLdParams) {a b ε : ℝ} (ha : 1 ≤ a) (hε : 0 ≤ ε) :
    10 * Real.sqrt (deltaLd a b ε D.q D.m D.d D.k) ≤
      deltaLd (10 * a) (b / 2) ε D.q D.m D.d D.k := by
  let N : ℝ := (D.d * D.m * D.k : ℕ)
  have hN : 1 ≤ N := Nat.one_le_cast.mpr (Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk)
  have hNa : 1 ≤ N ^ a := Real.one_le_rpow hN (by linarith)
  have hP0 : 0 ≤ a * N ^ a := by nlinarith
  have hs (x r : ℝ) (hx : 0 ≤ x) : Real.sqrt (x ^ r) = x ^ (r / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; ring_nf
  have hsum : Real.sqrt (ε ^ b + (D.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * (D.m * D.d : ℕ)))) ≤
      ε ^ (b / 2) + (D.q : ℝ) ^ (-(b / 2)) + (2 : ℝ) ^ (-((b / 2) * (D.m * D.d : ℕ))) := by
    refine (MIPStarRE.LDT.sqrt_add3_le_add3_sqrt (Real.rpow_nonneg hε _)
      (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _)).trans_eq ?_
    rw [hs ε b hε, hs (D.q : ℝ) (-b) (by positivity), hs 2 _ (by norm_num)]
    congr 2 <;> congr 1 <;> ring
  unfold deltaLd; simp only [Real.rpow_eq_pow]
  change 10 * Real.sqrt (a * N ^ a * _) ≤ 10 * a * N ^ (10 * a) * _
  rw [Real.sqrt_mul hP0]
  have hsP : Real.sqrt (a * N ^ a) ≤ a * N ^ (10 * a) :=
    (Real.sqrt_le_self_iff.mpr (Or.inr (by nlinarith))).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by linarith))
  have hb := mul_le_mul hsP hsum (Real.sqrt_nonneg _) (mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _))
  nlinarith

theorem error_and_collision_le_deltaLd (D : DirectLdParams) {a b ε : ℝ}
    (ha : 1 ≤ a) (hb : b ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ≤ deltaLd a b ε D.q D.m D.d D.k ∧
      (D.m : ℝ) * D.d / D.q ≤ deltaLd a b ε D.q D.m D.d D.k := by
  let N : ℝ := (D.d * D.m * D.k : ℕ)
  have hN : 1 ≤ N := Nat.one_le_cast.mpr (Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk)
  have hNa : N ≤ N ^ a := by simpa using Real.rpow_le_rpow_of_exponent_le hN ha
  have hP : N ≤ a * N ^ a := hNa.trans (le_mul_of_one_le_left (by linarith) ha)
  have hmd : (D.m : ℝ) * D.d ≤ N := by
    dsimp [N]; push_cast
    nlinarith [le_mul_of_one_le_right (by positivity : 0 ≤ (D.d : ℝ) * D.m) (by exact_mod_cast D.hk : (1 : ℝ) ≤ D.k)]
  have he : ε ≤ ε ^ b := by simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1 hb
  have hq : (D.q : ℝ)⁻¹ ≤ (D.q : ℝ) ^ (-b) := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast D.toLDTParameters.hq : (1 : ℝ) ≤ D.q) (neg_le_neg hb)
  have hx := Real.rpow_nonneg hε.le b
  have hy := Real.rpow_nonneg (by positivity : 0 ≤ (D.q : ℝ)) (-b)
  have hz := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(b * (D.m * D.d : ℕ)))
  unfold deltaLd; simp only [Real.rpow_eq_pow]
  change ε ≤ a * N ^ a * _ ∧ (D.m : ℝ) * D.d / D.q ≤ a * N ^ a * _
  exact ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr (hN.trans hP)) hx, mul_nonneg (by linarith : 0 ≤ a * N ^ a) (add_nonneg hy hz)],
    by rw [div_eq_mul_inv]; have := mul_le_mul (hmd.trans hP) hq (by positivity) (by linarith); nlinarith [mul_nonneg (by linarith : 0 ≤ a * N ^ a) (add_nonneg hx hz)]⟩

/-! ## Consistency defect transport, seed-fiber compression, and `k = 1` simultaneous measurements -/

export MIPStarRE.QPBT.DistanceCalculus (pureStateEuclideanVector
  pureStateEuclideanVector_apply pureStateEuclideanVector_norm pureState_stateQForm_eq_ev)

noncomputable def directPolyEquivPolynomial (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    PolyIndex D.m (DirectScalarQ D) D.d ≃ MIPStarRE.LDT.Polynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  have hdeg (p : MvPolynomial (Fin D.m) (DirectScalarQ D))
      (hp : ∀ i, MvPolynomial.degreeOf i p ≤ D.d) (i : Fin D.m) :
      MvPolynomial.degreeOf i (MvPolynomial.rename Fin.rev p) ≤ D.d := by
    rw [← Fin.rev_rev i, MvPolynomial.degreeOf_rename_of_injective Fin.rev_injective]; exact hp _
  have hinv (p : MvPolynomial (Fin D.m) (DirectScalarQ D)) :
      MvPolynomial.rename Fin.rev (MvPolynomial.rename Fin.rev p) = p := by
    rw [MvPolynomial.rename_rename, show Fin.rev ∘ Fin.rev = id from funext Fin.rev_rev]
    exact MvPolynomial.rename_id_apply p
  exact
    { toFun := fun g => ⟨MvPolynomial.rename Fin.rev g.1, hdeg g.1 (degreeOf_le_of_mem_polyFunc g.2)⟩
      invFun := fun g => ⟨MvPolynomial.rename Fin.rev g.poly, by
        rw [MvPolynomial.mem_restrictDegree]
        exact fun s hs i => MvPolynomial.degreeOf_le_iff.mp (hdeg g.poly g.lowIndividualDegree i) s hs⟩
      left_inv := fun g => Subtype.ext (hinv g.1)
      right_inv := fun ⟨p, _⟩ => by
        exact (show ∀ p' (eq : p' = p) h1 h2, ({ poly := p', lowIndividualDegree := h1 } :
          MIPStarRE.LDT.Polynomial D.toLDTParameters) = { poly := p, lowIndividualDegree := h2 } by
          intro _ eq _ _; subst eq; rfl) _ (hinv p) _ _ }

@[simp] theorem directPolyEquivPolynomial_apply (D : DirectLdParams)
    (g : PolyIndex D.m (DirectScalarQ D) D.d) (u : Fin D.m → DirectScalarQ D) :
    letI := D.toLDTFieldModel
    directPolyEquivPolynomial D g (directPointEquiv D u) =
      directScalarEquiv D (MvPolynomial.eval u g.1) := by
  letI := D.toLDTFieldModel
  unfold MIPStarRE.LDT.Polynomial.toFun evalPolynomialModel decodePoint
  change directScalarEquiv D (MvPolynomial.eval _ (MvPolynomial.rename Fin.rev g.1)) = _
  rw [MvPolynomial.eval_rename]
  exact congrArg (fun v => directScalarEquiv D (MvPolynomial.eval v g.1))
    (funext fun i => by simp only [Function.comp_apply, directPointEquiv_apply, Fin.rev_rev]; exact (directScalarEquiv D).symm_apply_apply _)

noncomputable def ldtMeasurementToMatrixMeasurement {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (M : MIPStarRE.LDT.Measurement α ι) :
    MIPStarRE.Quantum.Measurement α ι :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne M.outcome M.outcome_pos
    (M.sum_eq_total.trans M.total_eq_one)

noncomputable def directPolynomialMeasurement (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    {ι : Type*} → [Fintype ι] → [DecidableEq ι] →
      ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) ι →
        PolyMeas D.m (DirectScalarQ D) D.d ι :=
  letI := D.toLDTFieldModel
  fun G => matrixMeasurementTransport (directPolyEquivPolynomial D).symm
    (ldtMeasurementToMatrixMeasurement G.toMeasurement)

theorem directPolynomialMeasurement_evaluation_effect (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) ι)
      (u : Fin D.m → DirectScalarQ D) (a : DirectScalarQ D),
      ((directPolynomialMeasurement D G).postprocess (fun g => MvPolynomial.eval u g.1)).effect a =
        (ProjMeas.postprocess G (fun g => g (directPointEquiv D u))).outcome
          (directScalarEquiv D a) := by
  letI := D.toLDTFieldModel
  intro ι _ _ G u a
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect, ProjMeas.postprocess, SubMeas.postprocess_outcome]
  refine Finset.sum_bij (fun g _ => directPolyEquivPolynomial D g)
    (fun g hg => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      simpa only [directPolyEquivPolynomial_apply] using congrArg (directScalarEquiv D) hg)
    (fun _ _ _ _ h => (directPolyEquivPolynomial D).injective h)
    (fun g hg => ⟨(directPolyEquivPolynomial D).symm g, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      have hev := directPolyEquivPolynomial_apply D ((directPolyEquivPolynomial D).symm g) u
      rw [(directPolyEquivPolynomial D).apply_symm_apply] at hev
      exact (directScalarEquiv D).injective (hev.symm.trans hg),
      (directPolyEquivPolynomial D).apply_symm_apply g⟩)
    (fun _ _ => rfl)

theorem strategyConsRel_consistencyDefect_le {G : Game} (S : Strategy G)
    {Question Outcome : Type*} [Fintype Question] [DecidableEq Question]
    [Fintype Outcome] [DecidableEq Outcome]
    (mu : Distribution Question) (hmu : mu.IsProbability)
    (A : Question → ProjMeas Outcome S.ιA) (B : Question → ProjMeas Outcome S.ιB) (delta : ℝ)
    (h : ConsRel (strategyQuantumState S) mu (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) delta) :
    consistencyDefect mu (fun x a => heteroKron ((A x).outcome a) 1)
      (fun x a => heteroKron 1 ((B x).outcome a)) S.ψ ≤ delta := by
  letI := strategy_carrier_nonempty S
  let psi := strategyPureState S
  have hpsi : pureStateEuclideanVector psi = S.ψ :=
    (EuclideanSpace.equiv (S.ιA × S.ιB) ℂ).injective rfl
  have hEq : consistencyDefect mu (fun x a => heteroKron ((A x).outcome a) 1)
      (fun x a => heteroKron 1 ((B x).outcome a)) (pureStateEuclideanVector psi) =
      1 - avgOver mu (fun x => ∑ a : Outcome,
        DistanceCalculus.stateQForm (pureStateEuclideanVector psi)
          (heteroKron ((A x).outcome a) 1 * heteroKron 1 ((B x).outcome a))) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap mu
      (fun x => DistanceCalculus.leftPlacedMeasurement (ldtMeasurementToMatrixMeasurement (A x).toMeasurement))
      (fun x => DistanceCalculus.rightPlacedMeasurement (ldtMeasurementToMatrixMeasurement (B x).toMeasurement))
      (pureStateEuclideanVector psi) hmu (pureStateEuclideanVector_norm psi)
  rw [← hpsi, hEq, ← avgOver_const_of_isProbability mu hmu 1, ← avgOver_sub]
  refine (le_of_eq (avgOver_congr _ _ _ fun x => ?_)).trans h.offDiagonalBound
  change 1 - _ = qBipartiteConsDefect (psi : QuantumState _) (A x).toSubMeas (B x).toSubMeas
  rw [qBipartiteConsDefect_of_measurements (psi : QuantumState _) (A x).toMeasurement (B x).toMeasurement,
    ev_one_of_isNormalized _ psi.toQuantumState_isNormalized]
  congr 1; refine Finset.sum_congr rfl fun a _ => ?_
  change DistanceCalculus.stateQForm (pureStateEuclideanVector psi)
    (heteroKron ((A x).outcome a) 1 * heteroKron 1 ((B x).outcome a)) = _
  rw [DistanceCalculus.placed_product_stateQForm_eq]
  exact pureState_stateQForm_eq_ev psi (opTensor ((A x).outcome a) ((B x).outcome a))

instance directLdtPointNonempty (D : DirectLdParams) : Nonempty (Point D.toLDTParameters) :=
  ⟨fun _ => ⟨0, D.toLDTParameters.hq⟩⟩

noncomputable def averageDiagonalBlock {ι blk : Type*} [Fintype ι] [Fintype blk]
    (A : Op (ι × blk)) : Op ι :=
  (Fintype.card blk : ℝ)⁻¹ • ∑ r, A.submatrix (fun i => (i, r)) (fun i => (i, r))

noncomputable def correlatedAncillaCompressMeasurement {α ι blk : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype blk] [DecidableEq blk] [Nonempty blk]
    (M : MIPStarRE.Quantum.Measurement α (ι × blk)) :
    MIPStarRE.Quantum.Measurement α ι :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => averageDiagonalBlock (M.effect a))
    (fun a => smul_nonneg (by positivity) <| Finset.sum_nonneg fun r _ =>
      Matrix.nonneg_iff_posSemidef.mpr ((Matrix.nonneg_iff_posSemidef.mp (M.pos a)).submatrix _))
    (by
      ext i j
      simp only [averageDiagonalBlock, Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply,
        ← Finset.smul_sum]
      rw [Finset.sum_comm, Finset.sum_congr rfl fun r _ => by
        simpa only [Matrix.sum_apply] using congrFun (congrFun M.sum_eq_one (i, r)) (j, r)]
      simp [Matrix.one_apply, Fintype.card_ne_zero])

theorem correlatedAncillaCompressMeasurement_postprocess {α β ι blk : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] [Fintype blk] [DecidableEq blk] [Nonempty blk]
    (M : MIPStarRE.Quantum.Measurement α (ι × blk)) (f : α → β) :
    correlatedAncillaCompressMeasurement (M.postprocess f) =
      (correlatedAncillaCompressMeasurement M).postprocess f := by
  apply MIPStarRE.Quantum.Measurement.ext; intro b
  ext i j
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, correlatedAncillaCompressMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne, averageDiagonalBlock, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.submatrix_apply, Finset.smul_sum]
  exact Finset.sum_comm

noncomputable def seedFiberCompressPolyMeasTuple (L : LdParams) {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (G : DirectPolyMeasTuple L.toDirectLdParams (ι × Fin (L.q / L.m))) : PolyMeasTuple L ι :=
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  correlatedAncillaCompressMeasurement G

theorem correlatedState_compress_left {ιA ιB blk : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype blk] [DecidableEq blk] [Nonempty blk]
    (psi : EuclideanSpace ℂ (ιA × ιB))
    (phi : EuclideanSpace ℂ ((ιA × blk) × (ιB × blk)))
    (hphi : ∀ i j r s, phi ((i, r), (j, s)) =
      if r = s then psi (i, j) * (Real.sqrt (Fintype.card blk : ℝ) : ℂ)⁻¹ else 0)
    (A : Op (ιA × blk)) (B : Op ιB) :
    DistanceCalculus.stateQForm phi (heteroKron A (Matrix.blockDiagonal fun _ => B)) =
      DistanceCalculus.stateQForm psi (heteroKron (averageDiagonalBlock A) B) := by
  unfold DistanceCalculus.stateQForm
  apply congrArg Complex.re
  unfold applyOperatorToState heteroKron Matrix.kronecker averageDiagonalBlock
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  suffices h :
      (∑ i : ιA, ∑ r : blk, ∑ j : ιB, ∑ i' : ιA, ∑ j' : ιB,
        (starRingEnd ℂ) (Real.sqrt (Fintype.card blk : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) (psi (i, j)) *
          (B j j' * (A (i, r) (i', r) * ((Real.sqrt (Fintype.card blk : ℝ) : ℂ)⁻¹ * psi (i', j'))))) =
      ∑ i : ιA, ∑ j : ιB, ∑ i' : ιA, ∑ j' : ιB, ∑ r : blk,
        (starRingEnd ℂ) (psi (i, j)) * (psi (i', j') * (B j j' * ((Fintype.card blk : ℂ)⁻¹ * A (i, r) (i', r)))) by
    simpa [hphi, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply, apply_ite, map_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, Matrix.submatrix,
      Matrix.sum_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm] using h
  refine Fintype.sum_congr _ _ fun i => Finset.sum_comm.trans <| Fintype.sum_congr _ _ fun j =>
    Finset.sum_comm.trans <| Fintype.sum_congr _ _ fun i' => Finset.sum_comm.trans <|
      Fintype.sum_congr _ _ fun j' => Fintype.sum_congr _ _ fun r => ?_
  ring_nf; rw [inv_sqrt_natCast_mul_conj (Fintype.card blk)]; ring

theorem consistencyDefect_seedFiber_compress_left {G : Game} (S : Strategy G) (L : LdParams)
    {X α : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (mu : Distribution X) (A : X → α → Op (S.ιA × Fin (L.q / L.m))) (B : X → α → Op S.ιB) :
    consistencyDefect mu (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (Matrix.blockDiagonal fun _ => B x a)) (seedFiberLiftedState S L) =
      consistencyDefect mu (fun x a => heteroKron (averageDiagonalBlock (A x a)) 1)
        (fun x a => heteroKron 1 (B x a)) S.ψ := by
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold consistencyDefect avgOver
  simp_rw [DistanceCalculus.consistency_term_eq_stateQForm, DistanceCalculus.placed_product_stateQForm_eq]
  refine Finset.sum_congr rfl fun x _ => congrArg _ <| Fintype.sum_congr _ _ fun a =>
    Fintype.sum_congr _ _ fun b => ?_
  by_cases hab : a = b
  · simp [hab]
  · simp only [if_neg hab]
    exact correlatedState_compress_left S.ψ (seedFiberLiftedState S L)
      (seedFiberLiftedState_apply S L) (A x a) (B x b)

theorem consistencyDefect_seedFiber_compress_right {G : Game} (S : Strategy G) (L : LdParams)
    {X α : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (mu : Distribution X) (A : X → α → Op S.ιA) (B : X → α → Op (S.ιB × Fin (L.q / L.m))) :
    consistencyDefect mu (fun x a => heteroKron (Matrix.blockDiagonal fun _ => A x a) 1)
        (fun x a => heteroKron 1 (B x a)) (seedFiberLiftedState S L) =
      consistencyDefect mu (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (averageDiagonalBlock (B x a))) S.ψ := by
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  rw [← consistencyDefect_prodComm_heteroKron, ← consistencyDefect_prodComm_heteroKron mu A]
  unfold consistencyDefect avgOver
  simp_rw [DistanceCalculus.consistency_term_eq_stateQForm, DistanceCalculus.placed_product_stateQForm_eq]
  refine Finset.sum_congr rfl fun x _ => congrArg _ <| Fintype.sum_congr _ _ fun a =>
    Fintype.sum_congr _ _ fun b => ?_
  by_cases hab : a = b
  · simp [hab]
  · simp only [if_neg hab]
    exact correlatedState_compress_left (reindexState (Equiv.prodComm S.ιA S.ιB) S.ψ)
      (reindexState (Equiv.prodComm _ _) (seedFiberLiftedState S L))
      (fun j i r s => by
        change seedFiberLiftedState S L ((i, s), (j, r)) = _
        rw [seedFiberLiftedState_apply]; by_cases h : r = s
        · subst h; simp [reindexState]
        · rw [if_neg (Ne.symm h), if_neg h])
      (B x a) (A x b)

theorem seedFiberPointMeasurement_effect (L : LdParams) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : LdQuestion L → MIPStarRE.Quantum.Measurement (LdAnswer L) ι)
    (u : Fin L.m → ScalarQ L) (a : Fin L.k → ScalarQ L) :
    ((blockDiagonalMeasurement fun r : Fin (L.q / L.m) =>
        matrixMeasurementTransport (ldDirectAnswerEquiv L)
          (M (seededLdQuestion L (directLdPointQuestionOf L.toDirectLdParams u) r))).postprocess
        (directLdPointValuesOrZero L.toDirectLdParams)).effect a =
      Matrix.blockDiagonal fun _ : Fin (L.q / L.m) =>
        ((M (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)).effect a := by
  ext ⟨i, r⟩ ⟨j, s⟩
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, blockDiagonalMeasurement_effect,
    Matrix.sum_apply, Matrix.blockDiagonal_apply, matrixMeasurementTransport_effect]
  by_cases hrs : r = s
  · subst s; simp only [if_pos, seededLdQuestion]
    change ∑ x ∈ Finset.univ.filter (fun x => directLdPointValuesOrZero L.toDirectLdParams x = a),
        (M (ldPointQuestionOf L u)).effect ((ldDirectAnswerEquiv L).symm x) i j = _
    refine Finset.sum_bij (fun x _ => (ldDirectAnswerEquiv L).symm x)
      (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        cases x <;> exact hx)
      (fun _ _ _ _ h => (ldDirectAnswerEquiv L).symm.injective h)
      (fun y hy => ⟨ldDirectAnswerEquiv L y, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        cases y <;> exact hy, (ldDirectAnswerEquiv L).symm_apply_apply y⟩)
      (fun _ _ => rfl)
  · simp [hrs]

theorem ldStrategyToDirect_pointPolynomial_compression (L : LdParams) (S : Strategy (ldGame L))
    (GB : DirectPolyMeasTuple L.toDirectLdParams (S.ιB × Fin (L.q / L.m))) :
    consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u o => heteroKron ((((ldStrategyToDirect L S).A
          (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
            (directLdPointValuesOrZero L.toDirectLdParams)).effect o) 1)
        (fun u o => heteroKron 1 ((GB.postprocess (evalDirectPolyTupleAt u)).effect o))
        (ldStrategyToDirect L S).ψ =
      consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u o => heteroKron (((S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)).effect o) 1)
        (fun u o => heteroKron 1
          (((seedFiberCompressPolyMeasTuple L GB).postprocess (evalPolyTupleAt u)).effect o)) S.ψ := by
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  have hev (u : Fin L.m → ScalarQ L) :
      (seedFiberCompressPolyMeasTuple L GB).postprocess (evalPolyTupleAt u) =
        correlatedAncillaCompressMeasurement (GB.postprocess (evalDirectPolyTupleAt u)) :=
    (correlatedAncillaCompressMeasurement_postprocess GB (evalDirectPolyTupleAt u)).symm
  simp_rw [hev]
  exact (consistencyDefect_congr _ _ _ _ _ (seedFiberLiftedState S L)
    (fun u o => congrArg (heteroKron · 1) (seedFiberPointMeasurement_effect L S.A u o))
    (fun _ _ => rfl)).trans (consistencyDefect_seedFiber_compress_right S L _ _ _)

theorem ldStrategyToDirect_polynomialPoint_compression (L : LdParams) (S : Strategy (ldGame L))
    (GA : DirectPolyMeasTuple L.toDirectLdParams (S.ιA × Fin (L.q / L.m))) :
    consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u o => heteroKron ((GA.postprocess (evalDirectPolyTupleAt u)).effect o) 1)
        (fun u o => heteroKron 1 ((((ldStrategyToDirect L S).B
          (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
            (directLdPointValuesOrZero L.toDirectLdParams)).effect o))
        (ldStrategyToDirect L S).ψ =
      consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u o => heteroKron
          (((seedFiberCompressPolyMeasTuple L GA).postprocess (evalPolyTupleAt u)).effect o) 1)
        (fun u o => heteroKron 1
          (((S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)).effect o)) S.ψ := by
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  have hev (u : Fin L.m → ScalarQ L) :
      (seedFiberCompressPolyMeasTuple L GA).postprocess (evalPolyTupleAt u) =
        correlatedAncillaCompressMeasurement (GA.postprocess (evalDirectPolyTupleAt u)) :=
    (correlatedAncillaCompressMeasurement_postprocess GA (evalDirectPolyTupleAt u)).symm
  simp_rw [hev]
  exact (consistencyDefect_congr _ _ _ _ _ (seedFiberLiftedState S L)
    (fun _ _ => rfl)
    (fun u o => congrArg (heteroKron 1) (seedFiberPointMeasurement_effect L S.B u o))).trans
    (consistencyDefect_seedFiber_compress_left S L _ _ _)

theorem ldPointPair_consistencyDefect_le (L : LdParams) (S : Strategy (ldGame L))
    (hS : S.IsProjective) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u a => heteroKron (((S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)).effect a) 1)
        (fun u a => heteroKron 1 (((S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)).effect a))
        S.ψ ≤ 9 * ε := by
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  let D := L.toDirectLdParams
  let SD := ldStrategyToDirect L S
  have hSD := ldStrategyToDirect_isProjective L S hS
  have havgB {ι blk : Type} [Fintype ι] [Fintype blk] [DecidableEq blk] [Nonempty blk] (M : Op ι) :
      averageDiagonalBlock (Matrix.blockDiagonal fun _ : blk => M) = M := by
    have hsub (r : blk) : (Matrix.blockDiagonal fun _ : blk => M).submatrix
        (fun i => (i, r)) (fun i => (i, r)) = M := by ext i j; simp [Matrix.blockDiagonal_apply_eq]
    have hc : (Fintype.card blk : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    unfold averageDiagonalBlock
    simp only [hsub, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hcomp : consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
      (fun u a => heteroKron (((SD.A (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).effect a) 1)
      (fun u a => heteroKron 1 (((SD.B (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).effect a)) SD.ψ =
      consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u a => heteroKron (((S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)).effect a) 1)
        (fun u a => heteroKron 1 (((S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)).effect a)) S.ψ :=
    (consistencyDefect_congr _ _ _ _ _ (seedFiberLiftedState S L)
      (fun u a => congrArg (heteroKron · 1) (seedFiberPointMeasurement_effect L S.A u a))
      (fun u a => congrArg (heteroKron 1) (seedFiberPointMeasurement_effect L S.B u a))).trans
      ((consistencyDefect_seedFiber_compress_right S L _ _ _).trans
        (consistencyDefect_congr _ _ _ _ _ S.ψ (fun _ _ => rfl) fun _ _ => by rw [havgB]; rfl))
  rw [← hcomp]
  let PA (u : Fin D.m → DirectScalarQ D) := ProjMeas.postprocess
    (matrixMeasurementToLDTProjMeas (SD.A (directLdPointQuestionOf D u)) (hSD.1 _))
    (directLdPointValuesOrZero D)
  let PB (u : Fin D.m → DirectScalarQ D) := ProjMeas.postprocess
    (matrixMeasurementToLDTProjMeas (SD.B (directLdPointQuestionOf D u)) (hSD.2 _))
    (directLdPointValuesOrZero D)
  have hpt : avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
      (fun u => qBipartiteConsDefect (strategyQuantumState SD) (PA u).toSubMeas (PB u).toSubMeas) ≤
      directLdBranchRejectionProbability D SD (.point, .point) := by
    rw [directLdBranchRejectionProbability_eq_avgOver]
    refine (avgOver_mono _ _ _ fun u => qBipartiteConsDefect_le_directRejectedMass D SD hSD _ _
      (directLdPointValuesOrZero D) (directLdPointValuesOrZero D)
      (directLdPointValuesOrZero_eq_of_win D u)).trans_eq ?_
    let f := fun p => directRejectedMass D SD (directLdPointQuestionOf D p) (directLdPointQuestionOf D p)
    exact (avgOver_uniform_fst f).symm.trans
      ((avgOver_uniform_equiv_fst (directLdSpaceSplitEquiv D) fun pi => f pi.1).symm.trans
        (avgOver_congr _ _ _ fun _ => rfl))
  have hrej : directLdRejectionProbability D SD ≤ ε := by
    rw [directLdRejectionProbability_eq_one_sub_value, ldStrategyToDirect_value_eq]; linarith
  rw [directLdRejectionProbability, avgOver_ldType_pair] at hrej
  have hnn := directLdBranchRejectionProbability_nonneg D SD
  have hbr : directLdBranchRejectionProbability D SD (.point, .point) ≤ 9 * ε := by
    linarith [hnn (.point, .aline), hnn (.point, .dline), hnn (.aline, .point), hnn (.aline, .aline),
      hnn (.aline, .dline), hnn (.dline, .point), hnn (.dline, .aline), hnn (.dline, .dline)]
  refine (le_of_eq ?_).trans (strategyConsRel_consistencyDefect_le SD _
    (uniformDistribution_isProbability _) PA PB (9 * ε) ⟨hpt.trans hbr⟩)
  exact consistencyDefect_congr _ _ _ _ _ SD.ψ
    (fun _ _ => by simp only [PA, ProjMeas.postprocess, SubMeas.postprocess_outcome,
      matrixMeasurementToLDTProjMeas_outcome, MIPStarRE.Quantum.Measurement.postprocess_effect])
    (fun _ _ => by simp only [PB, ProjMeas.postprocess, SubMeas.postprocess_outcome,
      matrixMeasurementToLDTProjMeas_outcome, MIPStarRE.Quantum.Measurement.postprocess_effect])

theorem directPolynomialAgreement_avg_le_mdq (D : DirectLdParams)
    (g g' : PolyIndex D.m (DirectScalarQ D) D.d) (hneq : g ≠ g') :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => if MvPolynomial.eval u g.1 = MvPolynomial.eval u g'.1 then (1 : Error) else 0) ≤
      (D.m * D.d : Error) / D.q := by
  letI := D.toLDTFieldModel
  let gL := directPolyEquivPolynomial D g
  let g'L := directPolyEquivPolynomial D g'
  refine (le_of_eq ?_).trans (polynomialAgreement_avg_le_mdq D.toLDTParameters gL g'L
    fun h => hneq ((directPolyEquivPolynomial D).injective h))
  refine (avgOver_congr _ _ _ fun u => ?_).trans
    (avgOver_uniform_equiv (directPointEquiv D).symm fun u : Point D.toLDTParameters =>
      if gL u = g'L u then (1 : Error) else 0).symm
  simp only [gL, g'L, Equiv.symm_symm, directPolyEquivPolynomial_apply]
  exact if_congr (directScalarEquiv D).injective.eq_iff.symm rfl rfl

theorem exists_directSimultaneousPolynomialMeasurements_of_k_eq_one
    (D : DirectLdParams) (hk : D.k = 1) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (ε : Error) (hwin : 1 - ε ≤ S.value) :
    ∃ GA : DirectPolyMeasTuple D S.ιA, ∃ GB : DirectPolyMeasTuple D S.ιB,
      consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u o => heteroKron (((S.A (directLdPointQuestionOf D u)).postprocess
            (directLdPointValuesOrZero D)).effect o) 1)
          (fun u o => heteroKron 1 ((GB.postprocess (evalDirectPolyTupleAt u)).effect o)) S.ψ ≤
        Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) ∧
      consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u o => heteroKron ((GA.postprocess (evalDirectPolyTupleAt u)).effect o) 1)
          (fun u o => heteroKron 1 (((S.B (directLdPointQuestionOf D u)).postprocess
            (directLdPointValuesOrZero D)).effect o)) S.ψ ≤
        Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) ∧
      consistencyDefect (uniformDistribution Unit)
          (fun _ g => heteroKron (GA.effect g) 1)
          (fun _ g => heteroKron 1 (GB.effect g)) S.ψ ≤
        Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) := by
  letI := D.toLDTFieldModel
  haveI hU : Unique (Fin D.k) :=
    { default := ⟨0, by omega⟩, uniq := fun i => Fin.ext (by have := i.isLt; omega) }
  obtain ⟨GA₀, GB₀, h1, h2, h3⟩ := Test.mainFormal D.toLDTParameters
    (directCoordinateProjStrat D S hS default) (3 * ε)
    (directCoordinate_passes D S hS default ε hwin).soundnessHypothesis
    (directLdAuxParameter D) (four_hundred_mul_le_directLdAuxParameter D) (directLdAuxParameter_pos D)
  have hct {α β ι d0 : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      [Fintype ι] [DecidableEq ι] [Unique ι] [Fintype d0] [DecidableEq d0]
      (M : Quantum.Measurement α d0) (f : α → ι → β) (b : β) :
      (M.postprocess f).effect (fun _ => b) = (M.postprocess fun a => f a default).effect b := by
    simp only [Quantum.Measurement.postprocess_effect]
    exact Finset.sum_congr (Finset.filter_congr fun a _ => funext_iff.trans Unique.forall_iff) fun _ _ => rfl
  have hptEff {ι : Type} [Fintype ι] [DecidableEq ι]
      (M : DirectLdQuestion D → MIPStarRE.Quantum.Measurement (DirectLdAnswer D) ι)
      (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q))
      (u : Fin D.m → DirectScalarQ D) (a : DirectScalarQ D) :
      (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas (M (directPointQuestionOf D (directPointEquiv D u))) (hM _))
        (directPointAnswerReadout D default)).outcome (directScalarEquiv D a) =
        ((M (directLdPointQuestionOf D u)).postprocess
          (fun ans => directLdPointValuesOrZero D ans default)).effect a := by
    classical
    simp only [ProjMeas.postprocess, SubMeas.postprocess_outcome, matrixMeasurementToLDTProjMeas_outcome,
      directPointQuestionOf_directPointEquiv, MIPStarRE.Quantum.Measurement.postprocess_effect,
      directPointAnswerReadout]
    congr 1; ext ans; simp [(directScalarEquiv D).injective.eq_iff]
  refine ⟨(directPolynomialMeasurement D GA₀).postprocess (fun g _ => g),
    (directPolynomialMeasurement D GB₀).postprocess (fun g _ => g), ?_, ?_, ?_⟩
  · have hldt := strategyConsRel_consistencyDefect_le S _ (uniformDistribution_isProbability _)
      (directCoordinateProjStrat D S hS default).pointMeasurementA
      (fun u => ProjMeas.postprocess GB₀ fun g => g u) _ (by exact h1)
    refine ((consistencyDefect_outcome_equiv _ (Equiv.funUnique (Fin D.k) (DirectScalarQ D)).symm _ _ S.ψ).symm.trans
      ((consistencyDefect_congr _ _ _ _ _ S.ψ
        (fun u a => by
          change heteroKron (((S.A _).postprocess _).effect (fun _ => a)) 1 = _
          rw [hct, ← hptEff S.A hS.1 u a]; rfl)
        (fun u a => by
          change heteroKron 1 ((((directPolynomialMeasurement D GB₀).postprocess _).postprocess _).effect (fun _ => a)) = _
          rw [MIPStarRE.Quantum.Measurement.postprocess_comp, hct]
          exact congrArg (heteroKron 1) (directPolynomialMeasurement_evaluation_effect D GB₀ u a))).trans
      (consistencyDefect_uniform_question_outcome_equiv (directPointEquiv D) (directScalarEquiv D)
        (fun u a => heteroKron (((directCoordinateProjStrat D S hS default).pointMeasurementA u).outcome a) 1)
        (fun u a => heteroKron 1 ((ProjMeas.postprocess GB₀ fun g => g u).outcome a)) S.ψ))).trans_le hldt
  · have hldt := strategyConsRel_consistencyDefect_le S _ (uniformDistribution_isProbability _)
      (fun u => ProjMeas.postprocess GA₀ fun g => g u)
      (directCoordinateProjStrat D S hS default).pointMeasurementB _ (by exact h2)
    refine ((consistencyDefect_outcome_equiv _ (Equiv.funUnique (Fin D.k) (DirectScalarQ D)).symm _ _ S.ψ).symm.trans
      ((consistencyDefect_congr _ _ _ _ _ S.ψ
        (fun u a => by
          change heteroKron ((((directPolynomialMeasurement D GA₀).postprocess _).postprocess _).effect (fun _ => a)) 1 = _
          rw [MIPStarRE.Quantum.Measurement.postprocess_comp, hct]
          exact congrArg (heteroKron · 1) (directPolynomialMeasurement_evaluation_effect D GA₀ u a))
        (fun u a => by
          change heteroKron 1 (((S.B _).postprocess _).effect (fun _ => a)) = _
          rw [hct, ← hptEff S.B hS.2 u a]; rfl)).trans
      (consistencyDefect_uniform_question_outcome_equiv (directPointEquiv D) (directScalarEquiv D)
        (fun u a => heteroKron ((ProjMeas.postprocess GA₀ fun g => g u).outcome a) 1)
        (fun u a => heteroKron 1 (((directCoordinateProjStrat D S hS default).pointMeasurementB u).outcome a)) S.ψ))).trans_le hldt
  · have hldt := strategyConsRel_consistencyDefect_le S _ (uniformDistribution_isProbability Unit)
      (fun _ => GA₀) (fun _ => GB₀) _ (by exact h3)
    refine ((consistencyDefect_outcome_equiv _
      (Equiv.funUnique (Fin D.k) (PolyIndex D.m (DirectScalarQ D) D.d)).symm _ _ S.ψ).symm.trans
      ((consistencyDefect_congr _ _ _ _ _ S.ψ
        (fun _ p => by
          classical
          change heteroKron (((directPolynomialMeasurement D GA₀).postprocess (fun g _ => g)).effect (fun _ => p)) 1 =
            heteroKron (GA₀.outcome (directPolyEquivPolynomial D p)) 1
          rw [hct, MIPStarRE.Quantum.Measurement.postprocess_effect]
          simp [Finset.filter_eq', directPolynomialMeasurement, ldtMeasurementToMatrixMeasurement]; rfl)
        (fun _ p => by
          classical
          change heteroKron 1 (((directPolynomialMeasurement D GB₀).postprocess (fun g _ => g)).effect (fun _ => p)) =
            heteroKron 1 (GB₀.outcome (directPolyEquivPolynomial D p))
          rw [hct, MIPStarRE.Quantum.Measurement.postprocess_effect]
          simp [Finset.filter_eq', directPolynomialMeasurement, ldtMeasurementToMatrixMeasurement]; rfl)).trans
      (consistencyDefect_outcome_equiv _ (directPolyEquivPolynomial D)
        (fun _ g => heteroKron (GA₀.outcome g) 1) (fun _ g => heteroKron 1 (GB₀.outcome g)) S.ψ))).trans_le hldt

end

end MIPStarRE.QPBT
