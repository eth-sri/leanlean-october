module

public import QPBT.Algebra.Pauli
public import QPBT.Algebra.SelfDualBasisTheorems
public import QPBT.State
public import MIPStarRE.LDT.Preliminaries.FiniteFields

/-! # Pauli product, commutation, and cancellation identities

The principal results are blueprint `lem:twisted-commutation` and
`lem:cancellation`, from
`references/qpbt-paper/04_preliminaries.tex:1056-1095,1124-1151`,
restricted to the characteristic-two field used by the test.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum

section

variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]

/-- Pauli observables in one basis multiply by adding their labels. -/
theorem tauObservable_mul (W : PauliKind) (a a' : ι → K) :
    tauObservable W a * tauObservable W a' = tauObservable W (a + a') := by
  ext x y
  rw [Matrix.mul_apply]
  cases W
  · simp only [tauObservable_X_apply, ← sub_eq_iff_eq_add, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [sub_sub]
  · simp only [tauObservable_Z_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_ite, mul_zero]
    split_ifs with h
    · rw [← phaseSign_add, add_dotProduct, map_add]
    · rfl

/-- Pauli observables are involutions in characteristic two. -/
theorem tauObservable_sq (W : PauliKind) (a : ι → K) :
    tauObservable W a * tauObservable W a = 1 := by
  letI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
  rw [tauObservable_mul, show a + a = 0 from funext fun i => CharTwo.add_self_eq_zero (a i),
    tauObservable_zero]

/-- Exchanging a shift and a phase contributes the binary trace pairing. -/
theorem tauObservable_X_mul_Z (a b : ι → K) :
    tauObservable .X a * tauObservable .Z b =
      phaseSign (binTrace K (dotProduct a b)) • (tauObservable .Z b * tauObservable .X a) := by
  ext x y
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, tauObservable_X_apply,
    tauObservable_Z_apply]
  conv_lhs => simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_rhs => simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  split_ifs with h
  · rw [h, dotProduct_add, map_add, phaseSign_add, dotProduct_comm b a]
    rw [one_mul, mul_one, mul_left_comm, phaseSign_mul_self, mul_one]
  · simp

end

/-- Expand every register label in the fixed self-dual binary basis. This
arbitrary-index construction is the computational-basis identification in the
proof of `lem:pauli-binary`, shared by the algebra and soundness modules. -/
noncomputable def quditQubitLabelEquiv {q : ℕ} {ι : Type*}
    (F : FixedFieldModel q) :
    (ι → F.K) ≃ (ι × Fin F.basisDim → ZMod 2) :=
  (Equiv.piCongrRight (fun _ : ι => F.binaryCoordinates.toEquiv)).trans
    (Equiv.curry ι (Fin F.basisDim) (ZMod 2)).symm

/-- The label equivalence is the uncurried form of `kappaVec`. -/
private theorem quditQubitLabelEquiv_eq_kappaVec {q : ℕ} {ι : Type*}
    (F : FixedFieldModel q) (u : ι → F.K) :
    quditQubitLabelEquiv F u = kappaVec F u := rfl

/-- Self-duality identifies the field trace pairing with the binary coordinate
pairing after relabeling. -/
private theorem binTrace_dotProduct_eq_quditQubitLabelEquiv
    {q : ℕ} {ι : Type*} [Fintype ι] (F : FixedFieldModel q) (a u : ι → F.K) :
    binTrace F.K (dotProduct a u) =
      binTrace (ZMod 2)
        (dotProduct (quditQubitLabelEquiv F a) (kappaVec F u)) := by
  simp only [dotProduct, map_sum, binTrace_mul_eq_dotProduct F,
    Algebra.trace_self_apply, Fintype.sum_prod_type, quditQubitLabelEquiv,
    Equiv.trans_apply, Equiv.curry_symm_apply, kappaVec, basisCoordVec]
  rfl

/-- The coordinate label equivalence preserves addition. -/
private theorem quditQubitLabelEquiv_add {q : ℕ} {ι : Type*}
    (F : FixedFieldModel q) (a b : ι → F.K) :
    quditQubitLabelEquiv F (a + b) =
      quditQubitLabelEquiv F a + quditQubitLabelEquiv F b := by
  ext p
  rcases p with ⟨i, j⟩
  change F.binaryCoordinates (a i + b i) j =
    F.binaryCoordinates (a i) j + F.binaryCoordinates (b i) j
  simp

/-- Binary-coordinate relabeling transports both generalized Pauli observables. -/
private theorem tauObservable_reindex_quditQubitLabelEquiv
    {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FixedFieldModel q)
    (W : PauliKind) (a : ι → F.K) :
    tauObservable W a =
      Matrix.reindex (quditQubitLabelEquiv F).symm
        (quditQubitLabelEquiv F).symm
        (tauObservable W (quditQubitLabelEquiv F a)) := by
  classical
  ext x y
  simp
  cases W with
  | X =>
      simp [tauObservable_X_apply]
      have hadd := quditQubitLabelEquiv_add F y a
      rw [← hadd]
      simp
  | Z =>
      rw [tauObservable_Z_apply, tauObservable_Z_apply]
      by_cases hxy : x = y
      · subst y
        rw [if_pos rfl, if_pos rfl,
          binTrace_dotProduct_eq_quditQubitLabelEquiv,
          quditQubitLabelEquiv_eq_kappaVec F a,
          quditQubitLabelEquiv_eq_kappaVec F x]
      · simp_all

/-- Fourier inversion transports the Pauli projectors along the binary label
equivalence for any finite register index. This is the shared algebraic
calculation in `lem:pauli-binary`, `eq:qudit-to-qubit-pauli-1`, independent of
the soundness existence assertion in `cor:pauli-binary`. -/
theorem pauliProj_reindex_quditQubitLabelEquiv
    {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FixedFieldModel q)
    (W : PauliKind) (u : ι → F.K) :
    pauliProj W u =
      Matrix.reindex (quditQubitLabelEquiv F).symm
        (quditQubitLabelEquiv F).symm
        (pauliProj W (kappaVec F u)) := by
  classical
  rw [pauliProj_eq_avg_tauObservable, pauliProj_eq_avg_tauObservable]
  ext x y
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [Fintype.card_congr (quditQubitLabelEquiv (ι := ι) F)]
  congr 1
  apply Fintype.sum_equiv (quditQubitLabelEquiv F)
  intro a
  have hphase := congrArg phaseSign
    (binTrace_dotProduct_eq_quditQubitLabelEquiv F a u)
  have hentry := congrFun
    (congrFun (tauObservable_reindex_quditQubitLabelEquiv F W a) x) y
  simp at hentry
  simp_all

/-- The tensor product of binary Pauli projectors, obtained by specializing
`pauliProj` to `ZMod 2`. This is the binary target in blueprint
`lem:pauli-binary`, paper
`references/qpbt-paper/04_preliminaries.tex:1163-1208`. -/
noncomputable abbrev qubitPauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (b : ι → ZMod 2) : Op (ι → ZMod 2) :=
  pauliProj W b

end MIPStarRE.QPBT
