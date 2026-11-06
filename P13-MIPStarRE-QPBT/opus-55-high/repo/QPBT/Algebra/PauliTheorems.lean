module

public import QPBT.Algebra.Pauli
public import QPBT.Algebra.SelfDualBasisTheorems
public import QPBT.Algebra.Subspaces
public import QPBT.State
public import MIPStarRE.LDT.Preliminaries.FiniteFields

/-! # Pauli product, commutation, and cancellation identities

The principal results are blueprint `lem:twisted-commutation` and
`lem:cancellation`, from
`references/qpbt-paper/04_preliminaries.tex:1056-1095,1124-1151`. The
general-prime statements use the canonical character `ffChar`; binary
declarations below are separately named QPBT specializations.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum

/-- The shift observable in blueprint
`lem:twisted-commutation`, paper `04_preliminaries.tex:1056-1089`. -/
noncomputable def primeTauShift {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    (a : K) : Op K := fun i j => if i = j + a then 1 else 0

/-- The phase observable in blueprint
`lem:twisted-commutation`, paper `04_preliminaries.tex:1056-1089`. -/
noncomputable def primeTauPhase {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    (b : K) : Op K := fun i j =>
  if i = j then ffChar (p := p) (F := K) (b * j) else 0

variable {p : ℕ} {K ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fact p.Prime]

/-- The multi-qudit observable in `lem:twisted-commutation`, with `false`
denoting phase; blueprint `lem:twisted-commutation`, paper
`04_preliminaries.tex:1073-1095,1141-1151`. -/
noncomputable def primeTauObservable [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (a : ι → K) : Op (ι → K) :=
  fun x y => ∏ i : ι, if W then primeTauShift (p := p) (a i) (x i) (y i)
    else primeTauPhase (p := p) (a i) (x i) (y i)

/-- The coordinatewise tensor-entry presentation used by the Pauli observables. -/
def productMatrix {ι κ : Type*} [Fintype ι]
    (A : ι → Matrix κ κ ℂ) : Matrix (ι → κ) (ι → κ) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

/-- Matrix multiplication distributes over `productMatrix`. -/
theorem productMatrix_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ]
    (A B : ι → Matrix κ κ ℂ) :
    (productMatrix A * productMatrix B : Matrix (ι → κ) (ι → κ) ℂ) =
      productMatrix (fun i => A i * B i) := by
  ext x y
  simp [productMatrix, Matrix.mul_apply, Finset.prod_mul_distrib, Fintype.prod_sum, symm]

/-- Two single-coordinate shifts compose by adding their displacements. -/
theorem primeTauShift_mul {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] (a a' : K) :
    primeTauShift (p := p) a * primeTauShift (p := p) a' =
      primeTauShift (p := p) (a + a') := by
  ext x y
  simp [Matrix.mul_apply, primeTauShift, add_comm, add_left_comm]

/-- Two single-coordinate phases compose by adding their labels. -/
theorem primeTauPhase_mul {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] (b b' : K) :
    primeTauPhase (p := p) b * primeTauPhase (p := p) b' =
      primeTauPhase (p := p) (b + b') := by
  ext x y
  simp [Matrix.mul_apply, primeTauPhase, add_mul, AddChar.map_add_eq_mul]

/-- The generalized Pauli observable with zero label is the identity. -/
theorem primeTauObservable_zero [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) :
    primeTauObservable (p := p) W (0 : ι → K) = 1 := by
  ext x y
  cases W <;>
    simp only [primeTauObservable, if_true, Pi.zero_apply, primeTauShift,
      primeTauPhase, zero_mul, AddChar.map_zero_eq_one, Matrix.one_apply]
  all_goals
    by_cases hxy : ∀ i, x i = y i
    · have h : x = y := funext hxy
      simp_all
    · simp at hxy
      obtain ⟨i, hi⟩ := hxy
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp_all)]
      grind

/-- The product identity blueprint
`eq:pauli-product-power`, paper `04_preliminaries.tex:1082-1089`. -/
theorem primeTauObservable_mul [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a a' : ι → K) :
    primeTauObservable (p := p) W a * primeTauObservable (p := p) W a' =
      primeTauObservable (p := p) W (a + a') := by
  cases W with
  | false =>
      change productMatrix (fun i => primeTauPhase (p := p) (a i)) *
          productMatrix (fun i => primeTauPhase (p := p) (a' i)) =
        productMatrix (fun i => primeTauPhase (p := p) ((a + a') i))
      simp [primeTauPhase_mul, productMatrix_mul]
  | true =>
      change productMatrix (fun i => primeTauShift (p := p) (a i)) *
          productMatrix (fun i => primeTauShift (p := p) (a' i)) =
        productMatrix (fun i => primeTauShift (p := p) ((a + a') i))
      simp [primeTauShift_mul, productMatrix_mul]

/-- Natural powers of a generalized Pauli observable multiply its label by
repeated addition. -/
theorem primeTauObservable_pow_nat [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (a : ι → K) (n : ℕ) :
    (primeTauObservable (p := p) W a) ^ n =
      primeTauObservable (p := p) W (fun i => n • a i) := by
  induction n with
  | zero =>
      have hzero : (fun i => (0 : ℕ) • a i) = (0 : ι → K) := by
        funext i
        simp
      simp_all [primeTauObservable_zero, symm]
  | succ n ih =>
      calc
        (primeTauObservable (p := p) W a) ^ (n + 1) =
            (primeTauObservable (p := p) W a) ^ n *
              primeTauObservable (p := p) W a := pow_succ _ _
        _ = primeTauObservable (p := p) W (fun i => n • a i) *
              primeTauObservable (p := p) W a := by simp_all
        _ = primeTauObservable (p := p) W ((fun i => n • a i) + a) :=
              primeTauObservable_mul W _ _
        _ = primeTauObservable (p := p) W (fun i => (n + 1) • a i) := by
              have hlabels : ((fun i => n • a i) + a) =
                  (fun i => (n + 1) • a i) := by
                funext i
                rw [Pi.add_apply, add_nsmul, one_nsmul]
              simp_all

/-- The characteristic-`p` consequence of `primeTauObservable_pow`, blueprint
`eq:pauli-product-power`, paper `04_preliminaries.tex:1088-1089`. -/
theorem primeTauObservable_pow_char [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a : ι → K) :
    (primeTauObservable (p := p) W a) ^ p = 1 := by
  haveI : CharP K p := (Algebra.charP_iff (ZMod p) K p).mp (ZMod.charP p)
  rw [primeTauObservable_pow_nat]
  have hlabel : (fun i => p • a i) = (0 : ι → K) := by
    funext i
    simp
  simp_all [primeTauObservable_zero]

/-- A single-coordinate shift and phase satisfy the generalized Pauli twisted
commutation relation. -/
theorem primeTauShift_mul_primeTauPhase {p : ℕ} {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    (a b : K) :
    primeTauShift (p := p) a * primeTauPhase (p := p) b =
      (ffChar (p := p) (F := K) (-a * b)) •
        (primeTauPhase (p := p) b * primeTauShift (p := p) a) := by
  ext x y
  by_cases hxy : x = y + a
  · simp only [Matrix.mul_apply, primeTauShift, primeTauPhase, Matrix.smul_apply,
      smul_eq_mul]
    simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, mul_one]
    rw [← AddChar.map_add_eq_mul]
    ring_nf
  simp_all [Matrix.mul_apply, primeTauShift, primeTauPhase, Matrix.smul_apply]

/-- The source multi-qudit twisted relation blueprint
`eq:twisted-fq`, paper `04_preliminaries.tex:1090-1095,1141-1151`. -/
theorem primeTauObservable_X_mul_Z [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (a b : ι → K) :
    primeTauObservable (p := p) true a * primeTauObservable (p := p) false b =
      (ffChar (p := p) (F := K) (-dotProduct a b)) •
        (primeTauObservable (p := p) false b * primeTauObservable (p := p) true a) := by
  let ψ := ffChar (p := p) (F := K)
  have hchar : ψ (-dotProduct a b) = ∏ i, ψ (-(a i) * b i) := by
    calc
      ψ (-dotProduct a b) = ψ (∑ i, -(a i) * b i) := by
        simp [dotProduct]
      _ = ∏ i, ψ (-(a i) * b i) := by
        simpa using
          (map_prod ψ.toMonoidHom (fun i => Multiplicative.ofAdd (-(a i) * b i))
            Finset.univ)
  change productMatrix (fun i => primeTauShift (p := p) (a i)) *
      productMatrix (fun i => primeTauPhase (p := p) (b i)) =
    ψ (-dotProduct a b) •
      (productMatrix (fun i => primeTauPhase (p := p) (b i)) *
        productMatrix (fun i => primeTauShift (p := p) (a i)))
  rw [productMatrix_mul, productMatrix_mul]
  ext x y
  simp only [productMatrix, primeTauShift_mul_primeTauPhase, Matrix.smul_apply,
    smul_eq_mul, Finset.prod_mul_distrib]
  grind

/-- The canonical finite-field character at `p = 2` is `phaseSign` composed
with the binary trace. -/
theorem ffChar_two_eq_phaseSign {K : Type*} [Field K]
    [Algebra (ZMod 2) K] (x : K) :
    ffChar (p := 2) (F := K) x = phaseSign (binTrace K x) := by
  simp [phaseSign_eq_ffChar, binTrace, symm]

/-- The binary Pauli observable is the characteristic-two specialization of
the prime-characteristic observable. -/
theorem tauObservable_eq_primeTauObservable {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι]
    [DecidableEq ι] (W : PauliKind) (a : ι → K) :
    tauObservable W a = primeTauObservable (p := 2)
      (match W with | .X => true | .Z => false) a := by
  cases W with
  | X =>
      rfl
  | Z =>
      ext x y
      simp only [tauObservable, primeTauObservable, Bool.false_eq_true, if_false,
        tauPhase, primeTauPhase]
      simp [phaseSign_eq_ffChar]

/-- With no coordinates, every binary Pauli observable is the identity. -/
theorem tauObservable_eq_one_of_isEmpty {K ι : Type*} [Field K]
    [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι]
    [DecidableEq ι] [IsEmpty ι] (W : PauliKind) (a : ι → K) :
    tauObservable W a = 1 := by
  ext x y
  have hxy : x = y := Subsingleton.elim _ _
  subst y
  simp [tauObservable]

/-- Binary specialization of blueprint
`eq:pauli-product-power`, paper `04_preliminaries.tex:1082-1089`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`. -/
theorem tauObservable_mul {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (a a' : ι → K) :
    tauObservable W a * tauObservable W a' = tauObservable W (a + a') := by
  simp [tauObservable_eq_primeTauObservable, primeTauObservable_mul]

/-- Binary characteristic-two specialization of blueprint
`eq:pauli-product-power`, paper `04_preliminaries.tex:1088-1089`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`. -/
theorem tauObservable_sq {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι] (W : PauliKind) (a : ι → K) :
    tauObservable W a * tauObservable W a = 1 := by
  cases W with
  | X =>
      simpa only [tauObservable_eq_primeTauObservable, pow_two] using
        (primeTauObservable_pow_char (p := 2) true a)
  | Z =>
      simpa only [tauObservable_eq_primeTauObservable, pow_two] using
        (primeTauObservable_pow_char (p := 2) false a)

/-- Binary specialization of blueprint
`eq:twisted-fq`, paper `04_preliminaries.tex:1090-1095`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`. -/
theorem tauObservable_X_mul_Z {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι] (a b : ι → K) :
    tauObservable .X a * tauObservable .Z b =
      (phaseSign (binTrace K (dotProduct a b))) •
        (tauObservable .Z b * tauObservable .X a) := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      simp [tauObservable_eq_one_of_isEmpty, dotProduct, phaseSign]
  | inr hι =>
      have hphase : ffChar (p := 2) (F := K) (-dotProduct a b) =
          phaseSign (binTrace K (dotProduct a b)) := by
        rw [ffChar_two_eq_phaseSign]
        congr 1
        rw [map_neg]
        exact ZMod.neg_eq_self_mod_two _
      simp_all [tauObservable_eq_primeTauObservable, primeTauObservable_X_mul_Z]

variable {q : ℕ}

/-- Expand every register label in the fixed self-dual binary basis. This
arbitrary-index construction is the computational-basis identification in the
proof of `lem:pauli-binary`, shared by the algebra and soundness modules. -/
noncomputable def quditQubitLabelEquiv {ι : Type*}
    (F : FixedFieldModel q) :
    (ι → F.K) ≃ (ι × Fin F.basisDim → ZMod 2) :=
  (Equiv.piCongrRight (fun _ : ι => F.binaryCoordinates.toEquiv)).trans
    (Equiv.curry ι (Fin F.basisDim) (ZMod 2)).symm

/-- The label equivalence is the uncurried form of `kappaVec`. -/
theorem quditQubitLabelEquiv_eq_kappaVec {ι : Type*}
    (F : FixedFieldModel q) (u : ι → F.K) :
    quditQubitLabelEquiv F u = kappaVec F u := by
  rfl

/-- Self-duality identifies the field trace pairing with the binary coordinate
pairing after relabeling. -/
theorem binTrace_dotProduct_eq_quditQubitLabelEquiv
    {ι : Type*} [Fintype ι] (F : FixedFieldModel q) (a u : ι → F.K) :
    binTrace F.K (dotProduct a u) =
      binTrace (ZMod 2)
        (dotProduct (quditQubitLabelEquiv F a) (kappaVec F u)) := by
  simp [dotProduct, map_sum, binTrace_mul_eq_dotProduct, Fintype.sum_prod_type, quditQubitLabelEquiv, Equiv.trans_apply, Equiv.curry_symm_apply, kappaVec, basisCoordVec]

/-- The coordinate label equivalence preserves addition. -/
theorem quditQubitLabelEquiv_add {ι : Type*}
    (F : FixedFieldModel q) (a b : ι → F.K) :
    quditQubitLabelEquiv F (a + b) =
      quditQubitLabelEquiv F a + quditQubitLabelEquiv F b := by
  ext p
  rcases p with ⟨i, j⟩
  change F.binaryCoordinates (a i + b i) j =
    F.binaryCoordinates (a i) j + F.binaryCoordinates (b i) j
  simp

/-- A shift observable is the permutation matrix for addition by its label. -/
theorem tauObservable_X_apply
    {K ι : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (a x y : ι → K) :
    tauObservable .X a x y = if x = y + a then 1 else 0 := by
  change (∏ i : ι, if x i = y i + a i then 1 else 0) = _
  simp [Fintype.prod_boole, Pi.add_apply, funext_iff, symm]

/-- A phase observable is diagonal, with its phase given by the trace pairing. -/
theorem tauObservable_Z_apply
    {K ι : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (a x y : ι → K) :
    tauObservable .Z a x y =
      if x = y then phaseSign (binTrace K (dotProduct a y)) else 0 := by
  change
    (∏ i : ι,
      if x i = y i then phaseSign (binTrace K (a i * y i)) else 0) = _
  simp [Fintype.prod_ite_zero, prod_phaseSign_binTrace_dotProduct, funext_iff, symm]

/-- Binary-coordinate relabeling transports both generalized Pauli observables. -/
theorem tauObservable_reindex_quditQubitLabelEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FixedFieldModel q)
    (W : PauliKind) (a : ι → F.K) :
    tauObservable W a =
      Matrix.reindex (quditQubitLabelEquiv F).symm
        (quditQubitLabelEquiv F).symm
        (tauObservable W (quditQubitLabelEquiv F a)) := by
  ext x y
  simp
  cases W with
  | X =>
      rw [tauObservable_X_apply, tauObservable_X_apply]
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
      simp_all

/-- Fourier inversion transports the Pauli projectors along the binary label
equivalence for any finite register index. This is the shared algebraic
calculation in `lem:pauli-binary`, `eq:qudit-to-qubit-pauli-1`, independent of
the soundness existence assertion in `cor:pauli-binary`. -/
theorem pauliProj_reindex_quditQubitLabelEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FixedFieldModel q)
    (W : PauliKind) (u : ι → F.K) :
    pauliProj W u =
      Matrix.reindex (quditQubitLabelEquiv F).symm
        (quditQubitLabelEquiv F).symm
        (pauliProj W (kappaVec F u)) := by
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
  simp_all [congrFun, tauObservable_reindex_quditQubitLabelEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]

/-- The tensor product of binary Pauli projectors, obtained by specializing
`pauliProj` to `ZMod 2`. This is the binary target in blueprint
`lem:pauli-binary`, paper
`references/qpbt-paper/04_preliminaries.tex:1163-1208`. -/
noncomputable abbrev qubitPauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (b : ι → ZMod 2) : Op (ι → ZMod 2) :=
  pauliProj W b

end MIPStarRE.QPBT
