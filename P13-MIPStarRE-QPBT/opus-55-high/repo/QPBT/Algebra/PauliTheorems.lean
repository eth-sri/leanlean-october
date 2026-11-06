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

/-- The multi-qudit observable in `lem:twisted-commutation`, with `false`
denoting phase; blueprint `lem:twisted-commutation`, paper
`04_preliminaries.tex:1073-1095,1141-1151`. -/
noncomputable def primeTauObservable {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (a : ι → K) : Op (ι → K) :=
  fun x y => ∏ i : ι, if W then primeTauShift (p := p) (a i) (x i) (y i)
    else primeTauPhase (p := p) (a i) (x i) (y i)

/-- The coordinatewise tensor-entry presentation used by the Pauli observables. -/
private def productMatrix {ι κ : Type*} [Fintype ι]
    (A : ι → Matrix κ κ ℂ) : Matrix (ι → κ) (ι → κ) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

/-- Matrix multiplication distributes over `productMatrix`. -/
private theorem productMatrix_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ]
    (A B : ι → Matrix κ κ ℂ) :
    (productMatrix A * productMatrix B : Matrix (ι → κ) (ι → κ) ℂ) =
      productMatrix (fun i => A i * B i) := by
  classical
  ext x y
  simpa only [productMatrix, Matrix.mul_apply, Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun i z => A i (x i) z * B i z (y i))).symm

/-- Two single-coordinate shifts compose by adding their displacements. -/
private theorem primeTauShift_mul {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] (a a' : K) :
    primeTauShift (p := p) a * primeTauShift (p := p) a' =
      primeTauShift (p := p) (a + a') := by
  ext x y
  simp [Matrix.mul_apply, primeTauShift, add_comm, add_left_comm]

/-- Two single-coordinate phases compose by adding their labels. -/
private theorem primeTauPhase_mul {p : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] (b b' : K) :
    primeTauPhase (p := p) b * primeTauPhase (p := p) b' =
      primeTauPhase (p := p) (b + b') := by
  ext x y
  simp [Matrix.mul_apply, primeTauPhase, add_mul, AddChar.map_add_eq_mul]

/-- The generalized Pauli observable with zero label is the identity. -/
private theorem primeTauObservable_zero {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) :
    primeTauObservable (p := p) W (0 : ι → K) = 1 := by
  classical
  ext x y
  cases W <;>
    simp only [primeTauObservable, if_true, Pi.zero_apply, primeTauShift,
      primeTauPhase, zero_mul, AddChar.map_zero_eq_one, Matrix.one_apply]
  all_goals
    by_cases hxy : ∀ i, x i = y i
    · have h : x = y := funext hxy
      simp [h]
    · simp only [not_forall] at hxy
      obtain ⟨i, hi⟩ := hxy
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
      have h : x ≠ y := fun hxy => hi (congr_fun hxy i)
      simp [h]

/-- The product identity blueprint
`eq:pauli-product-power`, paper `04_preliminaries.tex:1082-1089`. -/
theorem primeTauObservable_mul {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a a' : ι → K) :
    primeTauObservable (p := p) W a * primeTauObservable (p := p) W a' =
      primeTauObservable (p := p) W (a + a') := by
  cases W with
  | false =>
      change productMatrix (fun i => primeTauPhase (p := p) (a i)) *
          productMatrix (fun i => primeTauPhase (p := p) (a' i)) =
        productMatrix (fun i => primeTauPhase (p := p) ((a + a') i))
      simpa [primeTauPhase_mul] using
        (productMatrix_mul
          (A := fun i => primeTauPhase (p := p) (a i))
          (B := fun i => primeTauPhase (p := p) (a' i)))
  | true =>
      change productMatrix (fun i => primeTauShift (p := p) (a i)) *
          productMatrix (fun i => primeTauShift (p := p) (a' i)) =
        productMatrix (fun i => primeTauShift (p := p) ((a + a') i))
      simpa [primeTauShift_mul] using
        (productMatrix_mul
          (A := fun i => primeTauShift (p := p) (a i))
          (B := fun i => primeTauShift (p := p) (a' i)))

/-- Natural powers of a generalized Pauli observable multiply its label by
repeated addition. -/
private theorem primeTauObservable_pow_nat {p : ℕ} {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    [Fintype ι] [DecidableEq ι] (W : Bool) (a : ι → K) (n : ℕ) :
    (primeTauObservable (p := p) W a) ^ n =
      primeTauObservable (p := p) W (fun i => n • a i) := by
  induction n with
  | zero =>
      rw [pow_zero]
      have hzero : (fun i => (0 : ℕ) • a i) = (0 : ι → K) := by
        funext i
        simp
      rw [hzero]
      exact (primeTauObservable_zero (p := p) (K := K) (ι := ι) W).symm
  | succ n ih =>
      calc
        (primeTauObservable (p := p) W a) ^ (n + 1) =
            (primeTauObservable (p := p) W a) ^ n *
              primeTauObservable (p := p) W a := pow_succ _ _
        _ = primeTauObservable (p := p) W (fun i => n • a i) *
              primeTauObservable (p := p) W a := by rw [ih]
        _ = primeTauObservable (p := p) W ((fun i => n • a i) + a) :=
              primeTauObservable_mul W _ _
        _ = primeTauObservable (p := p) W (fun i => (n + 1) • a i) := by
              have hlabels : ((fun i => n • a i) + a) =
                  (fun i => (n + 1) • a i) := by
                funext i
                rw [Pi.add_apply, add_nsmul, one_nsmul]
              exact congrArg
                (fun c => primeTauObservable (p := p) W c) hlabels

/-- The characteristic-`p` consequence of `primeTauObservable_pow`, blueprint
`eq:pauli-product-power`, paper `04_preliminaries.tex:1088-1089`. -/
theorem primeTauObservable_pow_char {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] (W : Bool) (a : ι → K) :
    (primeTauObservable (p := p) W a) ^ p = 1 := by
  haveI : CharP K p := (Algebra.charP_iff (ZMod p) K p).mp (ZMod.charP p)
  rw [primeTauObservable_pow_nat]
  have hlabel : (fun i => p • a i) = (0 : ι → K) := by
    funext i
    simp [nsmul_eq_mul, CharP.cast_eq_zero]
  rw [hlabel, primeTauObservable_zero]

/-- A single-coordinate shift and phase satisfy the generalized Pauli twisted
commutation relation. -/
private theorem primeTauShift_mul_primeTauPhase {p : ℕ} {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K]
    (a b : K) :
    primeTauShift (p := p) a * primeTauPhase (p := p) b =
      (ffChar (p := p) (F := K) (-a * b)) •
        (primeTauPhase (p := p) b * primeTauShift (p := p) a) := by
  ext x y
  by_cases hxy : x = y + a
  · subst x
    simp only [Matrix.mul_apply, primeTauShift, primeTauPhase, Matrix.smul_apply,
      smul_eq_mul]
    simp only [add_left_inj, mul_ite, ite_mul, one_mul, zero_mul, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, mul_one]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring_nf
  · simp [Matrix.mul_apply, primeTauShift, primeTauPhase, Matrix.smul_apply, hxy]

/-- The source multi-qudit twisted relation blueprint
`eq:twisted-fq`, paper `04_preliminaries.tex:1090-1095,1141-1151`. -/
theorem primeTauObservable_X_mul_Z {p : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Fact p.Prime] [Algebra (ZMod p) K] [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (a b : ι → K) :
    primeTauObservable (p := p) true a * primeTauObservable (p := p) false b =
      (ffChar (p := p) (F := K) (-dotProduct a b)) •
        (primeTauObservable (p := p) false b * primeTauObservable (p := p) true a) := by
  let ψ := ffChar (p := p) (F := K)
  have hchar : ψ (-dotProduct a b) = ∏ i, ψ (-(a i) * b i) := by
    calc
      ψ (-dotProduct a b) = ψ (∑ i, -(a i) * b i) := by
        congr 1
        simp [dotProduct]
      _ = ∏ i, ψ (-(a i) * b i) := by
        simpa only [AddChar.toMonoidHom_apply, toAdd_prod, toAdd_ofAdd] using
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
  rw [← hchar]

/-- The canonical finite-field character at `p = 2` is `phaseSign` composed
with the binary trace. -/
private theorem ffChar_two_eq_phaseSign {K : Type*} [Field K]
    [Algebra (ZMod 2) K] (x : K) :
    ffChar (p := 2) (F := K) x = phaseSign (binTrace K x) := by
  rw [ffChar_apply]
  exact (phaseSign_eq_ffChar (binTrace K x)).symm

/-- The binary Pauli observable is the characteristic-two specialization of
the prime-characteristic observable. -/
private theorem tauObservable_eq_primeTauObservable {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι]
    [DecidableEq ι] (W : PauliKind) (a : ι → K) :
    tauObservable W a = primeTauObservable (p := 2)
      (match W with | .X => true | .Z => false) a := by
  cases W with
  | X =>
      ext x y
      rfl
  | Z =>
      ext x y
      simp only [tauObservable, primeTauObservable, Bool.false_eq_true, if_false,
        tauPhase, primeTauPhase]
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hxy : x i = y i
      · rw [if_pos hxy, if_pos hxy, ffChar_apply]
        exact phaseSign_eq_ffChar _
      · rw [if_neg hxy, if_neg hxy]

/-- With no coordinates, every binary Pauli observable is the identity. -/
private theorem tauObservable_eq_one_of_isEmpty {K ι : Type*} [Field K]
    [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι]
    [DecidableEq ι] [IsEmpty ι] (W : PauliKind) (a : ι → K) :
    tauObservable W a = 1 := by
  classical
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
  cases W with
  | X =>
      simpa only [tauObservable_eq_primeTauObservable] using
        (primeTauObservable_mul (p := 2) true a a')
  | Z =>
      simpa only [tauObservable_eq_primeTauObservable] using
        (primeTauObservable_mul (p := 2) false a a')

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
      letI : IsEmpty ι := hι
      rw [tauObservable_eq_one_of_isEmpty]
      simp [dotProduct, phaseSign]
  | inr hι =>
      letI : Nonempty ι := hι
      have hphase : ffChar (p := 2) (F := K) (-dotProduct a b) =
          phaseSign (binTrace K (dotProduct a b)) := by
        rw [ffChar_two_eq_phaseSign]
        congr 1
        rw [map_neg]
        exact ZMod.neg_eq_self_mod_two _
      simpa only [tauObservable_eq_primeTauObservable, hphase] using
        (primeTauObservable_X_mul_Z (p := 2) a b)

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
    quditQubitLabelEquiv F u = kappaVec F u := by
  rfl

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

/-- A shift observable is the permutation matrix for addition by its label. -/
theorem tauObservable_X_apply
    {K ι : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (a x y : ι → K) :
    tauObservable .X a x y = if x = y + a then 1 else 0 := by
  change (∏ i : ι, if x i = y i + a i then 1 else 0) = _
  rw [Fintype.prod_boole]
  have hsupport : (∀ i, x i = y i + a i) ↔ x = y + a := by
    simpa only [Pi.add_apply] using
      (funext_iff (f := x) (g := y + a)).symm
  simp only [hsupport]

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
  rw [Fintype.prod_ite_zero, prod_phaseSign_binTrace_dotProduct]
  have hsupport : (∀ i, x i = y i) ↔ x = y :=
    (funext_iff (f := x) (g := y)).symm
  simp only [hsupport]

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
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  cases W with
  | X =>
      rw [tauObservable_X_apply, tauObservable_X_apply]
      have hadd := quditQubitLabelEquiv_add F y a
      rw [← hadd]
      by_cases hshift : x = y + a
      · rw [if_pos hshift, if_pos]
        exact congrArg (quditQubitLabelEquiv F) hshift
      · rw [if_neg hshift, if_neg]
        exact fun h => hshift ((quditQubitLabelEquiv F).injective h)
  | Z =>
      rw [tauObservable_Z_apply, tauObservable_Z_apply]
      by_cases hxy : x = y
      · subst y
        rw [if_pos rfl, if_pos rfl,
          binTrace_dotProduct_eq_quditQubitLabelEquiv,
          quditQubitLabelEquiv_eq_kappaVec F a,
          quditQubitLabelEquiv_eq_kappaVec F x]
      · have hlabels : quditQubitLabelEquiv F x ≠
            quditQubitLabelEquiv F y := fun h =>
          hxy ((quditQubitLabelEquiv F).injective h)
        rw [if_neg hxy, if_neg hlabels]

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
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm] at hentry
  rw [hphase, hentry]

/-- The tensor product of binary Pauli projectors, obtained by specializing
`pauliProj` to `ZMod 2`. This is the binary target in blueprint
`lem:pauli-binary`, paper
`references/qpbt-paper/04_preliminaries.tex:1163-1208`. -/
noncomputable abbrev qubitPauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (b : ι → ZMod 2) : Op (ι → ZMod 2) :=
  pauliProj W b

end MIPStarRE.QPBT
