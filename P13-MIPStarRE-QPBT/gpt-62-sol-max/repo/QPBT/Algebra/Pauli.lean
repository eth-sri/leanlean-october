module

public import QPBT.Upstream
public import QPBT.Algebra.FieldBasis
public import MIPStarRE.Quantum.FiniteMatrix.Basic
public import MIPStarRE.LDT.Preliminaries.FiniteFields

/-!
# Generalized Pauli operators and EPR states

The definitions here use finite matrix entries and rank-one projectors, so they
are usable by the later game statements without introducing an abstract
operator algebra.  The observable/projector expansions are obtained from
finite-field Fourier orthogonality in characteristic two.

## References

The source-facing nodes are blueprint `def:lin-reg`, `def:EPR`,
`def:generalized-pauli`, and `lem:pauli-observable-expansion`.  The paper origin is
`references/qpbt-paper/04_preliminaries.tex:908-1161`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum
open MIPStarRE.LDT.Preliminaries

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K]

/-- The two generalized Pauli bases used by the test in blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
inductive PauliKind where
  | X
  | Z
  deriving DecidableEq, Repr, Inhabited
instance PauliKind.instFintype : Fintype PauliKind :=
  ⟨{.X, .Z}, by intro x; cases x <;> simp⟩

/-- The other Pauli basis. -/
def PauliKind.other : PauliKind → PauliKind
  | .X => .Z
  | .Z => .X

/-- Select the component of a pair in the indicated Pauli basis. -/
def PauliKind.component {α : Type*} : PauliKind → α × α → α
  | .X, o => o.1
  | .Z, o => o.2

/-- The binary character used for generalized Pauli phases; see
`references/qpbt-paper/04_preliminaries.tex:1052-1081`.

It is public because the Fourier expansion declarations below expose this
character in their statement types. -/
noncomputable def phaseSign (t : ZMod 2) : ℂ :=
  if t = 0 then 1 else -1

/-- Formalization-only expansion of a sum over the binary field into its two
terms. -/
theorem sum_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ b, f b = f 0 + f 1 := by
  exact Fin.sum_univ_two (f ∘ ZMod.finEquiv 2)

/-- Formalization-only case split for the binary field: every element is zero
or one. -/
theorem zmod_two_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- In characteristic two, the standard additive character is the sign
character used by the binary Pauli definitions. -/
theorem phaseSign_eq_ffChar (t : ZMod 2) :
    phaseSign t = ZMod.stdAddChar (N := 2) t := by
  rcases zmod_two_eq_zero_or_one t with rfl | rfl
  · simp [phaseSign]
  · rw [phaseSign, if_neg one_ne_zero]
    change (-1 : ℂ) = ZMod.stdAddChar (N := 2) ((1 : ℤ) : ZMod 2)
    rw [ZMod.stdAddChar_coe]
    convert Complex.exp_pi_mul_I.symm using 1 <;> ring_nf

/-- The binary sign character carries a sum to the product of the two signs.
This is the character property underlying blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem phaseSign_add (s t : ZMod 2) :
    phaseSign (s + t) = phaseSign s * phaseSign t := by
  simpa only [phaseSign_eq_ffChar] using AddChar.map_add_eq_mul ZMod.stdAddChar s t

/-- The binary sign character takes real values, so conjugation fixes it. It is
used by the observable expansions of blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem star_phaseSign (t : ZMod 2) : star (phaseSign t) = phaseSign t := by
  by_cases ht : t = 0 <;> simp_all [phaseSign]

/-- The binary sign character squares to one, since the binary field has
characteristic two. This is the eigenvalue property used by the observables of
blueprint `def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem phaseSign_mul_self (t : ZMod 2) : phaseSign t * phaseSign t = 1 := by
  rw [← phaseSign_add, CharTwo.add_self_eq_zero]
  rfl

/-- The binary sign character sends sums to products. -/
theorem phaseSign_sum {ι : Type*} [Fintype ι] (f : ι → ZMod 2) :
    phaseSign (∑ i, f i) = ∏ i, phaseSign (f i) := by
  simpa only [phaseSign_eq_ffChar, AddChar.toMonoidHom_apply, toAdd_prod, toAdd_ofAdd] using
    map_prod ((ZMod.stdAddChar (N := 2)).toMonoidHom) (fun i => Multiplicative.ofAdd (f i)) Finset.univ

omit [Fintype K] [DecidableEq K] in
/-- The product of the coordinate phases is the phase of the trace pairing. -/
theorem prod_phaseSign_binTrace_dotProduct {ι : Type*} [Fintype ι]
    (u v : ι → K) :
    ∏ i, phaseSign (binTrace K (u i * v i)) =
      phaseSign (binTrace K (dotProduct u v)) := by
  rw [← phaseSign_sum]
  congr 2
  simp [dotProduct]

/-- The complex amplitude `(√n)⁻¹` normalizing a uniform superposition over `n`
basis vectors squares to `n⁻¹`.

This formalization-only normalization identity supports the Pauli normalizer
of blueprint `def:EPR`, paper origin
`references/qpbt-paper/04_preliminaries.tex:908-950`, and the seed-fiber and
correlated-ancilla amplitudes of the direct low-degree transport. -/
theorem inv_sqrt_natCast_mul_self (n : ℕ) :
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (n : ℂ)⁻¹ := by
  rw [← mul_inv_rev, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _),
    Complex.ofReal_natCast]

/-- Conjugated form of `inv_sqrt_natCast_mul_self`: the normalizing amplitude
`(√n)⁻¹` is real, so pairing it with its conjugate again gives `n⁻¹`.  This
formalization-only auxiliary is the form in which the identity occurs in Born
amplitudes, where the bra side carries the conjugate. -/
theorem inv_sqrt_natCast_mul_conj (n : ℕ) :
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
        (starRingEnd ℂ) (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (n : ℂ)⁻¹ := by
  rw [show (starRingEnd ℂ) (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (Real.sqrt (n : ℝ) : ℂ)⁻¹ by simp]
  exact inv_sqrt_natCast_mul_self n

omit [Field K] [DecidableEq K] [Algebra (ZMod 2) K] in
private theorem pauliNormalizer_mul_self {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    (∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) *
        (∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) =
      (Fintype.card (ι → K) : ℂ)⁻¹ := by
  simp only [Finset.prod_const, Finset.card_univ]
  rw [← mul_pow, inv_sqrt_natCast_mul_self, inv_pow, Fintype.card_fun]
  norm_cast

omit [Fintype K] [DecidableEq K] in
private theorem phaseSign_binTrace_dotProduct_add {ι : Type*} [Fintype ι]
    (u v w : ι → K) :
    phaseSign (binTrace K (dotProduct u v)) *
        phaseSign (binTrace K (dotProduct u w)) =
      phaseSign (binTrace K (dotProduct u (v + w))) := by
  rw [← phaseSign_add]
  congr 2
  simp

private local instance charP_binaryExtension : CharP K 2 :=
  (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)

omit [Fintype K] [DecidableEq K] in
private theorem tuple_add_eq_zero {ι : Type*} (u v : ι → K) : u + v = 0 ↔ u = v := by
  exact ⟨fun h => funext fun i => CharTwo.add_eq_zero.mp (congrFun h i),
    fun h => funext fun i => CharTwo.add_eq_zero.mpr (congrFun h i)⟩

private theorem sum_phaseSign_dotProduct {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ι → K) :
    ∑ u : ι → K, phaseSign (binTrace K (dotProduct u v)) =
      if v = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
  simpa only [phaseSign_eq_ffChar, ffChar_apply, dotProduct] using
    (sum_ffChar_sum_mul (p := 2) v)

/--
The shift operator `τ^X(a)`.  Blueprint `def:generalized-pauli`; paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
noncomputable def tauShift (a : K) : Op K :=
  fun i j => if i = j + a then 1 else 0

/--
The phase operator `τ^Z(b)`, with the fixed binary trace in the phase.  It is
the second operator of blueprint `def:generalized-pauli`; paper
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
noncomputable def tauPhase (b : K) : Op K :=
  fun i j => if i = j then phaseSign (binTrace K (b * j)) else 0

/-- The binary shift Pauli operator is Hermitian.  This is a
formalization-only specialization of the generalized Pauli definition. -/
theorem binaryTauShift_conjTranspose :
    (tauShift (K := ZMod 2) 1)ᴴ = tauShift (K := ZMod 2) 1 := by
  ext i j
  have hiff : j = i + 1 ↔ i = j + 1 := by
    rw [CharTwo.eq_add_iff_add_eq, eq_comm]
  simp_all [tauShift]

/-- The binary phase Pauli operator is Hermitian.  This is a
formalization-only specialization of the generalized Pauli definition. -/
theorem binaryTauPhase_conjTranspose :
    (tauPhase (K := ZMod 2) 1)ᴴ = tauPhase (K := ZMod 2) 1 := by
  ext i j
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [tauPhase, phaseSign, Matrix.conjTranspose_apply,
        Algebra.trace_self_apply]

/-- The binary shift Pauli operator is symmetric.  This formalization-only
identity supports transport across an EPR state. -/
theorem binaryTauShift_transpose :
    (tauShift (K := ZMod 2) 1)ᵀ = tauShift (K := ZMod 2) 1 := by
  ext i j
  have hiff : j = i + 1 ↔ i = j + 1 := by
    rw [CharTwo.eq_add_iff_add_eq, eq_comm]
  simp_all [tauShift]

/-- The binary phase Pauli operator is symmetric.  This formalization-only
identity supports transport across an EPR state. -/
theorem binaryTauPhase_transpose :
    (tauPhase (K := ZMod 2) 1)ᵀ = tauPhase (K := ZMod 2) 1 := by
  ext i j
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      rfl

/-- The binary shift Pauli operator squares to the identity.  This is a
formalization-only specialization of the generalized Pauli definition. -/
theorem binaryTauShift_sq :
    tauShift (K := ZMod 2) 1 * tauShift (K := ZMod 2) 1 = 1 := by
  ext i j
  simp [Matrix.mul_apply]
  rw [sum_zmod_two]
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      simp +decide [tauShift]

/-- The binary phase Pauli operator squares to the identity.  This is a
formalization-only specialization of the generalized Pauli definition. -/
theorem binaryTauPhase_sq :
    tauPhase (K := ZMod 2) 1 * tauPhase (K := ZMod 2) 1 = 1 := by
  ext i j
  simp [Matrix.mul_apply]
  rw [sum_zmod_two]
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [tauPhase, phaseSign, Matrix.one_apply, Algebra.trace_self_apply]

/-- The binary shift and phase Pauli operators anticommute.  This is a
formalization-only specialization of their generalized definitions. -/
theorem binaryTauShift_mul_tauPhase :
    tauShift (K := ZMod 2) 1 * tauPhase (K := ZMod 2) 1 =
      -(tauPhase (K := ZMod 2) 1 * tauShift (K := ZMod 2) 1) := by
  ext i j
  change
    (∑ k, tauShift (K := ZMod 2) 1 i k * tauPhase (K := ZMod 2) 1 k j) =
      -(∑ k, tauPhase (K := ZMod 2) 1 i k * tauShift (K := ZMod 2) 1 k j)
  rw [sum_zmod_two, sum_zmod_two]
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      simp [tauShift, tauPhase, phaseSign]

/-- The single-qudit eigenvector coordinate used in the tensor-product basis;
see `references/qpbt-paper/04_preliminaries.tex:1126-1161`. -/
noncomputable def singlePauliVec (W : PauliKind) (e x : K) : ℂ :=
  match W with
  | .Z => if x = e then 1 else 0
  | .X =>
      (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ * phaseSign (binTrace K (e * x))

/--
The normalized single/multi-qudit eigenvector for a Pauli basis label.  For an
index type `ι`, the input `e : ι → K` labels the tensor-product basis vector.
This is the vector form of blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`.
-/
noncomputable def pauliVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) (x : ι → K) : ℂ :=
  ∏ i : ι, singlePauliVec W (e i) (x i)

/--
The rank-one projector onto `pauliVec W e`.  This is the projective measurement
element `τ^W_e` in blueprint `def:generalized-pauli`; paper
`references/qpbt-paper/04_preliminaries.tex:1101-1122`.
-/
noncomputable def pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) : Op (ι → K) :=
  Matrix.vecMulVec (pauliVec W e) (fun x => star (pauliVec W e x))

private theorem pauliVec_Z_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (e x : ι → K) :
    pauliVec .Z e x = if x = e then 1 else 0 := by
  simp [pauliVec, singlePauliVec, Fintype.prod_ite_zero, ← funext_iff]

private theorem pauliVec_X_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (e x : ι → K) :
    pauliVec .X e x = (∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) *
      phaseSign (binTrace K (dotProduct e x)) := by
  simp only [pauliVec, singlePauliVec, Finset.prod_mul_distrib, prod_phaseSign_binTrace_dotProduct]

private theorem star_pauliVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e x : ι → K) : star (pauliVec W e x) = pauliVec W e x := by
  cases W
  · simp [pauliVec_X_apply, star_phaseSign, star_mul, mul_comm, star_prod, star_inv₀,
      show star (↑(Real.sqrt (Fintype.card K : ℝ)) : ℂ) = ↑(Real.sqrt (Fintype.card K : ℝ)) by simp]
  · by_cases h : x = e <;> simp [pauliVec_Z_apply, h]

private theorem pauliProj_X_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e x y : ι → K) :
    pauliProj .X e x y =
      (Fintype.card (ι → K) : ℂ)⁻¹ *
        phaseSign (binTrace K (dotProduct e (x + y))) := by
  rw [pauliProj, Matrix.vecMulVec_apply, star_pauliVec, pauliVec_X_apply, pauliVec_X_apply,
    mul_mul_mul_comm, pauliNormalizer_mul_self, phaseSign_binTrace_dotProduct_add]

/-- Generalized Pauli eigenspace projectors are symmetric matrices in
characteristic two. For the `X` basis this uses `x + y = y + x` in the
character formula; for the `Z` basis the projector is diagonal. This is the
EPR-transport property used in `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem pauliProj_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) :
    (pauliProj W e)ᵀ = pauliProj W e := by
  ext x y
  rw [Matrix.transpose_apply]
  cases W with
  | X =>
      simp [pauliProj_X_apply, add_comm]
  | Z =>
      simp only [pauliProj, Matrix.vecMulVec_apply, star_pauliVec, mul_comm]

/-- Generalized Pauli eigenspace projectors are mutually orthogonal. This is
the orthogonal-projector calculation used for the ancillary point measurement
in `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem pauliProj_mul_pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e f : ι → K) :
    pauliProj W e * pauliProj W f =
      if e = f then pauliProj W e else 0 := by
  have hinner : dotProduct (fun x => star (pauliVec W e x)) (pauliVec W f) =
      if e = f then 1 else 0 := by
    cases W
    · simp_rw [dotProduct, star_pauliVec, pauliVec_X_apply]
      conv_lhs =>
        enter [2, x]
        rw [mul_mul_mul_comm, pauliNormalizer_mul_self, dotProduct_comm e,
          dotProduct_comm f, phaseSign_binTrace_dotProduct_add]
      rw [← Finset.mul_sum, sum_phaseSign_dotProduct]
      simp only [tuple_add_eq_zero]
      split_ifs <;> simp [Fintype.card_ne_zero]
    · by_cases h : e = f
      · subst f; simp [dotProduct, star_pauliVec, pauliVec_Z_apply, mul_ite]
      · simp [dotProduct, star_pauliVec, pauliVec_Z_apply, mul_ite, h, Ne.symm h]
  simp only [pauliProj, Matrix.vecMulVec_mul_vecMulVec, hinner]
  split_ifs with h <;> simp [h]

/-- A compact operator-valued form of a generalized Pauli observable from
blueprint `def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
noncomputable def tauObservable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (a : ι → K) : Op (ι → K) :=
  fun x y => match W with
    | .X => if x = y + a then 1 else 0
    | .Z => if x = y then phaseSign (binTrace K (dotProduct a y)) else 0

omit [Fintype K] in
/-- A shift observable is the permutation matrix for addition by its label. -/
theorem tauObservable_X_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a x y : ι → K) :
    tauObservable .X a x y = if x = y + a then 1 else 0 := rfl

omit [Fintype K] in
/-- A phase observable is diagonal, with phase given by the trace pairing. -/
theorem tauObservable_Z_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a x y : ι → K) :
    tauObservable .Z a x y = if x = y then phaseSign (binTrace K (dotProduct a y)) else 0 := rfl

/--
The EPR vector on a finite label space.  Blueprint `def:EPR`; paper origin
`references/qpbt-paper/04_preliminaries.tex:946-955`.
-/
noncomputable def eprState (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    EuclideanSpace ℂ (V × V) :=
  (EuclideanSpace.equiv (V × V) ℂ).symm
    (fun p : V × V =>
      if p.1 = p.2 then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0)

/-- The EPR vector is normalized on a nonempty finite carrier; see
`def:EPR`, `references/qpbt-paper/04_preliminaries.tex:946-955`. -/
theorem eprState_norm (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    ‖eprState V‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.norm_sq_eq]
  change
    (∑ p : V × V,
      ‖if p.1 = p.2 then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0‖ ^ 2) =
      1 ^ 2
  rw [Fintype.sum_prod_type]
  have hcard : 0 < (Fintype.card V : ℝ) := by positivity
  calc
    _ =
        ∑ _x : V, ‖(Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy
        simp [hy.symm]
      · simp
    _ = 1 := by simp
    _ = 1 ^ 2 := by norm_num

/--
Fourier expansion of a generalized Pauli observable in the Pauli projectors.
This theorem is the characteristic-two (binary) specialization of the forward
identity `eq:pauli-obs-proj` in `lem:pauli-observable-expansion`,
with blueprint source `lem:pauli-observable-expansion`; paper origin
`references/qpbt-paper/04_preliminaries.tex:1151-1161`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`.
-/
theorem tauObservable_eq_sum_pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (a : ι → K) :
    tauObservable W a =
      ∑ e : ι → K, phaseSign (binTrace K (dotProduct a e)) • pauliProj W e := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  cases W with
  | X =>
      simp_rw [pauliProj_X_apply, tauObservable_X_apply,
        mul_left_comm _ (Fintype.card (ι → K) : ℂ)⁻¹, dotProduct_comm a,
        phaseSign_binTrace_dotProduct_add, ← Finset.mul_sum, sum_phaseSign_dotProduct,
        show a + (x + y) = x + (y + a) by abel, tuple_add_eq_zero]
      split_ifs <;> simp [Fintype.card_ne_zero]
  | Z =>
      simp only [tauObservable_Z_apply, pauliProj, Matrix.vecMulVec_apply, star_pauliVec,
        pauliVec_Z_apply, ite_mul, zero_mul, one_mul, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      by_cases h : x = y <;> simp_all [eq_comm]

/-- The inverse Fourier expansion of a Pauli projector.  This theorem is the
characteristic-two (binary) specialization of the inverse identity
`eq:pauli-inversion-0` in `lem:pauli-observable-expansion`,
with blueprint source `lem:pauli-observable-expansion`; paper origin
`references/qpbt-paper/04_preliminaries.tex:1151-1161`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`.
-/
theorem pauliProj_eq_avg_tauObservable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) :
    pauliProj W e =
      (Fintype.card (ι → K) : ℂ)⁻¹ •
        ∑ a : ι → K, phaseSign (binTrace K (dotProduct a e)) • tauObservable W a := by
  have hcoeff (x : ι → K) :
      ∑ i : ι → K,
          (Fintype.card (ι → K) : ℂ)⁻¹ *
            (phaseSign (binTrace K (dotProduct i e)) *
              phaseSign (binTrace K (dotProduct i x))) =
        if x = e then 1 else 0 := by
    rw [← Finset.mul_sum]
    simp_rw [phaseSign_binTrace_dotProduct_add, sum_phaseSign_dotProduct, tuple_add_eq_zero,
      eq_comm (a := e)]
    split_ifs <;> simp [Fintype.card_ne_zero]
  simp_rw [tauObservable_eq_sum_pauliProj]
  simp_rw [Finset.smul_sum, smul_smul]
  simp_all [Finset.sum_comm, ← Finset.sum_smul, hcoeff]

omit [Fintype K] in
/-- The generalized Pauli observable at the zero label is the identity, for
either Pauli kind.  blueprint
`def:generalized-pauli`. -/
theorem tauObservable_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (W : PauliKind) :
    tauObservable (K := K) W (0 : ι → K) = 1 := by
  ext x y
  cases W <;> simp [tauObservable, Matrix.one_apply, phaseSign]

/-- The Pauli basis projectors of one kind sum to the identity: they are the
effects of a complete measurement.  This is the Fourier expansion
`tauObservable_eq_sum_pauliProj` of `lem:pauli-observable-expansion` at the zero
label, blueprint `lem:pauli-observable-expansion`, paper
`references/qpbt-paper/04_preliminaries.tex:1151-1161`. -/
theorem sum_pauliProj_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (W : PauliKind) :
    (∑ e : ι → K, pauliProj W e) = 1 := by
  simpa [phaseSign, tauObservable_zero] using
    (tauObservable_eq_sum_pauliProj W (0 : ι → K)).symm

/-- Each Pauli basis projector is positive semidefinite: it is the rank-one
outer product of the normalized Pauli eigenvector with itself. -/
theorem posSemidef_pauliProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) : (pauliProj W e).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

end MIPStarRE.QPBT
