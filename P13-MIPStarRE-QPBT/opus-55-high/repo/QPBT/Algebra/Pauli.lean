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
  deriving DecidableEq, Inhabited
instance PauliKind.instFintype : Fintype PauliKind :=
  ⟨{.X, .Z}, by intro x; cases x <;> simp⟩
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
  calc
    ∑ b, f b = ∑ i : Fin 2, f (ZMod.finEquiv 2 i) := by
      rfl
    _ = f (ZMod.finEquiv 2 0) + f (ZMod.finEquiv 2 1) := Fin.sum_univ_two _
    _ = f 0 + f 1 := by rfl

/-- Formalization-only case split for the binary field: every element is zero
or one. -/
theorem zmod_two_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  by_cases hb : b = 0
  · simp_all
  · have hval_ne : b.val ≠ 0 := (ZMod.val_ne_zero b).mpr hb
    grind [ZMod.val_lt, ZMod.val_eq_one]

variable (t : ZMod 2)

/-- In characteristic two, the standard additive character is the sign
character used by the binary Pauli definitions. -/
theorem phaseSign_eq_ffChar :
    phaseSign t = ZMod.stdAddChar (N := 2) t := by
  by_cases ht : t = 0
  · subst t
    rw [phaseSign, if_pos rfl]
    simp
  · have hval : t.val = 1 := by
      have hval_ne : t.val ≠ 0 := (ZMod.val_ne_zero t).mpr ht
      have hval_lt : t.val < 2 := ZMod.val_lt t
      omega
    have ht_one : t = 1 := (ZMod.val_eq_one (by omega) t).mp hval
    subst t
    change (-1 : ℂ) = ZMod.stdAddChar (N := 2) ((1 : ℤ) : ZMod 2)
    rw [ZMod.stdAddChar_coe]
    convert Complex.exp_pi_mul_I.symm using 1
    all_goals ring_nf

/-- The binary sign character carries a sum to the product of the two signs.
This is the character property underlying blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem phaseSign_add (s t : ZMod 2) :
    phaseSign (s + t) = phaseSign s * phaseSign t := by
  rw [phaseSign_eq_ffChar, phaseSign_eq_ffChar, phaseSign_eq_ffChar]
  exact (ZMod.stdAddChar (N := 2)).map_add_eq_mul s t

/-- The binary sign character takes real values, so conjugation fixes it. It is
used by the observable expansions of blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem star_phaseSign : star (phaseSign t) = phaseSign t := by
  by_cases ht : t = 0 <;> simp [phaseSign, ht]

/-- The binary sign character squares to one, since the binary field has
characteristic two. This is the eigenvalue property used by the observables of
blueprint `def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem phaseSign_mul_self : phaseSign t * phaseSign t = 1 := by
  rw [← phaseSign_add]
  have hzero : t + t = 0 := by
    rcases zmod_two_eq_zero_or_one t with ht | ht <;> subst ht <;> decide
  rw [hzero, phaseSign, if_pos rfl]

variable {ι : Type*} [Fintype ι]

/-- The binary sign character sends sums to products. -/
theorem phaseSign_sum (f : ι → ZMod 2) :
    phaseSign (∑ i, f i) = ∏ i, phaseSign (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
      simp_all [Finset.sum_insert, Finset.prod_insert, phaseSign_add]

omit [Fintype K] [DecidableEq K] in
/-- The product of the coordinate phases is the phase of the trace pairing. -/
theorem prod_phaseSign_binTrace_dotProduct (u v : ι → K) :
    ∏ i, phaseSign (binTrace K (u i * v i)) =
      phaseSign (binTrace K (dotProduct u v)) := by
  simp [phaseSign_sum, dotProduct]

variable (n : ℕ)

/-- The complex amplitude `(√n)⁻¹` normalizing a uniform superposition over `n`
basis vectors squares to `n⁻¹`.

This formalization-only normalization identity supports the Pauli normalizer
of blueprint `def:EPR`, paper origin
`references/qpbt-paper/04_preliminaries.tex:908-950`, and the seed-fiber and
correlated-ancilla amplitudes of the direct low-degree transport. -/
theorem inv_sqrt_natCast_mul_self :
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (n : ℂ)⁻¹ := by
  calc
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
        ((Real.sqrt (n : ℝ) : ℂ) ^ 2)⁻¹ := by
      grind
    _ = ((n : ℝ) : ℂ)⁻¹ := by
      grind [Complex.ofReal_pow, Real.sq_sqrt, Nat.cast_nonneg]
    _ = (n : ℂ)⁻¹ := by norm_num

/-- Conjugated form of `inv_sqrt_natCast_mul_self`: the normalizing amplitude
`(√n)⁻¹` is real, so pairing it with its conjugate again gives `n⁻¹`.  This
formalization-only auxiliary is the form in which the identity occurs in Born
amplitudes, where the bra side carries the conjugate. -/
theorem inv_sqrt_natCast_mul_conj :
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
        (starRingEnd ℂ) (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (n : ℂ)⁻¹ := by
  rw [show (starRingEnd ℂ) (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (Real.sqrt (n : ℝ) : ℂ)⁻¹ by simp]
  exact inv_sqrt_natCast_mul_self n

omit [Field K] [DecidableEq K] [Algebra (ZMod 2) K] in
theorem pauliNormalizer_mul_self [DecidableEq ι] :
    (∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) *
        (∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) =
      (Fintype.card (ι → K) : ℂ)⁻¹ := by
  simp only [Finset.prod_const, Finset.card_univ]
  rw [← mul_pow, inv_sqrt_natCast_mul_self, inv_pow, Fintype.card_fun]
  norm_cast

omit [Fintype K] [DecidableEq K] in
theorem phaseSign_binTrace_dotProduct_add (u v w : ι → K) :
    phaseSign (binTrace K (dotProduct u v)) *
        phaseSign (binTrace K (dotProduct u w)) =
      phaseSign (binTrace K (dotProduct u (v + w))) := by
  simp [phaseSign_add, dotProduct, mul_add, Finset.sum_add_distrib]

omit [Fintype K] [DecidableEq K] in
theorem add_add_eq_zero_iff_eq_add {ι : Type*} (a x y : ι → K) :
    a + (x + y) = 0 ↔ x = y + a := by
  letI : CharP K 2 :=
    (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
  constructor
  · intro h
    funext i
    have hi : a i + (x i + y i) = 0 := by
      simpa using congrFun h i
    have hax : a i + x i = y i := (CharTwo.add_eq_zero).mp (by
      grind)
    calc
      x i = a i + (a i + x i) := (CharTwo.add_cancel_left (a i) (x i)).symm
      _ = a i + y i := by simp_all
      _ = y i + a i := add_comm _ _
  · intro h
    funext i
    have hxi : x i = y i + a i := by
      simpa using congrFun h i
    simp
    grind

theorem sum_phaseSign_dotProduct [DecidableEq ι] (v : ι → K) :
    ∑ u : ι → K, phaseSign (binTrace K (dotProduct u v)) =
      if v = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
  calc
    ∑ u : ι → K, phaseSign (binTrace K (dotProduct u v)) =
        ∑ u : ι → K, ffChar (p := 2) (F := K) (dotProduct u v) := by
      simp [phaseSign_eq_ffChar]
    _ = if v = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
      simpa only [dotProduct] using
        (sum_ffChar_sum_mul (p := 2) (F := K) (ι := ι) v)

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
  simp_all [tauShift, Matrix.conjTranspose_apply]

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
  simp_all [tauShift, Matrix.transpose_apply]

/-- The binary phase Pauli operator is symmetric.  This formalization-only
identity supports transport across an EPR state. -/
theorem binaryTauPhase_transpose :
    (tauPhase (K := ZMod 2) 1)ᵀ = tauPhase (K := ZMod 2) 1 := by
  ext i j
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [tauPhase, phaseSign, Matrix.transpose_apply,
        Algebra.trace_self_apply]

/-- The binary shift Pauli operator squares to the identity.  This is a
formalization-only specialization of the generalized Pauli definition. -/
theorem binaryTauShift_sq :
    tauShift (K := ZMod 2) 1 * tauShift (K := ZMod 2) 1 = 1 := by
  ext i j
  simp only [Matrix.mul_apply]
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      simp +decide [tauShift]

/-- The binary phase Pauli operator squares to the identity.  This is a
formalization-only specialization of the generalized Pauli definition. -/
theorem binaryTauPhase_sq :
    tauPhase (K := ZMod 2) 1 * tauPhase (K := ZMod 2) 1 = 1 := by
  ext i j
  simp only [Matrix.mul_apply]
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
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      simp +decide [tauShift, tauPhase, phaseSign]

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
noncomputable def pauliVec [DecidableEq ι]
    (W : PauliKind) (e : ι → K) (x : ι → K) : ℂ :=
  ∏ i : ι, singlePauliVec W (e i) (x i)

/--
The rank-one projector onto `pauliVec W e`.  This is the projective measurement
element `τ^W_e` in blueprint `def:generalized-pauli`; paper
`references/qpbt-paper/04_preliminaries.tex:1101-1122`.
-/
noncomputable def pauliProj [DecidableEq ι]
    (W : PauliKind) (e : ι → K) : Op (ι → K) :=
  Matrix.vecMulVec (pauliVec W e) (fun x => star (pauliVec W e x))

theorem pauliProj_X_apply [DecidableEq ι]
    (e x y : ι → K) :
    pauliProj .X e x y =
      (Fintype.card (ι → K) : ℂ)⁻¹ *
        phaseSign (binTrace K (dotProduct e (x + y))) := by
  change
    (∏ i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ *
        phaseSign (binTrace K (e i * x i))) *
      star (∏ i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ *
        phaseSign (binTrace K (e i * y i))) = _
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_phaseSign_binTrace_dotProduct, prod_phaseSign_binTrace_dotProduct]
  simp only [star_mul, star_phaseSign]
  have hstar :
      star (∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) =
        ∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ := by
    simp
  rw [hstar]
  calc
    (∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) *
          phaseSign (binTrace K (dotProduct e x)) *
        (phaseSign (binTrace K (dotProduct e y)) *
          ∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) =
        ((∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) *
          ∏ _i : ι, (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹) *
            (phaseSign (binTrace K (dotProduct e x)) *
              phaseSign (binTrace K (dotProduct e y))) := by ring
    _ = _ := by
      rw [pauliNormalizer_mul_self, phaseSign_binTrace_dotProduct_add]

/-- Generalized Pauli eigenspace projectors are symmetric matrices in
characteristic two. For the `X` basis this uses `x + y = y + x` in the
character formula; for the `Z` basis the projector is diagonal. This is the
EPR-transport property used in `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem pauliProj_transpose [DecidableEq ι]
    (W : PauliKind) (e : ι → K) :
    (pauliProj W e)ᵀ = pauliProj W e := by
  ext x y
  rw [Matrix.transpose_apply]
  cases W with
  | X =>
      simp [pauliProj_X_apply, add_comm]
  | Z =>
      have hreal (z : ι → K) : star (pauliVec .Z e z) = pauliVec .Z e z := by
        simp [pauliVec, singlePauliVec]
      change pauliVec .Z e y * star (pauliVec .Z e x) =
        pauliVec .Z e x * star (pauliVec .Z e y)
      grind

/-- Generalized Pauli eigenspace projectors are mutually orthogonal. This is
the orthogonal-projector calculation used for the ancillary point measurement
in `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem pauliProj_mul_pauliProj [DecidableEq ι]
    (W : PauliKind) (e f : ι → K) :
    pauliProj W e * pauliProj W f =
      if e = f then pauliProj W e else 0 := by
  ext x z
  cases W with
  | X =>
      rw [Matrix.mul_apply]
      simp_rw [pauliProj_X_apply]
      have hsum :
          (∑ y : ι → K,
              ((Fintype.card (ι → K) : ℂ)⁻¹ *
                  phaseSign (binTrace K (dotProduct e (x + y)))) *
                ((Fintype.card (ι → K) : ℂ)⁻¹ *
                  phaseSign (binTrace K (dotProduct f (y + z))))) =
            (Fintype.card (ι → K) : ℂ)⁻¹ *
                (Fintype.card (ι → K) : ℂ)⁻¹ *
              phaseSign (binTrace K (dotProduct e x)) *
              phaseSign (binTrace K (dotProduct f z)) *
              ∑ y : ι → K,
                phaseSign (binTrace K (dotProduct y (e + f))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [← phaseSign_binTrace_dotProduct_add e x y,
          ← phaseSign_binTrace_dotProduct_add f y z,
          ← phaseSign_binTrace_dotProduct_add y e f,
          dotProduct_comm e y, dotProduct_comm f y]
        ring
      rw [hsum, sum_phaseSign_dotProduct]
      letI : CharP K 2 :=
        (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
      by_cases hef : e = f
      · subst f
        have hzero : e + e = 0 := by
          funext i
          exact CharTwo.add_self_eq_zero (e i)
        rw [if_pos rfl, if_pos hzero]
        rw [pauliProj_X_apply]
        have hcard : (Fintype.card (ι → K) : ℂ) ≠ 0 := by positivity
        grind [phaseSign_binTrace_dotProduct_add]
      · have hadd : e + f ≠ 0 := by
          intro h
          apply hef
          funext i
          exact CharTwo.add_eq_zero.mp (congrFun h i)
        simp_all
  | Z =>
      have hz (g y : ι → K) :
          pauliVec .Z g y = if y = g then 1 else 0 := by
        simp [pauliVec, singlePauliVec, Fintype.prod_ite_zero, ← funext_iff]
      by_cases hef : e = f
      · simp_all [pauliProj, Matrix.mul_apply, Matrix.vecMulVec_apply]
      simp_all [Ne.symm, pauliProj, Matrix.mul_apply, Matrix.vecMulVec_apply]

/-- A compact operator-valued form of a generalized Pauli observable from
blueprint `def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`.
-/
noncomputable def tauObservable [DecidableEq ι]
    (W : PauliKind) (a : ι → K) : Op (ι → K) :=
  fun x y =>
    ∏ i : ι,
      match W with
      | .X => tauShift (a i) (x i) (y i)
      | .Z => tauPhase (a i) (x i) (y i)

variable (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V]

/--
The EPR vector on a finite label space.  Blueprint `def:EPR`; paper origin
`references/qpbt-paper/04_preliminaries.tex:946-955`.
-/
noncomputable def eprState :
    EuclideanSpace ℂ (V × V) :=
  (EuclideanSpace.equiv (V × V) ℂ).symm
    (fun p : V × V =>
      if p.1 = p.2 then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0)

/-- The EPR vector is normalized on a nonempty finite carrier; see
`def:EPR`, `references/qpbt-paper/04_preliminaries.tex:946-955`. -/
theorem eprState_norm :
    ‖eprState V‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_prod_type]
  have hcard : 0 < (Fintype.card V : ℝ) := by positivity
  calc
    ∑ x : V, ∑ y : V,
        ‖if x = y then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0‖ ^ 2 =
        ∑ _x : V, ‖(Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy
        simp [hy.symm]
      · simp
    _ = 1 := by
      simp
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
theorem tauObservable_eq_sum_pauliProj [DecidableEq ι]
    (W : PauliKind) (a : ι → K) :
    tauObservable W a =
      ∑ e : ι → K, phaseSign (binTrace K (dotProduct a e)) • pauliProj W e := by
  ext x y
  rw [show
    (∑ e : ι → K, phaseSign (binTrace K (dotProduct a e)) • pauliProj W e) x y =
      ∑ e : ι → K,
        phaseSign (binTrace K (dotProduct a e)) * pauliProj W e x y by
          simp [Matrix.sum_apply]]
  cases W with
  | X =>
      change
        (∏ i : ι, if x i = y i + a i then 1 else 0) =
          ∑ e : ι → K,
            phaseSign (binTrace K (dotProduct a e)) * pauliProj .X e x y
      simp_rw [pauliProj_X_apply]
      rw [Fintype.prod_boole]
      have hsupport : (∀ i, x i = y i + a i) ↔ x = y + a := by
        simpa using
          (funext_iff (f := x) (g := y + a)).symm
      simp only [hsupport]
      have hsum :
          (∑ e : ι → K,
            phaseSign (binTrace K (dotProduct a e)) *
              ((Fintype.card (ι → K) : ℂ)⁻¹ *
                phaseSign (binTrace K (dotProduct e (x + y))))) =
            (Fintype.card (ι → K) : ℂ)⁻¹ *
              ∑ e : ι → K,
                phaseSign (binTrace K (dotProduct e (a + (x + y)))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        calc
          phaseSign (binTrace K (dotProduct a e)) *
                ((Fintype.card (ι → K) : ℂ)⁻¹ *
                  phaseSign (binTrace K (dotProduct e (x + y)))) =
              (Fintype.card (ι → K) : ℂ)⁻¹ *
                (phaseSign (binTrace K (dotProduct e a)) *
                  phaseSign (binTrace K (dotProduct e (x + y)))) := by
            grind [dotProduct_comm]
          _ = _ := by rw [phaseSign_binTrace_dotProduct_add]
      rw [hsum, sum_phaseSign_dotProduct]
      by_cases hsupport : x = y + a
      · have hzero : a + (x + y) = 0 :=
          (add_add_eq_zero_iff_eq_add a x y).mpr hsupport
        simp_all
      simp [add_add_eq_zero_iff_eq_add]
  | Z =>
      change
        (∏ i : ι, if x i = y i then phaseSign (binTrace K (a i * y i)) else 0) =
          ∑ e : ι → K, phaseSign (binTrace K (dotProduct a e)) *
            ((∏ i : ι, if x i = e i then 1 else 0) *
              star (∏ i : ι, if y i = e i then 1 else 0))
      simp only [Fintype.prod_ite_zero, Finset.prod_const_one]
      by_cases hxy : x = y
      · rw [prod_phaseSign_binTrace_dotProduct]
        simp [← funext_iff]
      · simp [← funext_iff, hxy]

/-- The inverse Fourier expansion of a Pauli projector.  This theorem is the
characteristic-two (binary) specialization of the inverse identity
`eq:pauli-inversion-0` in `lem:pauli-observable-expansion`,
with blueprint source `lem:pauli-observable-expansion`; paper origin
`references/qpbt-paper/04_preliminaries.tex:1151-1161`.

**Scope restriction:** This characteristic-two specialization is separated
from the general-prime identity as documented in
`docs/paper-gaps/qpbt_characteristic-two-pauli-scope.tex`.
-/
theorem pauliProj_eq_avg_tauObservable [DecidableEq ι]
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
    rw [show
      (∑ i : ι → K,
        phaseSign (binTrace K (dotProduct i e)) *
          phaseSign (binTrace K (dotProduct i x))) =
        ∑ i : ι → K, phaseSign (binTrace K (dotProduct i (e + x))) by
          simp [phaseSign_binTrace_dotProduct_add]]
    rw [sum_phaseSign_dotProduct]
    have hzero : e + x = 0 ↔ x = e := by
      simpa using
        (add_add_eq_zero_iff_eq_add (K := K) e x (0 : ι → K))
    by_cases hx : x = e
    · simp_all
    · simp_all
  simp_rw [tauObservable_eq_sum_pauliProj]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  simp_all

omit [Field K] [Fintype K] [Algebra (ZMod 2) K] in
/-- Formalization-only: a product of coordinate indicators is the indicator of
equality of the two tuples. -/
theorem prod_indicator_eq_one_apply (x y : ι → K) :
    (∏ _i : ι, (if x _i = y _i then (1 : ℂ) else 0)) = if x = y then 1 else 0 := by
  by_cases h : x = y
  · simp_all
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

omit [Fintype K] in
/-- The generalized Pauli observable at the zero label is the identity, for
either Pauli kind.  blueprint
`def:generalized-pauli`. -/
theorem tauObservable_zero [DecidableEq ι] (W : PauliKind) :
    tauObservable (K := K) W (0 : ι → K) = 1 := by
  ext x y
  rw [Matrix.one_apply, ← prod_indicator_eq_one_apply (K := K) x y]
  cases W <;>
    exact Finset.prod_congr rfl fun i _ => by
      simp [tauShift, tauPhase, phaseSign]

/-- The Pauli basis projectors of one kind sum to the identity: they are the
effects of a complete measurement.  This is the Fourier expansion
`tauObservable_eq_sum_pauliProj` of `lem:pauli-observable-expansion` at the zero
label, blueprint `lem:pauli-observable-expansion`, paper
`references/qpbt-paper/04_preliminaries.tex:1151-1161`. -/
theorem sum_pauliProj_eq_one [DecidableEq ι] (W : PauliKind) :
    (∑ e : ι → K, pauliProj W e) = 1 := by
  have h := tauObservable_eq_sum_pauliProj (K := K) W (0 : ι → K)
  rw [tauObservable_zero] at h
  rw [h]
  simp [dotProduct, phaseSign]

/-- Each Pauli basis projector is positive semidefinite: it is the rank-one
outer product of the normalized Pauli eigenvector with itself. -/
theorem posSemidef_pauliProj [DecidableEq ι]
    (W : PauliKind) (e : ι → K) : (pauliProj W e).PosSemidef := by
  set A : Matrix Unit (ι → K) ℂ :=
    Matrix.of (fun (_ : Unit) (x : ι → K) => star (pauliVec W e x)) with hA
  have h : pauliProj W e = Aᴴ * A := by
    ext x y
    rw [Matrix.mul_apply]
    simp [hA, pauliProj, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply]
  simp_all [Matrix.posSemidef_conjTranspose_mul_self]

end MIPStarRE.QPBT
