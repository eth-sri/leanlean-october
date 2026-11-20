module

public import MIPStarRE.LDT.Basic.ParametersBase

/-!
# Finite-field bases and the fixed binary representation

The Pauli basis test uses fields of size `2^k` for odd `k`, together with a
chosen self-dual normal basis over `ZMod 2`.  This file constructs such bases
and records the resulting fixed field model for later proofs.

## References

The declarations correspond to blueprint `def:admissible-size`,
`def:dual-self-dual-normal-basis`, `def:subfields-kappa`, `def:subfield-trace`,
and `def:binary-representation`.
Their paper origin is `references/qpbt-paper/04_preliminaries.tex:433-502,653-728`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

/-- `IsAdmissibleSize q` is the predicate `q = 2^k` for an odd exponent.
This is blueprint `def:admissible-size`, with paper origin
`references/qpbt-paper/04_preliminaries.tex:662-667`.
-/
def IsAdmissibleSize (q : ℕ) : Prop := ∃ k : ℕ, Odd k ∧ q = 2 ^ k

/-- An admissible field size is at least two, its binary exponent being odd
and therefore positive.  This is a property of blueprint
`def:admissible-size`, paper origin
`references/qpbt-paper/04_preliminaries.tex:662-667`.
-/
theorem IsAdmissibleSize.two_le {q : ℕ} (hq : IsAdmissibleSize q) : 2 ≤ q := by
  obtain ⟨k, hk, hqk⟩ := hq
  obtain ⟨j, hj⟩ := hk
  bound

/-- An admissible field size is either two or a multiple of eight: its binary
exponent is odd, hence either one or at least three.  This is a property of
blueprint
`def:admissible-size`, paper origin
`references/qpbt-paper/04_preliminaries.tex:662-667`.
-/
theorem IsAdmissibleSize.eq_two_or_eight_dvd {q : ℕ} (hq : IsAdmissibleSize q) :
    q = 2 ∨ 8 ∣ q := by
  obtain ⟨k, hk, hqk⟩ := hq
  obtain ⟨j, hj⟩ := hk
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · simp_all
  · right
    refine ⟨2 ^ (2 * j + 1 - 3), ?_⟩
    rw [hqk, hj, show 8 = 2 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega

/-- A dual pair of bases for blueprint
`def:dual-self-dual-normal-basis`, paper `04_preliminaries.tex:494-496`. -/
def IsDualBasisPair {F K ι : Type*} [CommRing F] [CommRing K] [DecidableEq ι]
    [Algebra F K] (b b' : Module.Basis ι F K) : Prop :=
  ∀ i j, Algebra.trace F K (b i * b' j) = if i = j then 1 else 0

namespace Basis

/-- Self-duality in blueprint
`def:dual-self-dual-normal-basis`, paper `04_preliminaries.tex:494-497`. -/
def IsSelfDual {F K ι : Type*} [CommRing F] [CommRing K] [DecidableEq ι]
    [Algebra F K] (b : Module.Basis ι F K) : Prop :=
  IsDualBasisPair b b

/-- Normality in blueprint
`def:dual-self-dual-normal-basis`, paper `04_preliminaries.tex:498-502`. The
Frobenius exponent uses the cardinality of the base field. -/
def IsNormal {F K : Type*} [CommSemiring F] [Fintype F] [Field K] [Algebra F K]
    {k : ℕ} (b : Module.Basis (Fin k) F K) : Prop :=
  ∃ α : K, ∀ j, b j = α ^ (Fintype.card F ^ j.1)

end Basis

/- The characteristic-two self-dual normal-basis construction is carried out
in the group algebra of the finite Galois group.  The transition from a normal
basis to its trace dual is a symmetric unit; odd cardinality makes its square
root unique and symmetric. -/

section GroupAlgebra

variable {G : Type*} [CommGroup G]

variable (hodd : Odd (Nat.card G))

include hodd in
/-- The squaring automorphism of a commutative group whose `Nat.card` is odd. -/
noncomputable def squareMulEquiv : G ≃* G :=
  MulEquiv.ofBijective (powMonoidHom 2) hodd.coprime_two_right.pow_left_bijective

theorem monoid_algebra_sq_eq_dom_congr
    (x : MonoidAlgebra (ZMod 2) G) :
    x ^ 2 = MonoidAlgebra.domCongr (ZMod 2) (ZMod 2) (squareMulEquiv hodd) x := by
  letI : CharP (MonoidAlgebra (ZMod 2) G) 2 :=
    charP_of_injective_algebraMap' (ZMod 2) 2
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp [add_pow_char, hx, hy]
  | single g r =>
      simp
      rfl

include hodd in
theorem monoid_algebra_sq_bijective :
    Function.Bijective (fun x : MonoidAlgebra (ZMod 2) G => x ^ 2) := by
  have heq : (fun x : MonoidAlgebra (ZMod 2) G => x ^ 2) =
      MonoidAlgebra.domCongr (ZMod 2) (ZMod 2) (squareMulEquiv hodd) := by
    funext x
    apply monoid_algebra_sq_eq_dom_congr
  rw [heq]
  exact (MonoidAlgebra.domCongr (ZMod 2) (ZMod 2) (squareMulEquiv hodd)).bijective

end GroupAlgebra

section NormalTraceDual

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]

local notation "G" => Gal(K/(ZMod 2))

-- Named, not anonymous: both instances are in the comparator statement
-- closure, and an anonymous instance is given a generated name that encodes
-- the defining module, which the Mathlib-only challenge file cannot
-- reproduce.  See `docs/comparator.md`, "Environment alignment for QPBT".
noncomputable local instance instCommGroupGaloisZMod2 : CommGroup G :=
  IsCyclic.commGroup
noncomputable local instance instDecidableEqGaloisZMod2 : DecidableEq G :=
  Classical.decEq G

theorem normal_basis_trace_dual_apply (σ : G) :
    (IsGalois.normalBasis (ZMod 2) K).traceDual σ =
      σ ((IsGalois.normalBasis (ZMod 2) K).traceDual 1) := by
  classical
  let b := IsGalois.normalBasis (ZMod 2) K
  have hdual : (b.traceDual : G → K) = fun τ => τ (b.traceDual 1) := by
    simp
    intro τ υ
    calc
      _ =
          Algebra.trace (ZMod 2) K
            (τ⁻¹ (τ (b.traceDual 1) * b υ)) := by
              symm
              apply Algebra.trace_eq_of_algEquiv
      _ = Algebra.trace (ZMod 2) K (b.traceDual 1 * b (τ⁻¹ * υ)) := by
        have hτ : τ⁻¹ (τ (b.traceDual 1)) = b.traceDual 1 := by
          exact τ.symm_apply_apply _
        have hυ : τ⁻¹ (b υ) = b (τ⁻¹ * υ) := by
          calc
            _ = τ⁻¹ (υ (b 1)) := by
              rw [IsGalois.normalBasis_apply]
            _ = (τ⁻¹ * υ) (b 1) := rfl
            _ = _ := (IsGalois.normalBasis_apply _).symm
        simp_all
      _ = _ := b.trace_traceDual_mul 1 _
      _ = _ := by simp only [inv_mul_eq_one, eq_comm]
  exact congr_fun hdual σ

theorem normal_basis_repr_symm_mul_single
    (a : MonoidAlgebra (ZMod 2) G) (σ : G) (r : ZMod 2) :
    ((MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans
        (IsGalois.normalBasis (ZMod 2) K).repr.symm)
        (a * MonoidAlgebra.single σ r) =
      r • σ (((MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans
        (IsGalois.normalBasis (ZMod 2) K).repr.symm) a) := by
  classical
  let b := IsGalois.normalBasis (ZMod 2) K
  let φ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.repr.symm
  change φ _ = r • σ (φ a)
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, hx, hy, smul_add]
  | single τ s =>
      simp only [MonoidAlgebra.single_mul_single, φ, LinearEquiv.trans_apply,
        MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single,
        b.repr_symm_single, map_smul, smul_smul]
      rw [mul_comm]
      apply congrArg
      rw [mul_comm]
      calc
        b (σ * τ) = _ := IsGalois.normalBasis_apply _
        _ = _ := rfl
        _ = _ := congrArg σ (IsGalois.normalBasis_apply τ).symm

theorem normal_basis_transition (a : MonoidAlgebra (ZMod 2) G) :
    let b := IsGalois.normalBasis (ZMod 2) K
    let φ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.repr.symm
    let ψ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.traceDual.repr.symm
    let v := φ.symm (b.traceDual 1)
    φ (v * a) = ψ a := by
  classical
  let b := IsGalois.normalBasis (ZMod 2) K
  let φ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.repr.symm
  let ψ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.traceDual.repr.symm
  let v := φ.symm (b.traceDual 1)
  change _ = ψ a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | single σ r =>
      rw [normal_basis_repr_symm_mul_single]
      rw [φ.apply_symm_apply _]
      simp [ψ]
      exact congrArg _ (normal_basis_trace_dual_apply σ).symm

theorem normal_basis_repr_apply_eq_trace (x : K) (σ : G) :
    let b := IsGalois.normalBasis (ZMod 2) K
    (b.repr x) σ = Algebra.trace (ZMod 2) K (x * b.traceDual σ) := by
  classical
  let b := IsGalois.normalBasis (ZMod 2) K
  simpa using
    b.traceDual.traceDual_repr_apply x σ

theorem normal_basis_transition_inv :
    let b := IsGalois.normalBasis (ZMod 2) K
    let φ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.repr.symm
    let v := φ.symm (b.traceDual 1)
    MonoidAlgebra.domCongr (ZMod 2) (ZMod 2) (MulEquiv.inv G) v = v := by
  classical
  let b := IsGalois.normalBasis (ZMod 2) K
  let v := ((MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.repr.symm).symm (b.traceDual 1)
  change _ = v
  ext σ
  have hv (τ : G) : v.coeff τ =
      Algebra.trace (ZMod 2) K (b.traceDual 1 * b.traceDual τ) := by
    apply normal_basis_repr_apply_eq_trace
  rw [MonoidAlgebra.coeff_domCongr, hv, hv]
  calc
    _ =
        Algebra.trace (ZMod 2) K
          (σ (b.traceDual 1 * b.traceDual σ⁻¹)) := by
            symm
            apply Algebra.trace_eq_of_algEquiv
    _ = Algebra.trace (ZMod 2) K (b.traceDual σ * b.traceDual 1) := by
      rw [map_mul, ← normal_basis_trace_dual_apply,
        normal_basis_trace_dual_apply σ⁻¹]
      have hσ : σ (σ⁻¹ (b.traceDual 1)) = b.traceDual 1 := by
        exact σ.apply_symm_apply _
      rw [hσ]
    _ = _ := by
      rw [mul_comm]

theorem trace_group_algebra_pairing
    (a d : MonoidAlgebra (ZMod 2) G) :
    let b := IsGalois.normalBasis (ZMod 2) K
    let φ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.repr.symm
    let ψ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.traceDual.repr.symm
    let invAlg := MonoidAlgebra.domCongr (ZMod 2) (ZMod 2) (MulEquiv.inv G)
    Algebra.trace (ZMod 2) K (φ a * ψ d) = (invAlg a * d).coeff 1 := by
  classical
  let b := IsGalois.normalBasis (ZMod 2) K
  let φ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.repr.symm
  let ψ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.traceDual.repr.symm
  let invAlg := MonoidAlgebra.domCongr (ZMod 2) (ZMod 2) (MulEquiv.inv G)
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, add_mul, hx, hy, MonoidAlgebra.coeff_add, Finsupp.add_apply]
  | single σ r =>
      induction d using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy =>
          simp only [map_add, mul_add, hx, hy, MonoidAlgebra.coeff_add,
            Finsupp.add_apply]
      | single τ s =>
          simp [φ, ψ, invAlg, LinearEquiv.trans_apply, MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single, b.repr_symm_single, b.traceDual.repr_symm_single, smul_mul_smul, map_smul, b.trace_mul_traceDual, MonoidAlgebra.domCongr_single, MonoidAlgebra.single_mul_single]
          by_cases h : σ = τ
          · subst τ
            simp [mul_comm]
          · simp_all [inv_mul_eq_one]

/-- A finite binary extension whose Galois group has odd cardinality admits a
self-dual normal basis indexed by that group. Starting from Mathlib's normal
basis, the construction multiplies by the inversion-invariant square root of
the transition element to the trace-dual basis in the group algebra. This is
the construction underlying `exists_selfDualNormalBasis`, paper
`04_preliminaries.tex:702-725`. -/
theorem exists_self_dual_normal_basis_gal (hodd : Odd (Nat.card G)) :
    ∃ c : Module.Basis G (ZMod 2) K,
      (∀ σ τ, Algebra.trace (ZMod 2) K (c σ * c τ) =
        if σ = τ then 1 else 0) ∧
      ∃ α : K, ∀ σ, c σ = σ α := by
  classical
  let A := MonoidAlgebra (ZMod 2) G
  let b := IsGalois.normalBasis (ZMod 2) K
  let φ :=
    (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.repr.symm
  let ψ :=
    (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.traceDual.repr.symm
  let v := φ.symm (b.traceDual 1)
  let invAlg :=
    MonoidAlgebra.domCongr (ZMod 2) (ZMod 2) (MulEquiv.inv G)
  obtain ⟨u, hu⟩ := (monoid_algebra_sq_bijective hodd).surjective v
  change u ^ 2 = v at hu
  have hu_unit : IsUnit u := by
    rw [← isUnit_pow_iff (by omega : 2 ≠ 0), hu]
    classical
    let b := IsGalois.normalBasis (ZMod 2) K
    let φ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.repr.symm
    let ψ := (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans b.traceDual.repr.symm
    let v := φ.symm (b.traceDual 1)
    rw [IsUnit.isUnit_iff_mulLeft_bijective]
    have heq : (fun a => v * a) = fun a => φ.symm (ψ a) := by
      funext a
      apply φ.injective
      simp
      exact normal_basis_transition a
    rw [heq]
    exact φ.symm.bijective.comp ψ.bijective
  let U := hu_unit.unit
  have hU : U = u := hu_unit.unit_spec
  have hu_inv : invAlg u = u := by
    apply (monoid_algebra_sq_bijective hodd).injective
    calc
      _ = _ := (map_pow invAlg u 2).symm
      _ = invAlg v := congrArg invAlg hu
      _ = v := normal_basis_transition_inv
      _ = u ^ 2 := hu.symm
  let c :=
    (MonoidAlgebra.basis G (ZMod 2)).map ((Units.mulLeftLinearEquiv (ZMod 2) A U).trans φ)
  have hc (σ : G) :
      c σ = φ ((U : A) * MonoidAlgebra.single σ 1) := by
    solve_by_elim [congrArg]
  have htransition (a : A) : φ (v * a) = ψ a := normal_basis_transition a
  have hc_dual (τ : G) :
      c τ = ψ ((U⁻¹) * MonoidAlgebra.single τ (1 : ZMod 2)) := by
    simp [← htransition]
    apply congrArg φ
    simp [← hu, ← hU, pow_two, mul_assoc]
  refine ⟨c, ?_, φ U, ?_⟩
  · intro σ τ
    rw [hc, hc_dual, trace_group_algebra_pairing]
    have hInvU : invAlg U = U := by exact hu_inv
    rw [map_mul, hInvU, MonoidAlgebra.domCongr_single]
    by_cases h : σ = τ
    · subst τ
      simp [mul_assoc, mul_left_comm]
    · have hne : σ⁻¹ * τ ≠ 1 := by simpa [inv_mul_eq_one]
      have hne' : τ * σ⁻¹ ≠ 1 := by simpa [mul_comm] using hne
      simp [mul_assoc, mul_comm, mul_left_comm, h, hne']
  · intro σ
    rw [hc, normal_basis_repr_symm_mul_single]
    simp only [one_smul]
    rfl

end NormalTraceDual

/-- Existence over the binary extension of cardinality `2^k` for odd `k`;
blueprint `def:dual-self-dual-normal-basis`,
paper `04_preliminaries.tex:702-725`. -/
theorem exists_selfDualNormalBasis {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (k : ℕ) (hk : Odd k)
    (hcard : Fintype.card K = 2 ^ k) :
    ∃ b : Module.Basis (Fin k) (ZMod 2) K,
      Basis.IsSelfDual b ∧ Basis.IsNormal b := by
  classical
  let G := Gal(K/(ZMod 2))
  letI : CommGroup G := IsCyclic.commGroup
  have hfinrank : Module.finrank (ZMod 2) K = k := by
    apply Nat.pow_right_injective (by omega : 1 < 2)
    calc
      _ =
          Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) K := by norm_num
      _ = Fintype.card K := Module.card_eq_pow_finrank.symm
      _ = 2 ^ k := hcard
  have hoddG := ((IsGalois.card_aut_eq_finrank (ZMod 2) K).trans hfinrank) ▸ hk
  obtain ⟨cG, hcG_selfDual, α, hcG_normal⟩ :=
    exists_self_dual_normal_basis_gal hoddG
  let frob := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  let e₀ : Fin (Module.finrank (ZMod 2) K) ≃ G := Equiv.ofBijective
    _
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) K)
  let e := (finCongr hfinrank.symm).trans e₀
  refine ⟨(cG.reindex e.symm), ?_, α, ?_⟩
  · intro i j
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    simpa using hcG_selfDual (e i) (e j)
  · intro i
    rw [Module.Basis.reindex_apply, hcG_normal]
    change (frob ^ i.1) α = _
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

theorem zmod2_fin_equiv_symm_val (x : ZMod 2) :
    ((ZMod.finEquiv 2).symm x).val = if x = 1 then 1 else 0 := by
  fin_cases x <;> rfl

/--
A fixed finite-field model records the carrier and the chosen coding of its
elements by `Fin q`.  The algebra structure and stored basis data make explicit
the paper's once-and-for-all self-dual normal-basis convention; they are
deliberately part of the model rather than quantified afresh by the soundness
theorem.  This is the Lean carrier for blueprint
`def:binary-representation`, paper origin
`references/qpbt-paper/04_preliminaries.tex:653-728`.
-/
/- The finite-field carrier is specialized to `Type 0`, as are the finite
models used by the surrounding Euclidean-space API. -/
structure FixedFieldModel (q : ℕ) extends MIPStarRE.LDT.FieldModel.{0} q where
  /-- Scalar restriction from `ZMod 2` to the chosen field. -/
  algebra : Algebra (ZMod 2) K
  /-- Dimension of the chosen basis over the prime subfield. -/
  basisDim : ℕ
  /-- The chosen basis dimension is odd, as required for a self-dual normal basis
  over the binary field. -/
  basisDimOdd : Odd basisDim
  /-- The admissible field-size relation for the chosen basis dimension. -/
  basisCard : q = 2 ^ basisDim
  /-- The chosen basis of `K` over `ZMod 2`. -/
  basis : Module.Basis (Fin basisDim) (ZMod 2) K
  /--
  The inherited coding of `K` is the natural binary encoding of the stored
  basis coordinates.  This field records the source's `downsize` convention
  rather than allowing an unrelated permutation of `Fin q`.  It is the
  coordinate clause of blueprint
  `def:binary-representation`, with paper origin
  `references/qpbt-paper/04_preliminaries.tex:669-680`.
  -/
  representation_natural :
    ∀ v : Fin basisDim → ZMod 2,
      (toFieldModel.equiv (basis.equivFun.symm v)).val =
        ∑ i : Fin basisDim, if v i = 1 then 2 ^ i.1 else 0
  /-- Self-duality of the chosen basis with respect to the field trace. -/
  selfDual : ∀ i j, Algebra.trace (ZMod 2) K (basis i * basis j) =
    if i = j then 1 else 0
  /-- Normality of the chosen basis, recorded by a Frobenius generator. -/
  normal : ∃ α : K, ∀ i, basis i = α ^ (2 ^ i.1)

/-!
The paper fixes the field representation and self-dual normal basis once for
each admissible field size.  We expose that choice through a single global
selector rather than carrying a potentially different model in every game
parameter record.  Existence is a named stage-4.3 proof obligation; the
selector itself is the resulting noncomputable choice.
-/

/-- An admissible binary field size admits the fixed self-dual normal model used
by the Pauli basis test.  This is the existence assertion implicit in
`def:dual-self-dual-normal-basis` and blueprint
`def:binary-representation`, paper origin
`references/qpbt-paper/04_preliminaries.tex:653-680,702-725`.

This theorem constructs the finite field and its little-endian coordinate
coding.  It records only mathematical existence; it does not formalize the
algorithmic complexity assertion in `lem:efficient_basis`.
-/
theorem exists_fixed_field_model (q : ℕ) (hq : IsAdmissibleSize q) :
    Nonempty (FixedFieldModel q) := by
  classical
  obtain ⟨k, hk, hq⟩ := hq
  subst q
  have hk0 : k ≠ 0 := by
    obtain ⟨m, hm⟩ := hk
    omega
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 k
  letI := Fintype.ofFinite K
  obtain ⟨b, hb_selfDual, hb_normal⟩ :=
    exists_selfDualNormalBasis (K := K) k hk (by rw [Fintype.card_eq_nat_card, GaloisField.card 2 k hk0])
  let bitEquiv : (Fin k → ZMod 2) ≃ (Fin k → Fin 2) :=
    Equiv.piCongrRight fun _ => (ZMod.finEquiv 2).symm
  let fieldEquiv :=
    b.equivFun.toEquiv |>.trans bitEquiv |>.trans finFunctionFinEquiv
  refine ⟨{
    toFieldModel := {
      K := K
      instField := inferInstance
      instFintype := inferInstance
      instDecidableEq := inferInstance
      equiv := fieldEquiv
    }
    algebra := (inferInstance : Algebra (ZMod 2) K)
    basisDim := k
    basisDimOdd := hk
    basisCard := rfl
    basis := b
    representation_natural := ?_
    selfDual := hb_selfDual
    normal := ?_
  }⟩
  · intro v
    simp only [fieldEquiv, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
      LinearEquiv.apply_symm_apply, bitEquiv]
    simp [zmod2_fin_equiv_symm_val]
  · obtain ⟨α, hα⟩ := hb_normal
    refine ⟨α, fun i => ?_⟩
    apply hα

/-- The once-and-for-all field model selected for an admissible size.  Every
QPBT parameter record uses this same choice, matching the paper's fixed
self-dual normal-basis identification rather than quantifying over arbitrary
representations.  Blueprint `def:binary-representation`; paper origin
`references/qpbt-paper/04_preliminaries.tex:653-680`.
-/
noncomputable def fixedFieldModel (q : ℕ) (hq : IsAdmissibleSize q) :
    FixedFieldModel q :=
  Classical.choice (exists_fixed_field_model q hq)

instance instFieldK {q : ℕ} (F : FixedFieldModel q) : Field F.K := F.toFieldModel.instField
variable {q : ℕ} (F : FixedFieldModel q)

instance instFintypeK : Fintype F.K := F.toFieldModel.instFintype
instance instDecidableEqK : DecidableEq F.K :=
  F.toFieldModel.instDecidableEq
instance instAlgebraZModOfNatNatK : Algebra (ZMod 2) F.K :=
  F.algebra

/-- The fixed binary representation obtained from the chosen basis coordinates. -/
noncomputable def binaryRepresentation : F.K ≃ Fin q :=
  F.toFieldModel.equiv

/--
The coordinate map associated with a finite basis.  This is the `κ` of
blueprint `def:subfields-kappa`,
whose paper origin is `references/qpbt-paper/04_preliminaries.tex:433-502`.
-/
noncomputable abbrev kappa {F K ι : Type*} [CommSemiring F] [Semiring K]
    [Algebra F K] [Finite ι]
    (b : Module.Basis ι F K) : K ≃ₗ[F] (ι → F) :=
  b.equivFun

/--
The finite-field trace used by the Pauli phases.  This is a thin wrapper around
Mathlib's basis-independent `Algebra.trace`, matching Equation `eq:def-trace`
in blueprint `def:subfield-trace`
(`references/qpbt-paper/04_preliminaries.tex:481-502`).
-/
noncomputable abbrev binTrace (K : Type*) [CommRing K] [Algebra (ZMod 2) K] :
    K →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) K

/-- The trace selected by a fixed model; this is the map denoted `tr` in the
paper's blueprint `def:binary-representation`,
paper origin `references/qpbt-paper/04_preliminaries.tex:653-680`. -/
noncomputable def fixedBinTrace : F.K → ZMod 2 :=
  binTrace F.K

end MIPStarRE.QPBT
