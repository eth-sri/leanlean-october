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
  grind

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
    rw [hqk, hj, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
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

section

variable (hodd : Odd (Nat.card G))
include hodd

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
      rw [add_pow_char, hx, hy, map_add]
  | single g r =>
      simp [MonoidAlgebra.single_pow, squareMulEquiv, ZMod.pow_card]
      rfl

theorem monoid_algebra_sq_bijective :
    Function.Bijective (fun x : MonoidAlgebra (ZMod 2) G => x ^ 2) := by
  simpa only [monoid_algebra_sq_eq_dom_congr hodd] using
    (MonoidAlgebra.domCongr (ZMod 2) (ZMod 2) (squareMulEquiv hodd)).bijective

end

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

local notation "A" => MonoidAlgebra (ZMod 2) G
local notation "b" => IsGalois.normalBasis (ZMod 2) K

private noncomputable def groupBasisEquiv (c : Module.Basis G (ZMod 2) K) : A ≃ₗ[ZMod 2] K :=
  (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans c.repr.symm

local notation "φ" => groupBasisEquiv b
local notation "ψ" => groupBasisEquiv (Module.Basis.traceDual b)
local notation "v" => LinearEquiv.symm φ (Module.Basis.traceDual b 1)
local notation "invAlg" => MonoidAlgebra.domCongr (ZMod 2) (ZMod 2) (MulEquiv.inv G)

@[local simp] private theorem groupBasisEquiv_single (c : Module.Basis G (ZMod 2) K)
    (σ : G) (r : ZMod 2) : groupBasisEquiv c (MonoidAlgebra.single σ r) = r • c σ := by
  simp [groupBasisEquiv, c.repr_symm_single]

private theorem normal_basis_mul (σ τ : G) : b (σ * τ) = σ (b τ) := by
  rw [IsGalois.normalBasis_apply (σ * τ), IsGalois.normalBasis_apply τ]
  rfl

private theorem normal_basis_trace_dual_apply (σ : G) : (b).traceDual σ = σ ((b).traceDual 1) := by
  classical
  have h : ((b).traceDual : G → K) = fun τ => τ ((b).traceDual 1) := by
    rw [(b).traceDual_eq_iff]
    intro τ υ
    rw [Algebra.traceForm_apply, ← Algebra.trace_eq_of_algEquiv τ⁻¹, map_mul,
      ← normal_basis_mul, AlgEquiv.coe_inv, AlgEquiv.symm_apply_apply, (b).trace_traceDual_mul]
    simp only [inv_mul_eq_one, eq_comm]
  exact congr_fun h σ

private theorem normal_basis_repr_symm_mul_single (a : A) (σ : G) (r : ZMod 2) :
    φ (a * MonoidAlgebra.single σ r) = r • σ (φ a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, hx, hy, smul_add]
  | single τ s =>
      rw [MonoidAlgebra.single_mul_single, mul_comm τ σ]
      simp [map_smul, smul_smul, normal_basis_mul, mul_comm s r]

private theorem normal_basis_transition (a : A) : φ (v * a) = ψ a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [mul_add, hx, hy]
  | single σ r => simp [normal_basis_repr_symm_mul_single, normal_basis_trace_dual_apply σ]

private theorem normal_basis_transition_is_unit : IsUnit v := by
  rw [IsUnit.isUnit_iff_mulLeft_bijective]
  convert (φ).symm.bijective.comp (ψ).bijective using 1
  funext a
  exact (φ).symm_apply_eq.mpr (normal_basis_transition a).symm |>.symm

private theorem normal_basis_transition_inv : invAlg v = v := by
  classical
  have hv (τ : G) : (v).coeff τ = Algebra.trace (ZMod 2) K ((b).traceDual 1 * (b).traceDual τ) := by
    change ((b).repr ((b).traceDual 1)) τ = _
    simpa only [Algebra.traceForm_apply, (b).traceDual_traceDual] using
      (b).traceDual.traceDual_repr_apply ((b).traceDual 1) τ
  ext σ
  rw [MonoidAlgebra.coeff_domCongr, hv, hv]
  change Algebra.trace (ZMod 2) K ((b).traceDual 1 * (b).traceDual σ⁻¹) = _
  rw [← Algebra.trace_eq_of_algEquiv σ, map_mul, normal_basis_trace_dual_apply σ⁻¹,
    AlgEquiv.coe_inv, AlgEquiv.apply_symm_apply, ← normal_basis_trace_dual_apply σ, mul_comm]

private theorem trace_group_algebra_pairing (a d : A) :
    Algebra.trace (ZMod 2) K (φ a * ψ d) = (invAlg a * d).coeff 1 := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, hx, hy]
  | single σ r =>
      rw [groupBasisEquiv_single, smul_mul_assoc, map_smul, MonoidAlgebra.domCongr_single,
        MonoidAlgebra.coeff_single_mul_apply]
      change r • Algebra.trace (ZMod 2) K (b σ * ψ d) = r * d.coeff (σ⁻¹⁻¹ * 1)
      simp only [inv_inv, mul_one, smul_eq_mul]
      congr 1
      simpa only [Algebra.traceForm_apply, mul_comm, groupBasisEquiv, LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply, MonoidAlgebra.coeffLinearEquiv_apply] using
        ((b).traceDual_repr_apply (ψ d) σ).symm

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
  obtain ⟨u, hu⟩ := (monoid_algebra_sq_bijective hodd).surjective v
  change u ^ 2 = v at hu
  have hu_unit : IsUnit u :=
    (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (hu ▸ normal_basis_transition_is_unit)
  lift u to Aˣ using hu_unit with U
  have hinv : invAlg (U : A) = U := by
    apply (monoid_algebra_sq_bijective hodd).injective
    change (invAlg (U : A)) ^ 2 = (U : A) ^ 2
    rw [← map_pow, hu, normal_basis_transition_inv]
  let c := (MonoidAlgebra.basis G (ZMod 2)).map
    ((Units.mulLeftLinearEquiv (ZMod 2) A U).trans φ)
  have hc (σ : G) : c σ = φ ((U : A) * MonoidAlgebra.single σ 1) := rfl
  have hd (τ : G) : c τ = ψ ((↑(U⁻¹) : A) * MonoidAlgebra.single τ 1) := by
    rw [hc, ← normal_basis_transition, ← hu]
    simp [pow_two, ← mul_assoc, ← Units.val_mul]
  refine ⟨c, fun σ τ => ?_, φ (U : A), fun σ => ?_⟩
  · rw [hc, hd, trace_group_algebra_pairing, map_mul, hinv, MonoidAlgebra.domCongr_single]
    rw [mul_mul_mul_comm, Units.mul_inv, one_mul, MonoidAlgebra.single_mul_single,
      mul_one, MonoidAlgebra.coeff_single]
    change (Finsupp.single (σ⁻¹ * τ) (1 : ZMod 2)) 1 = _
    simp [Finsupp.single_apply, inv_mul_eq_one]
  · rw [hc, normal_basis_repr_symm_mul_single, one_smul]

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
    apply Nat.pow_right_injective (by decide : 1 < 2)
    simpa [Module.card_eq_pow_finrank (K := ZMod 2) (V := K)] using hcard
  have hcardG := (IsGalois.card_aut_eq_finrank (ZMod 2) K).trans hfinrank
  obtain ⟨cG, hcG_selfDual, α, hcG_normal⟩ :=
    exists_self_dual_normal_basis_gal (K := K) (hcardG ▸ hk)
  let frob := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  let e₀ : Fin (Module.finrank (ZMod 2) K) ≃ G := Equiv.ofBijective
    (fun i => frob ^ i.1)
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) K)
  let e : Fin k ≃ G := (finCongr hfinrank.symm).trans e₀
  let c : Module.Basis (Fin k) (ZMod 2) K := cG.reindex e.symm
  refine ⟨c, ?_, α, ?_⟩
  · intro i j
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    simpa [e] using hcG_selfDual (e i) (e j)
  · intro i
    rw [Module.Basis.reindex_apply, hcG_normal]
    change (frob ^ i.1) α = α ^ (Fintype.card (ZMod 2) ^ i.1)
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
  have hcardK : Fintype.card K = 2 ^ k := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 k hk0]
  obtain ⟨b, hb_selfDual, hb_normal⟩ :=
    exists_selfDualNormalBasis (K := K) k hk hcardK
  let bitEquiv : (Fin k → ZMod 2) ≃ (Fin k → Fin 2) :=
    Equiv.piCongrRight fun _ => (ZMod.finEquiv 2).symm
  let fieldEquiv := b.equivFun.toEquiv |>.trans bitEquiv |>.trans finFunctionFinEquiv
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
    change (fieldEquiv (b.equivFun.symm v)).val = _
    simp only [fieldEquiv, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
      LinearEquiv.apply_symm_apply, bitEquiv]
    rw [finFunctionFinEquiv_apply]
    apply Finset.sum_congr rfl
    intro i _
    change ((ZMod.finEquiv 2).symm (v i)).val * 2 ^ i.1 = _
    rw [zmod2_fin_equiv_symm_val]
    split_ifs <;> simp
  · obtain ⟨α, hα⟩ := hb_normal
    refine ⟨α, fun i => ?_⟩
    simpa using hα i

/-- The once-and-for-all field model selected for an admissible size.  Every
QPBT parameter record uses this same choice, matching the paper's fixed
self-dual normal-basis identification rather than quantifying over arbitrary
representations.  Blueprint `def:binary-representation`; paper origin
`references/qpbt-paper/04_preliminaries.tex:653-680`.
-/
noncomputable def fixedFieldModel (q : ℕ) (hq : IsAdmissibleSize q) :
    FixedFieldModel q :=
  Classical.choice (exists_fixed_field_model q hq)

section

variable {q : ℕ} (F : FixedFieldModel q)
include q F

instance instFieldK : Field F.K := F.toFieldModel.instField
instance instFintypeK : Fintype F.K := F.toFieldModel.instFintype
instance instDecidableEqK : DecidableEq F.K :=
  F.toFieldModel.instDecidableEq
instance instAlgebraZModOfNatNatK : Algebra (ZMod 2) F.K :=
  F.algebra

/-- The fixed binary representation obtained from the chosen basis coordinates. -/
noncomputable def binaryRepresentation : F.K ≃ Fin q :=
  F.toFieldModel.equiv

end

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
noncomputable def fixedBinTrace {q : ℕ} (F : FixedFieldModel q) : F.K → ZMod 2 :=
  binTrace F.K

end MIPStarRE.QPBT
