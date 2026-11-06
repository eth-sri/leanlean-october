module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




/-!
Develops quotient groups attached to an abstract valued norm, including kernel, image, and
representative criteria.
-/

/-!
Identifies norm-quotient classes with valuation classes modulo the residue degree and constructs
the resulting cyclic equivalences.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u v

namespace DiscreteValuationField
namespace ValuedNorm

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)

/--
The defining evaluation formula for `valuation` is `vG.val (N.toHom x) = (N.residueDegree : ℤ) *
vH.val x`.
-/
@[simp] theorem valuation_apply (x : H) :
    vG.val (N.toHom x) = (N.residueDegree : ℤ) * vH.val x :=
  N.valuation_formula x

/--
`valuation_apply` satisfies the division formula `vG.val (N.toHom (x / y)) = (N.residueDegree : ℤ)
* (vH.val x - vH.val y)`.
-/
@[simp] theorem valuation_apply_div (x y : H) :
    vG.val (N.toHom (x / y)) =
      (N.residueDegree : ℤ) * (vH.val x - vH.val y) := by
  rw [N.valuation_apply, vH.val_div]

/--
`valuation_apply_uniformizer` satisfies the integer-power formula `vG.val (N.toHom (ϖH ^ n)) =
(N.residueDegree : ℤ) * n`.
-/
@[simp] theorem valuation_apply_uniformizer_zpow {ϖH : H}
    (hϖH : vH.IsUniformizer ϖH) (n : ℤ) :
    vG.val (N.toHom (ϖH ^ n)) = (N.residueDegree : ℤ) * n := by
  rw [N.valuation_apply, vH.val_uniformizer_zpow hϖH n]

/--
`valuation_apply_uniformizer` satisfies the natural-power formula `vG.val (N.toHom (ϖH ^ n)) =
(N.residueDegree : ℤ) * (n : ℤ)`.
-/
@[simp] theorem valuation_apply_uniformizer_pow {ϖH : H}
    (hϖH : vH.IsUniformizer ϖH) (n : ℕ) :
    vG.val (N.toHom (ϖH ^ n)) = (N.residueDegree : ℤ) * (n : ℤ) := by
  rw [N.valuation_apply, vH.val_uniformizer_pow hϖH n]

/--
`valuation_apply_zeroSubgroup_mul_uniformizer` satisfies the integer-power formula `vG.val
(N.toHom (u * ϖH ^ n)) = (N.residueDegree : ℤ) * n`.
-/
@[simp] theorem valuation_apply_zeroSubgroup_mul_uniformizer_zpow
    {ϖH u : H} (hϖH : vH.IsUniformizer ϖH)
    (hu : u ∈ vH.zeroSubgroup) (n : ℤ) :
    vG.val (N.toHom (u * ϖH ^ n)) = (N.residueDegree : ℤ) * n := by
  rw [N.valuation_apply, vH.valuation_uniformizer_normal_form hϖH hu n]

/--
`valuation_apply_zeroSubgroup_mul_uniformizer` satisfies the natural-power formula `vG.val
(N.toHom (u * ϖH ^ n)) = (N.residueDegree : ℤ) * (n : ℤ)`.
-/
@[simp] theorem valuation_apply_zeroSubgroup_mul_uniformizer_pow
    {ϖH u : H} (hϖH : vH.IsUniformizer ϖH)
    (hu : u ∈ vH.zeroSubgroup) (n : ℕ) :
    vG.val (N.toHom (u * ϖH ^ n)) =
      (N.residueDegree : ℤ) * (n : ℤ) := by
  rw [N.valuation_apply]
  have hv := vH.valuation_uniformizer_normal_form hϖH hu (n : ℤ)
  simpa using congrArg (fun m : ℤ => (N.residueDegree : ℤ) * m) hv

/--
Establishes the identity `vG.valuationHom (N.toHom x) = vH.valuationHom x ^ (N.residueDegree :
ℤ)`.
-/
@[simp] theorem valuationHom_apply_norm (x : H) :
    vG.valuationHom (N.toHom x) =
      vH.valuationHom x ^ (N.residueDegree : ℤ) := by
  rw [MultiplicativeIntegerValuation.valuationHom_apply,
    N.valuation_apply,
    MultiplicativeIntegerValuation.valuationHom_apply,
    mul_comm (N.residueDegree : ℤ) (vH.val x),
    Int.ofAdd_mul]

/--
Establishes the identity `Multiplicative.toAdd (vG.valuationHom (N.toHom x)) = (N.residueDegree :
ℤ) * Multiplicative.toAdd (vH.valuationHom x)`.
-/
@[simp] theorem toAdd_valuationHom_apply_norm (x : H) :
    Multiplicative.toAdd (vG.valuationHom (N.toHom x)) =
      (N.residueDegree : ℤ) *
        Multiplicative.toAdd (vH.valuationHom x) := by
  rw [N.valuationHom_apply_norm, Int.toAdd_zpow,
    MultiplicativeIntegerValuation.valuationHom_apply, toAdd_ofAdd,
    mul_comm (vH.val x) (N.residueDegree : ℤ)]

/--
`valuationHom_apply_norm` satisfies the division formula `vG.valuationHom (N.toHom (x / y)) =
vH.valuationHom (x / y) ^ (N.residueDegree : ℤ)`.
-/
@[simp] theorem valuationHom_apply_norm_div (x y : H) :
    vG.valuationHom (N.toHom (x / y)) =
      vH.valuationHom (x / y) ^ (N.residueDegree : ℤ) :=
  N.valuationHom_apply_norm (x / y)



/-- The norm subgroup attached to a valued norm. -/
def normSubgroup : Subgroup G :=
  N.toHom.range

/-- The valuation of any norm is divisible by the residue degree. -/
theorem residueDegree_dvd_valuation_of_mem_normSubgroup
    {x : G} (hx : x ∈ N.normSubgroup) :
    (N.residueDegree : ℤ) ∣ vG.val x := by
  rcases hx with ⟨y, rfl⟩
  exact ⟨vH.val y, N.valuation_apply y⟩









/--
Establishes the identity `((vG.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) : Multiplicative ℤ) = vH.valuationHom x ^
(N.residueDegree : ℤ)`.
-/
@[simp] theorem coe_quotientZeroSubgroupEquivValueSubgroup_norm_mk
    (x : H) :
    ((vG.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) :
      Multiplicative ℤ) =
      vH.valuationHom x ^ (N.residueDegree : ℤ) := by
  rw [MultiplicativeIntegerValuation.coe_quotientZeroSubgroupEquivValueSubgroup_mk]
  exact N.valuationHom_apply_norm x

/--
Establishes the identity `Multiplicative.toAdd (((vG.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) : Multiplicative ℤ)) =
(N.residueDegree : ℤ) * vH.val x`.
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_norm_mk
    (x : H) :
    Multiplicative.toAdd
      (((vG.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) :
        Multiplicative ℤ)) =
      (N.residueDegree : ℤ) * vH.val x := by
  rw [N.coe_quotientZeroSubgroupEquivValueSubgroup_norm_mk,
    Int.toAdd_zpow,
    MultiplicativeIntegerValuation.valuationHom_apply, toAdd_ofAdd,
    mul_comm (vH.val x) (N.residueDegree : ℤ)]



















/-- If all valuation-zero target elements are norms and the source valuation
has a uniformizer, valuation divisibility by the residue degree is sufficient
for norm-subgroup membership. -/
theorem mem_normSubgroup_of_residueDegree_dvd_val_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    {x : G} (hx : (N.residueDegree : ℤ) ∣ vG.val x) :
    x ∈ N.normSubgroup := by
  rcases hx with ⟨n, hn⟩
  have hval :
      vG.val x = vG.val (N.toHom (ϖH ^ n)) := by
    rw [N.valuation_apply_uniformizer_zpow hϖH n, hn]
  rcases vG.exists_zeroSubgroup_mul_eq_of_val_eq hval with ⟨u, hu, hux⟩
  have hu_norm : u ∈ N.normSubgroup := hzero hu
  have hnorm : u * N.toHom (ϖH ^ n) ∈ N.normSubgroup :=
    N.normSubgroup.mul_mem hu_norm
      ((MonoidHom.mem_range (f := N.toHom)).2 ⟨ϖH ^ n, rfl⟩)
  simpa [← hux] using hnorm

/-- With source uniformizer and norm-surjectivity on valuation-zero target
elements, the norm subgroup is exactly the elements whose valuation is
divisible by the residue degree. -/
theorem mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    x ∈ N.normSubgroup ↔ (N.residueDegree : ℤ) ∣ vG.val x := by
  constructor
  · exact N.residueDegree_dvd_valuation_of_mem_normSubgroup
  · exact N.mem_normSubgroup_of_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero









/-- The valuation map modulo the residue-degree multiple subgroup.  This is
the canonical value-group map used to compare norm quotients with
`ℤ / fℤ`. -/
def valueModResidueDegreeHom :
    G →* Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  (QuotientGroup.mk'
      (integerMultipleSubgroup (N.residueDegree : ℤ))).comp
    vG.valuationHom

/--
The defining evaluation formula for `valueModResidueDegreeHom` is `N.valueModResidueDegreeHom x =
QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (vG.valuationHom x)`.
-/
@[simp] theorem valueModResidueDegreeHom_apply (x : G) :
    N.valueModResidueDegreeHom x =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (vG.valuationHom x) :=
  rfl



/-- The specified map is surjective: `Function.Surjective N.valueModResidueDegreeHom`. -/
theorem valueModResidueDegreeHom_surjective_of_uniformizer
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    Function.Surjective N.valueModResidueDegreeHom := by
  intro q
  rcases
    QuotientGroup.mk'_surjective
      (integerMultipleSubgroup (N.residueDegree : ℤ)) q with
    ⟨m, rfl⟩
  exact ⟨ϖG ^ Multiplicative.toAdd m, by
    rw [N.valueModResidueDegreeHom_apply,
      MultiplicativeIntegerValuation.valuationHom_apply,
      vG.val_uniformizer_zpow hϖG (Multiplicative.toAdd m),
      ofAdd_toAdd]⟩

/--
Characterizes `x ∈ N.valueModResidueDegreeHom.ker` by the equivalent condition `(N.residueDegree :
ℤ) ∣ vG.val x`.
-/
theorem mem_valueModResidueDegreeHom_ker_iff (x : G) :
    x ∈ N.valueModResidueDegreeHom.ker ↔
      (N.residueDegree : ℤ) ∣ vG.val x := by
  change N.valueModResidueDegreeHom x = 1 ↔
    (N.residueDegree : ℤ) ∣ vG.val x
  rw [N.valueModResidueDegreeHom_apply,
    MultiplicativeIntegerValuation.valuationHom_apply]
  simp [QuotientGroup.mk'_apply]

/-- The map `G/G⁰ → ℤ/fℤ` induced by valuation modulo the
residue-degree multiple subgroup. -/
def zeroSubgroupQuotientToValueModResidueDegree :
    G ⧸ vG.zeroSubgroup →*
      Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  QuotientGroup.map vG.zeroSubgroup
    (integerMultipleSubgroup (N.residueDegree : ℤ)) vG.valuationHom (by
      intro x hx
      change vG.valuationHom x ∈
        integerMultipleSubgroup (N.residueDegree : ℤ)
      rw [mem_integerMultipleSubgroup_iff,
        MultiplicativeIntegerValuation.valuationHom_apply, toAdd_ofAdd,
        (MultiplicativeIntegerValuation.mem_zeroSubgroup_iff vG x).1 hx]
      exact dvd_zero (N.residueDegree : ℤ))

/--
Establishes the identity `N.zeroSubgroupQuotientToValueModResidueDegree (QuotientGroup.mk'
vG.zeroSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
(vG.valuationHom x)`.
-/
@[simp] theorem zeroSubgroupQuotientToValueModResidueDegree_mk (x : G) :
    N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (vG.valuationHom x) := by
  simp [zeroSubgroupQuotientToValueModResidueDegree]

/--
Establishes the identity `N.zeroSubgroupQuotientToValueModResidueDegree (QuotientGroup.mk'
vG.zeroSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
(Multiplicative.ofAdd (vG.val x))`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_mk_ofAdd (x : G) :
    N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_mk x,
    MultiplicativeIntegerValuation.valuationHom_apply]

/--
The specified map is surjective: `Function.Surjective
N.zeroSubgroupQuotientToValueModResidueDegree`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_surjective_of_uniformizer
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    Function.Surjective N.zeroSubgroupQuotientToValueModResidueDegree := by
  intro q
  rcases
    QuotientGroup.mk'_surjective
      (integerMultipleSubgroup (N.residueDegree : ℤ)) q with
    ⟨m, rfl⟩
  exact ⟨QuotientGroup.mk' vG.zeroSubgroup
      (ϖG ^ Multiplicative.toAdd m), by
    rw [N.zeroSubgroupQuotientToValueModResidueDegree_mk,
      MultiplicativeIntegerValuation.valuationHom_apply,
      vG.val_uniformizer_zpow hϖG (Multiplicative.toAdd m),
      ofAdd_toAdd]⟩





/--
Establishes the identity `N.valueModResidueDegreeHom.ker = (integerMultipleSubgroup
(N.residueDegree : ℤ)).comap vG.valuationHom`.
-/
theorem valueModResidueDegreeHom_ker_eq_valuationHom_comap :
    N.valueModResidueDegreeHom.ker =
      (integerMultipleSubgroup (N.residueDegree : ℤ)).comap
        vG.valuationHom := by
  rw [valueModResidueDegreeHom,
    ← MonoidHom.comap_ker
      (QuotientGroup.mk'
        (integerMultipleSubgroup (N.residueDegree : ℤ)))
      vG.valuationHom,
    QuotientGroup.ker_mk']

/-- The subgroup of `G/G⁰` consisting of classes whose value is divisible by the
residue degree.  This is the kernel of the value-mod-residue-degree map. -/
def residueDegreeClassSubgroup :
    Subgroup (G ⧸ vG.zeroSubgroup) :=
  Subgroup.map (QuotientGroup.mk' vG.zeroSubgroup)
    N.valueModResidueDegreeHom.ker

/-- The subgroup appearing in `N.residueDegreeClassSubgroup.Normal` is normal. -/
instance residueDegreeClassSubgroup_normal :
    N.residueDegreeClassSubgroup.Normal := by
  dsimp [residueDegreeClassSubgroup]
  infer_instance





/--
Establishes the identity `N.zeroSubgroupQuotientToValueModResidueDegree.ker =
N.residueDegreeClassSubgroup`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup :
    N.zeroSubgroupQuotientToValueModResidueDegree.ker =
      N.residueDegreeClassSubgroup := by
  rw [zeroSubgroupQuotientToValueModResidueDegree, QuotientGroup.ker_map,
    ← N.valueModResidueDegreeHom_ker_eq_valuationHom_comap]
  rfl











/-- First-isomorphism form of the value-mod-residue-degree map.  A target
uniformizer makes `G/G⁰ → ℤ/fℤ` surjective. -/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup ≃*
      Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  (QuotientGroup.quotientMulEquivOfEq
    (N.zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (φ := N.zeroSubgroupQuotientToValueModResidueDegree)
      (N.zeroSubgroupQuotientToValueModResidueDegree_surjective_of_uniformizer hϖG))

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
(QuotientGroup.mk' N.residueDegreeClassSubgroup q) = N.zeroSubgroupQuotientToValueModResidueDegree
q`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      N.zeroSubgroupQuotientToValueModResidueDegree q := by
  change QuotientGroup.kerLift N.zeroSubgroupQuotientToValueModResidueDegree
      ((QuotientGroup.quotientMulEquivOfEq
        N.zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup.symm)
        (QuotientGroup.mk q)) = N.zeroSubgroupQuotientToValueModResidueDegree q
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk N.zeroSubgroupQuotientToValueModResidueDegree q

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd (vG.val
x))`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (x : G) :
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk hϖG,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk_ofAdd x]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree
hϖG).symm (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd
(vG.val x))) = QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup
x)`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_val
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (x : G) :
    (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd (vG.val x))) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).injective
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        ((N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
          (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
            (Multiplicative.ofAdd (vG.val x)))) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
        exact
          (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).apply_symm_apply _
    _ =
      N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) := by
        rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
          hϖG x]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree
hϖG).symm (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd
n)) = QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^
n))`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ n)) := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).injective
  rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
      hϖG (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]
  simp











































/--
`zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_uniformizerClass` satisfies the
integer-power formula `N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
((QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_uniformizerClass_zpow
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n : ℤ) :
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        ((QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd n) := by
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
      hϖG (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]

/--
`zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass`
satisfies the integer-power formula
`(N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm (QuotientGroup.mk'
(integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)) = (QuotientGroup.mk'
N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
-/
@[simp]
theorem
zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass_zpow
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd
      hϖG n,
    ← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]

/-- Establishes the identity `N.valueModResidueDegreeHom.ker = N.normSubgroup`. -/
theorem valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    N.valueModResidueDegreeHom.ker = N.normSubgroup := by
  ext x
  rw [N.mem_valueModResidueDegreeHom_ker_iff,
    N.mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero x]

/-- The subgroup `N/G⁰` inside the zero-valuation quotient `G/G⁰`, where
`N` is the norm subgroup. -/
def normSubgroupClassInZeroQuotient : Subgroup (G ⧸ vG.zeroSubgroup) :=
  Subgroup.map (QuotientGroup.mk' vG.zeroSubgroup) N.normSubgroup

/-- The subgroup appearing in `N.normSubgroupClassInZeroQuotient.Normal` is normal. -/
instance normSubgroupClassInZeroQuotient_normal
    [(N.normSubgroup).Normal] :
    N.normSubgroupClassInZeroQuotient.Normal := by
  dsimp [normSubgroupClassInZeroQuotient]
  infer_instance





/-- Establishes the identity `N.residueDegreeClassSubgroup = N.normSubgroupClassInZeroQuotient`. -/
theorem residueDegreeClassSubgroup_eq_normSubgroupClassInZeroQuotient_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    N.residueDegreeClassSubgroup =
      N.normSubgroupClassInZeroQuotient := by
  rw [residueDegreeClassSubgroup, normSubgroupClassInZeroQuotient,
    N.valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
      hϖH hzero]

/-- The quotient by the value-side residue-degree class subgroup is the same
as the quotient by the norm-class subgroup when valuation-zero target elements
are norms. -/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivNormClass
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup ≃*
      (G ⧸ vG.zeroSubgroup) ⧸ N.normSubgroupClassInZeroQuotient :=
  QuotientGroup.quotientMulEquivOfEq
    (N.residueDegreeClassSubgroup_eq_normSubgroupClassInZeroQuotient_of_zeroSubgroup_le
      hϖH hzero)

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup q) = QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient q`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q := by
  rfl

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup x)`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_mk_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk hϖH hzero]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
(QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) = QuotientGroup.mk'
N.residueDegreeClassSubgroup q`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup q := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).injective
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        ((N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
          (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q)) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q := by
        exact
          (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).apply_symm_apply _
    _ =
      N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) := by
        rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk hϖH hzero q]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
(QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk hϖH hzero]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormClass_uniformizerClass` satisfies the integer-power
formula `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero ((QuotientGroup.mk'
N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) = (QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        ((QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk_mk
      hϖH hzero (ϖG ^ n)]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_uniformizerClass` satisfies the
integer-power formula `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
((QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n)
= (QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        ((QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk_mk
    hϖH hzero (ϖG ^ n)]

/-- The natural map `G/G⁰ → G/N`, where `N` is a norm subgroup containing
the valuation-zero subgroup. -/
def zeroSubgroupQuotientToNormQuotient [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    G ⧸ vG.zeroSubgroup →* G ⧸ N.normSubgroup :=
  QuotientGroup.map vG.zeroSubgroup N.normSubgroup (MonoidHom.id G) (by
      intro x hx
      exact hzero hx)

/--
Establishes the identity `N.zeroSubgroupQuotientToNormQuotient hzero (QuotientGroup.mk'
vG.zeroSubgroup x) = QuotientGroup.mk' N.normSubgroup x`.
-/
@[simp] theorem zeroSubgroupQuotientToNormQuotient_mk
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' N.normSubgroup x := by
  exact QuotientGroup.map_mk' vG.zeroSubgroup N.normSubgroup
    (MonoidHom.id G) (fun _ hx => hzero hx) x



















/-- The third-isomorphism equivalence
`(G/G⁰)/(N/G⁰) ≃ G/N` for the norm subgroup. -/
noncomputable def zeroQuotientModuloNormClassEquivNormQuotient
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.normSubgroupClassInZeroQuotient ≃*
      G ⧸ N.normSubgroup :=
  QuotientGroup.quotientQuotientEquivQuotient
    vG.zeroSubgroup N.normSubgroup hzero

/--
Establishes the identity `N.zeroQuotientModuloNormClassEquivNormQuotient hzero (QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient q) = N.zeroSubgroupQuotientToNormQuotient hzero q`.
-/
@[simp] theorem zeroQuotientModuloNormClassEquivNormQuotient_mk
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloNormClassEquivNormQuotient hzero
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) =
      N.zeroSubgroupQuotientToNormQuotient hzero q := by
  change
    QuotientGroup.quotientQuotientEquivQuotientAux
        vG.zeroSubgroup N.normSubgroup hzero q =
      N.zeroSubgroupQuotientToNormQuotient hzero q
  exact
    (QuotientGroup.quotientQuotientEquivQuotientAux_mk
      (N := vG.zeroSubgroup) (M := N.normSubgroup) (h := hzero) q)

/--
Establishes the identity `N.zeroQuotientModuloNormClassEquivNormQuotient hzero (QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup x)) = QuotientGroup.mk'
N.normSubgroup x`.
-/
@[simp] theorem zeroQuotientModuloNormClassEquivNormQuotient_mk_mk
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroQuotientModuloNormClassEquivNormQuotient hzero
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.normSubgroup x := by
  rw [N.zeroQuotientModuloNormClassEquivNormQuotient_mk hzero,
    N.zeroSubgroupQuotientToNormQuotient_mk hzero x]

/-- Direct form of the quotient comparison from the residue-degree class
subgroup to the norm quotient. -/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivNormQuotient
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup ≃*
      G ⧸ N.normSubgroup :=
  (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).trans
    (N.zeroQuotientModuloNormClassEquivNormQuotient hzero)

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup q) = N.zeroSubgroupQuotientToNormQuotient hzero
q`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      N.zeroSubgroupQuotientToNormQuotient hzero q := by
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      N.zeroQuotientModuloNormClassEquivNormQuotient hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup q)) := rfl
    _ = N.zeroSubgroupQuotientToNormQuotient hzero q := by
      rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk hϖH hzero q,
        N.zeroQuotientModuloNormClassEquivNormQuotient_mk hzero q]

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' N.normSubgroup x`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.normSubgroup x := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk hϖH hzero,
    N.zeroSubgroupQuotientToNormQuotient_mk hzero x]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
(QuotientGroup.mk' N.normSubgroup x) = QuotientGroup.mk' N.residueDegreeClassSubgroup
(QuotientGroup.mk' vG.zeroSubgroup x)`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
        (QuotientGroup.mk' N.normSubgroup x) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).injective
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        ((N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
          (QuotientGroup.mk' N.normSubgroup x)) =
      QuotientGroup.mk' N.normSubgroup x := by
        exact
          (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).apply_symm_apply _
    _ =
      N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) := by
        rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
          hϖH hzero x]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormQuotient_uniformizerClass` satisfies the
integer-power formula `N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
((QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
(QuotientGroup.mk' N.normSubgroup ϖG) ^ n`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        ((QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      (QuotientGroup.mk' N.normSubgroup ϖG) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
      hϖH hzero (ϖG ^ n)]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_uniformizerClass` satisfies the
integer-power formula `(N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) = (QuotientGroup.mk' N.residueDegreeClassSubgroup
(QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
        ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_mk
      hϖH hzero (ϖG ^ n),
    ← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]

















/-- The actual norm quotient is the value-group quotient `ℤ / fℤ` when
valuation-zero target elements are norms and the target valuation has a
uniformizer. -/
noncomputable def normQuotientEquivValueModResidueDegree
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    G ⧸ N.normSubgroup ≃*
      Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  (QuotientGroup.quotientMulEquivOfEq
      (N.valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
        hϖH hzero).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      N.valueModResidueDegreeHom
      (N.valueModResidueDegreeHom_surjective_of_uniformizer hϖG))

/--
Establishes the identity `N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
(QuotientGroup.mk' N.normSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree
: ℤ)) (vG.valuationHom x)`.
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (vG.valuationHom x) := by
  change QuotientGroup.kerLift N.valueModResidueDegreeHom
      ((QuotientGroup.quotientMulEquivOfEq
        (N.valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
          hϖH hzero).symm) (QuotientGroup.mk x)) = N.valueModResidueDegreeHom x
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk N.valueModResidueDegreeHom x

/--
Establishes the identity `N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
(QuotientGroup.mk' N.normSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree
: ℤ)) (Multiplicative.ofAdd (vG.val x))`.
-/
theorem normQuotientEquivValueModResidueDegree_mk_ofAdd
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.normQuotientEquivValueModResidueDegree_mk hϖG hϖH hzero x,
    MultiplicativeIntegerValuation.valuationHom_apply]

/--
`normQuotientEquivValueModResidueDegree_uniformizer` satisfies the integer-power formula
`N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero (QuotientGroup.mk' N.normSubgroup (ϖG ^
n)) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)`.
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_uniformizer_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup (ϖG ^ n)) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd n) := by
  rw [N.normQuotientEquivValueModResidueDegree_mk_ofAdd
      hϖG hϖH hzero (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]

/--
Establishes the identity `(N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
(QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd (vG.val
x))) = QuotientGroup.mk' N.normSubgroup x`.
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_symm_mk_val
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd (vG.val x))) =
      QuotientGroup.mk' N.normSubgroup x := by
  apply (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).injective
  calc
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        ((N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
          (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
            (Multiplicative.ofAdd (vG.val x)))) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
        exact
          (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).apply_symm_apply _
    _ =
      N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) := by
        rw [N.normQuotientEquivValueModResidueDegree_mk_ofAdd
          hϖG hϖH hzero x]

/--
Establishes the identity `(N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
(QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)) =
QuotientGroup.mk' N.normSubgroup (ϖG ^ n)`.
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_symm_mk_ofAdd
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      QuotientGroup.mk' N.normSubgroup (ϖG ^ n) := by
  apply (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).injective
  rw [N.normQuotientEquivValueModResidueDegree_uniformizer_zpow
      hϖG hϖH hzero n]
  simp

/-- Compatibility of the natural map `G/G⁰ → G/N` with the value-modulo
residue-degree map. -/
@[simp] theorem normQuotientEquivValueModResidueDegree_zeroSubgroupQuotientToNormQuotient_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroSubgroupQuotientToNormQuotient hzero
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  rw [N.zeroSubgroupQuotientToNormQuotient_mk hzero x,
    N.normQuotientEquivValueModResidueDegree_mk hϖG hϖH hzero x,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk x]

/-- The direct residue-degree-class quotient to the norm quotient, followed by
the norm-quotient/value-group equivalence, agrees with the direct
value-mod-residue-degree quotient map on representatives. -/
@[simp]
theorem
normQuotientEquivValueModResidueDegree_zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup q)) =
      N.zeroSubgroupQuotientToValueModResidueDegree q := by
  refine QuotientGroup.induction_on q ?_
  intro x
  change
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup
            (QuotientGroup.mk' vG.zeroSubgroup x))) =
      N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x)
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk
      hϖH hzero (QuotientGroup.mk' vG.zeroSubgroup x),
    N.zeroSubgroupQuotientToNormQuotient_mk hzero x,
    N.normQuotientEquivValueModResidueDegree_mk hϖG hϖH hzero x,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk x]

/--
Establishes the identity `N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
(N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero (QuotientGroup.mk'
N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x))) = QuotientGroup.mk'
(integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd (vG.val x))`.
-/
@[simp]
theorem
normQuotientEquivValueModResidueDegree_zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup
            (QuotientGroup.mk' vG.zeroSubgroup x))) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
      hϖH hzero x,
    N.normQuotientEquivValueModResidueDegree_mk_ofAdd hϖG hϖH hzero x]



end ValuedNorm

end DiscreteValuationField

end

end LocalFieldTheory

universe u v

namespace LocalFieldTheory

noncomputable section

namespace DiscreteValuationField
namespace ValuedNorm

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)













































/-- Under the value-group equivalence, the `n`th power of the target
uniformizer class maps to the class of `n` modulo the residue-degree subgroup. -/
@[simp] theorem normQuotientEquivValueModResidueDegree_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd n) := by
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n]
  exact N.normQuotientEquivValueModResidueDegree_uniformizer_zpow
    hϖG hϖH hzero n

/--
`normQuotientEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass` satisfies the
integer-power formula `(N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
(QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)) =
(QuotientGroup.mk' N.normSubgroup ϖG) ^ n`.
-/
@[simp] theorem normQuotientEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      (QuotientGroup.mk' N.normSubgroup ϖG) ^ n := by
  rw [N.normQuotientEquivValueModResidueDegree_symm_mk_ofAdd
      hϖG hϖH hzero n,
    ← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n]

/-- The actual norm quotient as the standard cyclic group
`Multiplicative (ZMod f)`, where `f` is the residue degree in the valuation
formula. -/
noncomputable def normQuotientEquivZMod
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    G ⧸ N.normSubgroup ≃* Multiplicative (ZMod N.residueDegree) :=
  (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).trans
    (valueModIntegerMultipleSubgroupEquivZMod (N.residueDegree : ℤ))

/--
Establishes the identity `N.normQuotientEquivZMod hϖG hϖH hzero (QuotientGroup.mk' N.normSubgroup
x) = Multiplicative.ofAdd ((vG.val x : ℤ) : ZMod N.residueDegree)`.
-/
@[simp] theorem normQuotientEquivZMod_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivZMod hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) =
      Multiplicative.ofAdd ((vG.val x : ℤ) : ZMod N.residueDegree) := by
  rw [normQuotientEquivZMod, MulEquiv.trans_apply,
    N.normQuotientEquivValueModResidueDegree_mk_ofAdd hϖG hϖH hzero x]
  rfl

/--
`normQuotientEquivZMod_uniformizer` satisfies the integer-power formula `N.normQuotientEquivZMod
hϖG hϖH hzero (QuotientGroup.mk' N.normSubgroup (ϖG ^ n)) = Multiplicative.ofAdd ((n : ℤ) : ZMod
N.residueDegree)`.
-/
@[simp] theorem normQuotientEquivZMod_uniformizer_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivZMod hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup (ϖG ^ n)) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree) := by
  rw [N.normQuotientEquivZMod_mk hϖG hϖH hzero (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]

/--
`normQuotientEquivZMod_uniformizerClass` satisfies the integer-power formula
`N.normQuotientEquivZMod hϖG hϖH hzero ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree)`.
-/
@[simp] theorem normQuotientEquivZMod_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivZMod hϖG hϖH hzero
        ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree) := by
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n,
    N.normQuotientEquivZMod_uniformizer_zpow hϖG hϖH hzero n]

/--
Establishes the identity `(N.normQuotientEquivZMod hϖG hϖH hzero).symm (Multiplicative.ofAdd ((n :
ℤ) : ZMod N.residueDegree)) = QuotientGroup.mk' N.normSubgroup (ϖG ^ n)`.
-/
@[simp] theorem normQuotientEquivZMod_symm_mk_ofAdd
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.normQuotientEquivZMod hϖG hϖH hzero).symm
        (Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree)) =
      QuotientGroup.mk' N.normSubgroup (ϖG ^ n) := by
  apply (N.normQuotientEquivZMod hϖG hϖH hzero).injective
  rw [MulEquiv.apply_symm_apply,
    N.normQuotientEquivZMod_uniformizer_zpow hϖG hϖH hzero n]









































































end ValuedNorm

end DiscreteValuationField

end

end LocalFieldTheory
