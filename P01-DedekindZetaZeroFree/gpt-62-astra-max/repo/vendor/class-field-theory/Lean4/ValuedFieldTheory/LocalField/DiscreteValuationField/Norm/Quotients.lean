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
    {vG : MultiplicativeIntegerValuation G}
    {vH : MultiplicativeIntegerValuation H}
    (N : ValuedNorm vG vH)

/--
The defining evaluation formula for `valuation` is `vG.val (N.toHom x) = (N.residueDegree : ℤ) *
vH.val x`.
-/
@[simp] theorem valuation_apply (x : H) :
    vG.val (N.toHom x) = (N.residueDegree : ℤ) * vH.val x :=
  N.valuation_formula x

/--
`valuation_apply_uniformizer` satisfies the integer-power formula `vG.val (N.toHom (ϖH ^ n)) =
(N.residueDegree : ℤ) * n`.
-/
@[simp] theorem valuation_apply_uniformizer_zpow {ϖH : H}
    (hϖH : vH.IsUniformizer ϖH) (n : ℤ) :
    vG.val (N.toHom (ϖH ^ n)) = (N.residueDegree : ℤ) * n := by
  rw [N.valuation_apply, vH.val_uniformizer_zpow hϖH n]

/-- The norm subgroup attached to a valued norm. -/
def normSubgroup : Subgroup G :=
  N.toHom.range

/-- The valuation of any norm is divisible by the residue degree. -/
theorem residueDegree_dvd_valuation_of_mem_normSubgroup
    {x : G} (hx : x ∈ N.normSubgroup) :
    (N.residueDegree : ℤ) ∣ vG.val x := by
  rcases hx with ⟨y, rfl⟩
  exact ⟨vH.val y, N.valuation_apply y⟩

section

variable {ϖH : H} (hϖH : vH.IsUniformizer ϖH) (hzero : vG.zeroSubgroup ≤ N.normSubgroup)

include hϖH hzero in
/-- If all valuation-zero target elements are norms and the source valuation
has a uniformizer, valuation divisibility by the residue degree is sufficient
for norm-subgroup membership. -/
theorem mem_normSubgroup_of_residueDegree_dvd_val_of_zeroSubgroup_le
    {x : G} (hx : (N.residueDegree : ℤ) ∣ vG.val x) :
    x ∈ N.normSubgroup := by
  rcases hx with ⟨n, hn⟩
  have hval :
      vG.val x = vG.val (N.toHom (ϖH ^ n)) := by
    rw [N.valuation_apply_uniformizer_zpow hϖH n, hn]
  rcases vG.exists_zeroSubgroup_mul_eq_of_val_eq hval with ⟨u, hu, hux⟩
  have hnorm :=
    N.normSubgroup.mul_mem (hzero hu)
      ((MonoidHom.mem_range).2 ⟨ϖH ^ n, rfl⟩)
  simpa [← hux] using hnorm

include hϖH hzero in
/-- With source uniformizer and norm-surjectivity on valuation-zero target
elements, the norm subgroup is exactly the elements whose valuation is
divisible by the residue degree. -/
theorem mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le (x : G) :
    x ∈ N.normSubgroup ↔ (N.residueDegree : ℤ) ∣ vG.val x := by
  constructor
  · exact N.residueDegree_dvd_valuation_of_mem_normSubgroup
  · exact N.mem_normSubgroup_of_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero

end

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
    simp_all [N.valueModResidueDegreeHom_apply, MultiplicativeIntegerValuation.valuationHom_apply, vG.val_uniformizer_zpow]⟩

/--
Characterizes `x ∈ N.valueModResidueDegreeHom.ker` by the equivalent condition `(N.residueDegree :
ℤ) ∣ vG.val x`.
-/
theorem mem_valueModResidueDegreeHom_ker_iff (x : G) :
    x ∈ N.valueModResidueDegreeHom.ker ↔
      (N.residueDegree : ℤ) ∣ vG.val x := by
  simp [QuotientGroup.mk'_apply]

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

/-- Establishes the identity `N.valueModResidueDegreeHom.ker = N.normSubgroup`. -/
theorem valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    N.valueModResidueDegreeHom.ker = N.normSubgroup := by
  ext x
  simp [N.mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le hϖH hzero x]

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

section

variable [(N.normSubgroup).Normal] {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)

/-- The quotient by the value-side residue-degree class subgroup is the same
as the quotient by the norm-class subgroup when valuation-zero target elements
are norms. -/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivNormClass :
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
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q := rfl

end

section

variable [(N.normSubgroup).Normal] (hzero : vG.zeroSubgroup ≤ N.normSubgroup)

/-- The natural map `G/G⁰ → G/N`, where `N` is a norm subgroup containing
the valuation-zero subgroup. -/
def zeroSubgroupQuotientToNormQuotient :
    G ⧸ vG.zeroSubgroup →* G ⧸ N.normSubgroup :=
  QuotientGroup.map vG.zeroSubgroup N.normSubgroup (MonoidHom.id G) (fun x hx => hzero hx)

/-- The third-isomorphism equivalence
`(G/G⁰)/(N/G⁰) ≃ G/N` for the norm subgroup. -/
noncomputable def zeroQuotientModuloNormClassEquivNormQuotient :
    (G ⧸ vG.zeroSubgroup) ⧸ N.normSubgroupClassInZeroQuotient ≃*
      G ⧸ N.normSubgroup :=
  QuotientGroup.quotientQuotientEquivQuotient
    vG.zeroSubgroup N.normSubgroup hzero

/--
Establishes the identity `N.zeroQuotientModuloNormClassEquivNormQuotient hzero (QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient q) = N.zeroSubgroupQuotientToNormQuotient hzero q`.
-/
@[simp] theorem zeroQuotientModuloNormClassEquivNormQuotient_mk
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloNormClassEquivNormQuotient hzero
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) =
      N.zeroSubgroupQuotientToNormQuotient hzero q := by
  exact
    ((by apply QuotientGroup.quotientQuotientEquivQuotientAux_mk))

end

section

variable [(N.normSubgroup).Normal] {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)

/-- Direct form of the quotient comparison from the residue-degree class
subgroup to the norm quotient. -/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivNormQuotient :
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
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      N.zeroSubgroupQuotientToNormQuotient hzero q := by
  rfl

end

variable [(N.normSubgroup).Normal] {ϖG : G} (hϖG : vG.IsUniformizer ϖG) {ϖH : H}
    (hϖH : vH.IsUniformizer ϖH) (hzero : vG.zeroSubgroup ≤ N.normSubgroup)

/-- The actual norm quotient is the value-group quotient `ℤ / fℤ` when
valuation-zero target elements are norms and the target valuation has a
uniformizer. -/
noncomputable def normQuotientEquivValueModResidueDegree :
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
@[simp] theorem normQuotientEquivValueModResidueDegree_mk (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (vG.valuationHom x) := by
  exact QuotientGroup.kerLift_mk N.valueModResidueDegreeHom x

/--
Establishes the identity `N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
(QuotientGroup.mk' N.normSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree
: ℤ)) (Multiplicative.ofAdd (vG.val x))`.
-/
theorem normQuotientEquivValueModResidueDegree_mk_ofAdd (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rfl

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
    {vG : MultiplicativeIntegerValuation G}
    {vH : MultiplicativeIntegerValuation H}
    (N : ValuedNorm vG vH)

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
  rfl

end ValuedNorm

end DiscreteValuationField

end

end LocalFieldTheory
