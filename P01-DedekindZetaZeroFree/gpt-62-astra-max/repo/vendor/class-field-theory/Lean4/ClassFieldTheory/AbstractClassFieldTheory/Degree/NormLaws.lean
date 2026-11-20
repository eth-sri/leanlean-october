module

public import ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation
public import GaloisCohomology.GroupTheory.QuotientTower

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# Laws for relative norms

This file proves the structural laws for the coset-sum norm constructed in `Norm.lean`.
-/

noncomputable section

open scoped BigOperators Pointwise

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

section

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] (K : ClosedSubgroup G)

/-- The subgroup corresponding to the conjugate abstract field `K^σ`.

The construction uses a right exponent, hence `G_{K^σ} = σ⁻¹ G_K σ`. -/
def conjugateClosedSubgroup (σ : G) : ClosedSubgroup G where
  toSubgroup := ConjAct.toConjAct σ⁻¹ • K.toSubgroup
  isClosed' := by
    convert IsClosed.preimage
      (IsTopologicalGroup.continuous_conj (G := G) σ) K.isClosed' using 1
    ext x
    change x ∈ (ConjAct.toConjAct σ⁻¹ • K.toSubgroup : Subgroup G) ↔
      σ * x * σ⁻¹ ∈ K.toSubgroup
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]

/--
Characterizes `x ∈ conjugateClosedSubgroup K σ` by the equivalent condition `σ * x * σ⁻¹ ∈ K`.
-/
@[simp]
theorem conjugateClosedSubgroup_mem (σ x : G) :
    x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K := by
  change x ∈ (ConjAct.toConjAct σ⁻¹ • K.toSubgroup : Subgroup G) ↔
    σ * x * σ⁻¹ ∈ K.toSubgroup
  simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]

end

section

variable [ContinuousMul G] (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G) (a : ambientFixedAddSubgroup A K)

/-- The right-conjugate `a^σ`, expressed through the left action of `G`. -/
def conjugateFixedElement :
    ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ) := by
  refine ⟨A.ρ σ⁻¹ a.1, ?_⟩
  intro x
  let k : K.toSubgroup := ⟨σ * x.1 * σ⁻¹,
    (conjugateClosedSubgroup_mem K σ x.1).mp x.2⟩
  calc
    _ = A.ρ (x.1 * σ⁻¹) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (σ⁻¹ * k.1) a.1 := by simp [k, mul_assoc]
    _ = A.ρ σ⁻¹ (A.ρ k.1 a.1) := by
      rw [map_mul]
      rfl
    _ = A.ρ σ⁻¹ a.1 := by rw [a.2 k]

/--
Establishes the identity `((conjugateFixedElement A K σ a : ambientFixedAddSubgroup A
(conjugateClosedSubgroup K σ)) : A.V) = A.ρ σ⁻¹ a.1`.
-/
@[simp]
theorem conjugateFixedElement_coe :
    ((conjugateFixedElement A K σ a :
      ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ)) : A.V) =
      A.ρ σ⁻¹ a.1 :=
  rfl

end

 section

variable {G : Type*} [Group G] [TopologicalSpace G]

def absoluteConjugationEquiv
    (σ : G) :
    (baseField G).toSubgroup ≃
      (baseField G).toSubgroup where
  toFun x := ⟨σ * x.1 * σ⁻¹, trivial⟩
  invFun x := ⟨σ⁻¹ * x.1 * σ, trivial⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]

 theorem mem_absoluteExtension
    (K : ClosedSubgroup G)
    (x : (baseField G).toSubgroup) :
    x ∈ extensionSubgroup (baseField G) K
        (le_baseField K) ↔ x.1 ∈ K :=
  Iff.rfl

/-- Conjugation identifies the absolute coset spaces for `K^σ` and `K`. -/
noncomputable def absoluteConjugateCosetEquiv [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G) :
    ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (conjugateClosedSubgroup K σ)
          (le_baseField (conjugateClosedSubgroup K σ))) ≃
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K)) :=
  Quotient.congr (absoluteConjugationEquiv σ) (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply,
      mem_absoluteExtension, mem_absoluteExtension,
      conjugateClosedSubgroup_mem]
    change σ * (x.1⁻¹ * y.1) * σ⁻¹ ∈ K.toSubgroup ↔
      (σ * x.1 * σ⁻¹)⁻¹ * (σ * y.1 * σ⁻¹) ∈ K.toSubgroup
    simp [mul_assoc])

/--
Establishes the identity `absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) = QuotientGroup.mk
(absoluteConjugationEquiv σ x)`.
-/
@[simp]
theorem absoluteConjugateCosetEquiv_mk [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G)
    (x : (baseField G).toSubgroup) :
    absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) =
      QuotientGroup.mk (absoluteConjugationEquiv σ x) :=
  rfl

end

section

variable [ContinuousMul G] (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)

private theorem relativeCosetAction_absoluteConjugate
    (a : ambientFixedAddSubgroup A K)
    (q : (baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))) :
    relativeCosetAction A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) q =
      A.ρ σ⁻¹
        (relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
  refine Quotient.inductionOn' q ?_
  intro x
  rw [relativeCosetAction_mk, absoluteConjugateCosetEquiv_mk,
    relativeCosetAction_mk, conjugateFixedElement_coe]
  calc
    _ = A.ρ (x.1 * σ⁻¹) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (σ⁻¹ * (σ * x.1 * σ⁻¹)) a.1 := by simp [mul_assoc]
    _ = A.ρ σ⁻¹ (A.ρ (σ * x.1 * σ⁻¹) a.1) := by
      rw [map_mul]
      rfl

/-- conjugation compatibility of normalized valuations: the absolute norm commutes with conjugation.

The construction writes the action on fields and elements on the right.  Thus the
left action used by `Rep` realizes `a^σ` as `ρ(σ⁻¹)a`. -/
theorem relativeNorm_absoluteConjugate_apply
    [Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K))]
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G)
            (conjugateClosedSubgroup K σ)
            (le_baseField (conjugateClosedSubgroup K σ))) :=
      Finite.of_equiv
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) K
            (le_baseField K))
        (absoluteConjugateCosetEquiv K σ).symm
    ((relativeNorm A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) :
      ambientFixedAddSubgroup A (baseField G)) : A.V) =
      A.ρ σ⁻¹
        ((relativeNorm A (baseField G) K
          (le_baseField K) a :
          ambientFixedAddSubgroup A (baseField G)) : A.V) := by
  let := Fintype.ofFinite
    ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K
        (le_baseField K))
  let conjugateFintype :=
    Fintype.ofEquiv
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K))
      (absoluteConjugateCosetEquiv K σ).symm
  have hconjugateFintype : Fintype.ofFinite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (conjugateClosedSubgroup K σ)
          (le_baseField (conjugateClosedSubgroup K σ))) = conjugateFintype :=
    Subsingleton.elim _ _
  simp only [relativeNorm_apply_coe, relativeNormValue]
  rw [hconjugateFintype]
  let relativeCosetAction₀ := relativeCosetAction A (baseField G) K (le_baseField K) a
  calc
    _ =
      ∑ q, A.ρ σ⁻¹
        (relativeCosetAction₀
          (absoluteConjugateCosetEquiv K σ q)) := by
            solve_by_elim [Finset.sum_congr, relativeCosetAction_absoluteConjugate]
    _ = A.ρ σ⁻¹
        (∑ q, relativeCosetAction₀
          (absoluteConjugateCosetEquiv K σ q)) := by
            rw [map_sum]
    _ = A.ρ σ⁻¹
        (∑ q, relativeCosetAction₀ q) := by
            rw [(absoluteConjugateCosetEquiv K σ).sum_comp]

end

section

variable (A : Rep ℤ G) (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)

/-- The action of an element of `G_K` on `A_L`, when `L | K` is Galois.

Normality is used only to prove that the translate is still fixed by `G_L`. -/
def normalExtensionAction
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    ambientFixedAddSubgroup A L := by
  refine ⟨A.ρ k.1 a.1, ?_⟩
  intro l
  let lK := Subgroup.inclusion hLK l
  have hc : k⁻¹ * lK * k ∈ extensionSubgroup K L hLK :=
    by simpa using hnormal.conj_mem lK l.2 k⁻¹
  let l' : L.toSubgroup := ⟨(k⁻¹ * lK * k).1, hc⟩
  have hl'val : (l' : G) = (k⁻¹ * lK * k : K.toSubgroup) :=
    rfl
  calc
    A.ρ l.1 (A.ρ k.1 a.1) = A.ρ (l.1 * k.1) a.1 := by rw [map_mul]; rfl
    _ = A.ρ (k.1 * l'.1) a.1 := by rw [hl'val]; simp [lK, mul_assoc]
    _ = A.ρ k.1 (A.ρ l'.1 a.1) := by rw [map_mul]; rfl
    _ = A.ρ k.1 a.1 := by rw [a.2 l']

/--
Establishes the identity `((normalExtensionAction A K L hLK hnormal k a : ambientFixedAddSubgroup
A L) : A.V) = A.ρ k.1 a.1`.
-/
@[simp]
theorem normalExtensionAction_coe
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    ((normalExtensionAction A K L hLK hnormal k a : ambientFixedAddSubgroup A L) : A.V) =
      A.ρ k.1 a.1 :=
  rfl

/-- For a finite Galois abstract extension, the relative norm is invariant under
the `G_K`-conjugacy action on `A_L`. -/
theorem relativeNorm_normalExtensionAction
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    relativeNorm A K L hLK (normalExtensionAction A K L hLK hnormal k a) =
      relativeNorm A K L hLK a := by
  apply Subtype.ext
  let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let e : (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    Equiv.mulRight (QuotientGroup.mk k)
  have hterm : ∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
      relativeCosetAction A K L hLK (normalExtensionAction A K L hLK hnormal k a) q =
        relativeCosetAction A K L hLK a (e q) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    simp only [relativeCosetAction_mk, normalExtensionAction_coe]
    have he : e (QuotientGroup.mk x) = QuotientGroup.mk (x * k) := rfl
    rw [he, relativeCosetAction_mk]
    change A.ρ x.1 (A.ρ k.1 a.1) = A.ρ (x.1 * k.1) a.1
    rw [map_mul]
    rfl
  simp only [relativeNorm_apply_coe, relativeNormValue]
  simp_rw [hterm]
  exact e.sum_comp (relativeCosetAction A K L hLK a)

end

/-- Finiteness is closed under composition in a tower of closed subgroups. -/
theorem relativeTowerQuotientFinite
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [Finite (L.toSubgroup ⧸ extensionSubgroup L M hML)] :
    Finite
      (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK)) :=
  Finite.of_equiv
    ((K.toSubgroup ⧸ extensionSubgroup K L hLK) ×
      (L.toSubgroup ⧸ extensionSubgroup L M hML))
    (Subgroup.quotientTowerEquiv hML hLK).symm

namespace DegreeData.FiniteTower

variable (T : DegreeData.FiniteTower G)

/-- The finite composite extension represented by a finite tower. -/
noncomputable def totalExtension : DegreeData.FiniteAbstractExtension G where
  toAbstractExtension := T.toTower.totalExtension
  finiteQuotient := relativeTowerQuotientFinite
    T.base T.middle T.top T.top_le_middle T.middle_le_base

/-- The quotient from the top to the base of a finite tower is finite. -/
instance totalQuotientFinite :
    Finite (T.base.toSubgroup ⧸
      extensionSubgroup T.base T.top
        (T.top_le_middle.trans T.middle_le_base)) :=
  T.totalExtension.finiteQuotient

end DegreeData.FiniteTower

private theorem relativeCosetAction_towerProductEquiv
    (A : Rep ℤ G) (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A M)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (r : L.toSubgroup ⧸ extensionSubgroup L M hML) :
    relativeCosetAction A K M (hML.trans hLK) a
        ((Subgroup.quotientTowerEquiv hML hLK).symm (q, r)) =
      A.ρ (Quotient.out q).1 (relativeCosetAction A L M hML a r) := by
  refine Quotient.inductionOn' r ?_
  intro x
  have he : (Subgroup.quotientTowerEquiv hML hLK).symm
      (q, QuotientGroup.mk x) =
      QuotientGroup.mk (Quotient.out q * Subgroup.inclusion hLK x) := rfl
  simp_all

namespace DegreeData.FiniteTower

variable (T : DegreeData.FiniteTower G)

/-- Relative norms are transitive along a finite tower.  All containments and
finite quotient witnesses are obtained from `T`. -/
theorem norm_trans_apply (A : Rep ℤ G)
    (a : ambientFixedAddSubgroup A T.top) :
    relativeNorm A T.base T.middle T.middle_le_base
        (relativeNorm A T.middle T.top T.top_le_middle a) =
      relativeNorm A T.base T.top
        (T.top_le_middle.trans T.middle_le_base) a := by
          apply Subtype.ext
          let := Fintype.ofFinite (T.base.toSubgroup ⧸ extensionSubgroup T.base T.middle T.middle_le_base)
          let := Fintype.ofFinite (T.middle.toSubgroup ⧸ extensionSubgroup T.middle T.top T.top_le_middle)
          let totalFintype :=
            Fintype.ofEquiv
              ((T.base.toSubgroup ⧸ extensionSubgroup T.base T.middle T.middle_le_base) ×
                (T.middle.toSubgroup ⧸ extensionSubgroup T.middle T.top T.top_le_middle))
              (Subgroup.quotientTowerEquiv T.top_le_middle T.middle_le_base).symm
          have htotalFintype : Fintype.ofFinite
              (T.base.toSubgroup ⧸ extensionSubgroup T.base T.top (T.top_le_middle.trans T.middle_le_base)) = totalFintype :=
            Subsingleton.elim _ _
          have houter : ∀ q : T.base.toSubgroup ⧸ extensionSubgroup T.base T.middle T.middle_le_base,
              relativeCosetAction A T.base T.middle T.middle_le_base (relativeNorm A T.middle T.top T.top_le_middle a) q =
                A.ρ (Quotient.out q).1 (relativeNormValue A T.middle T.top T.top_le_middle a) := by
            intro q
            calc
              _ =
                  relativeCosetAction A T.base T.middle T.middle_le_base (relativeNorm A T.middle T.top T.top_le_middle a)
                    (QuotientGroup.mk (Quotient.out q)) := congrArg
                        (relativeCosetAction A T.base T.middle T.middle_le_base (relativeNorm A T.middle T.top T.top_le_middle a))
                        (Quotient.out_eq' q).symm
              _ = A.ρ (Quotient.out q).1
                  ((relativeNorm A T.middle T.top T.top_le_middle a : ambientFixedAddSubgroup A T.middle) : A.V) :=
                relativeCosetAction_mk A T.base T.middle T.middle_le_base (relativeNorm A T.middle T.top T.top_le_middle a)
                  (Quotient.out q)
              _ = A.ρ (Quotient.out q).1 (relativeNormValue A T.middle T.top T.top_le_middle a) := by
                rfl
          simp only [relativeNorm_apply_coe, relativeNormValue]
          rw [htotalFintype]
          rw [Finset.sum_congr rfl (fun q _ ↦ houter q)]
          simp only [relativeNormValue]
          simp_rw [map_sum]
          rw [← Fintype.sum_prod_type (f := fun p :
            (T.base.toSubgroup ⧸ extensionSubgroup T.base T.middle T.middle_le_base) ×
              (T.middle.toSubgroup ⧸ extensionSubgroup T.middle T.top T.top_le_middle) ↦
                A.ρ (Quotient.out p.1).1
                  (relativeCosetAction A T.middle T.top T.top_le_middle a p.2))]
          calc
            _ =
              ∑ p, relativeCosetAction A T.base T.top (T.top_le_middle.trans T.middle_le_base) a
                ((Subgroup.quotientTowerEquiv T.top_le_middle T.middle_le_base).symm p) := by
                  grind [relativeCosetAction_towerProductEquiv]
            _ = ∑ q, relativeCosetAction A T.base T.top (T.top_le_middle.trans T.middle_le_base) a q :=
              (Subgroup.quotientTowerEquiv T.top_le_middle T.middle_le_base).symm.sum_comp
                (relativeCosetAction A T.base T.top (T.top_le_middle.trans T.middle_le_base) a)

end DegreeData.FiniteTower

end
end ClassFormation
