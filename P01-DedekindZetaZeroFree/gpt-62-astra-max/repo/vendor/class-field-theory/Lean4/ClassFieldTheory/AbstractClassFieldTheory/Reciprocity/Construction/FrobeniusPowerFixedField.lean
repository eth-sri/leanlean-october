module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateFieldCompositum

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Frobenius power fixed fields

This module constructs the fixed fields of powers of a Frobenius element and
proves their inclusion, exponent, normality, unramifiedness, finiteness,
degree, quotient-cardinality, and generator properties.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section degreeOnePowerFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- An element fixing `L` commutes modulo `G_{\widetilde L}` with every
degree-zero element of `G(\widetilde L/K)`.  Group-theoretically this is
`[G_L,I_K] ⊆ G_L ∩ I_K = G_{\widetilde L}`; it is the reason the
fields fixed by the powers of `φⁿ` in the universal norm-descent lemma are stable under the
elements `τᵢ` occurring in `(*)`. -/
theorem extensionInertia_commutes_of_mem_extensionSubgroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (k : K.field.toSubgroup) (hk : k ∈ extensionSubgroup K.field L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1) :
    (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) * q =
      q * QuotientGroup.mk k := by
  revert hq
  refine Quotient.inductionOn' q ?_
  intro t hdt
  apply QuotientGroup.eq.mpr
  constructor
  · change (k * t)⁻¹ * (t * k) ∈ extensionSubgroup K.field L hLK
    have hconj : t⁻¹ * k⁻¹ * t ∈ extensionSubgroup K.field L hLK := by
      simpa using hLnormal.conj_mem k⁻¹
        ((extensionSubgroup K.field L hLK).inv_mem hk) t⁻¹
    simpa [mul_assoc] using
      (extensionSubgroup K.field L hLK).mul_mem hconj hk
  · simp [mul_assoc]

/-- Let `P/K` be a finite Galois subextension of `\widetilde L/K`
containing `L`.  The `|G(P/K)|`-th power of every element of
`G(\widetilde L/K)` fixes `P`, hence commutes with the degree-zero kernel.
This is the precise finite-stage input behind the choice
`n = [M:K]`, `σ = φⁿ`. -/
theorem quotientPower_card_commutes_degreeZero (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    (hPL : P.field.toSubgroup ≤ L.toSubgroup)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (q τ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτ : D.extensionNormalizedDegree K L hLK τ = 1) :
    let n := Nat.card
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below)
    q ^ n * τ = τ * q ^ n := by
  let R := K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below
  let := P.finite
  let n := Nat.card R
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let hIP : D.extensionInertiaWithin K.field L hLK ≤
      extensionSubgroup K.field P.field P.below := by
    solve_by_elim [P.above]
  let rP :=
    QuotientGroup.map (D.extensionInertiaWithin K.field L hLK)
      (extensionSubgroup K.field P.field P.below)
      (MonoidHom.id K.field.toSubgroup) hIP
  let k : K.field.toSubgroup := Quotient.out (q ^ n)
  have hkq : (QuotientGroup.mk k : Q) = q ^ n :=
    Quotient.out_eq' (q ^ n)
  have hrPpow : rP (q ^ n) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one'
  have hkP : k ∈ extensionSubgroup K.field P.field P.below := by
    apply (QuotientGroup.eq_one_iff k).1
    calc
      (QuotientGroup.mk k : R) = rP (QuotientGroup.mk k) := rfl
      _ = rP (q ^ n) := congrArg rP hkq
      _ = 1 := hrPpow
  have hkL : k ∈ extensionSubgroup K.field L hLK := by
    apply (mem_extensionSubgroup_iff K.field L hLK k).2
    exact hPL ((mem_extensionSubgroup_iff K.field P.field P.below k).1 hkP)
  have hcomm := D.extensionInertia_commutes_of_mem_extensionSubgroup
    K L hLK k hkL τ hτ
  simpa [hkq] using hcomm

section

variable (D : DegreeData G) (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK) (hφ : D.frobeniusExponent K L hLK φ = 1) (n : ℕ)

include hφ in
theorem extensionNormalizedDegree_pow_of_degreeOne :
    D.extensionNormalizedDegree K L hLK (φ.1 ^ n) =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
  rw [map_pow,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ, hφ]
  simp

/-- A positive power of a degree-one Frobenius element, with the exponent
recorded exactly.  These are the elements `σ = φⁿ` and `σⁿ = φⁿ²`. -/
def frobeniusPowerOfDegreeOne (hn : 0 < n) : D.FrobeniusElements K L hLK :=
  ⟨φ.1 ^ n,
    ⟨n, hn, D.extensionNormalizedDegree_pow_of_degreeOne
      K L hLK φ hφ n⟩⟩

/-- The degree-one Frobenius power has the stated ambient coercion. -/
@[simp]
theorem frobeniusPowerOfDegreeOne_coe (hn : 0 < n) :
    (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn).1 = φ.1 ^ n :=
  rfl

end

/-- If `P/K` is finite Galois and contained in `\widetilde L`, then `P`
is contained in the field fixed by `φⁿ`, where
`n = |G(P/K)|`.  Indeed `φⁿ` is trivial in `G(P/K)`, and the kernel
of the restriction map is closed, so it contains the whole procyclic
closure generated by `φⁿ`. -/
theorem frobeniusPowerFixedField_le_finiteField (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    let n := P.quotientCard
    let hn : 0 < n := P.quotientCard_pos
    (D.frobeniusFixedField K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).toSubgroup ≤
      P.field.toSubgroup := by
  dsimp only
  let R := K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below
  let n := P.quotientCard
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let hIP : D.extensionInertiaWithin K.field L hLK ≤
      extensionSubgroup K.field P.field P.below := by
    solve_by_elim [P.above]
  let rP : Q →ₜ* R :=
    { toMonoidHom :=
        QuotientGroup.map
          (N := D.extensionInertiaWithin K.field L hLK)
          (M := extensionSubgroup K.field P.field P.below)
          (f := MonoidHom.id K.field.toSubgroup) hIP
      continuous_toFun := by
        solve_by_elim [QuotientGroup.map]}
  let := P.finite
  let :=
    extensionSubgroup_isClosed K.field P.field P.below
  have hrPpow : rP (φ.1 ^ n) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one'
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n P.quotientCard_pos
  have hclosure :
      (D.frobeniusClosure K L hLK σ).toSubgroup ≤
        rP.toMonoidHom.ker := by
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      intro z hz
      have hz' : z = φ.1 ^ n := by simpa [σ] using hz
      subst z
      exact hrPpow
    · exact isClosed_eq rP.continuous continuous_const
  rintro g ⟨k, hk, rfl⟩
  apply (mem_extensionSubgroup_iff K.field P.field P.below k).1
  apply (QuotientGroup.eq_one_iff k).1
  have hk' := hclosure hk
  change QuotientGroup.mk' (extensionSubgroup K.field P.field P.below) k = 1 at hk'
  exact hk'

/-- The Frobenius exponent of the degree-one power is the supplied exponent. -/
@[simp]
theorem frobeniusExponent_powerOfDegreeOne (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) (hn : 0 < n) :
    D.frobeniusExponent K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn) = n :=
  by
    apply proCIntegerOne_pow_nat_injective
    exact ((D.extensionNormalizedDegree_frobenius_eq_pow K L hLK (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).symm).trans (D.extensionNormalizedDegree_pow_of_degreeOne K L hLK φ hφ n)

private theorem frobeniusClosure_power_mul_le (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (D.frobeniusClosure K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
        (Nat.mul_pos hn hm))).toSubgroup ≤
      (D.frobeniusClosure K L hLK
        (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).toSubgroup := by
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let x := φ.1 ^ n
  let C := closedSubgroupGenerated ({x} : Set Q)
  have hpowC : φ.1 ^ (n * m) ∈ C.toSubgroup := by
    rw [pow_mul]
    exact C.toSubgroup.pow_mem (Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure (by simp [x]))) m
  change (closedSubgroupGenerated
      (Set.range (fun _ : Unit => φ.1 ^ (n * m)))).toSubgroup ≤
    (closedSubgroupGenerated
      (Set.range (fun _ : Unit => φ.1 ^ n))).toSubgroup
  have hrangeLeft : Set.range (fun _ : Unit => φ.1 ^ (n * m)) =
      ({φ.1 ^ (n * m)} : Set Q) := by ext q; simp
  have hrangeRight : Set.range (fun _ : Unit => φ.1 ^ n) =
      ({φ.1 ^ n} : Set Q) := by ext q; simp
  rw [hrangeLeft, hrangeRight]
  apply Subgroup.topologicalClosure_minimal
  · simpa using hpowC
  apply ClosedSubgroup.isClosed'

/-- If `Σ` is fixed by `φⁿ`, then the field fixed by `φⁿᵐ` extends `Σ`.
This is the tower `Σ_m / Σ` used in the universal norm-descent lemma. -/
theorem frobeniusPowerFixedField_le (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (D.frobeniusFixedField K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
        (Nat.mul_pos hn hm))).toSubgroup ≤
      (D.frobeniusFixedField K L hLK
        (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).toSubgroup := by
  rintro z ⟨k, hk, rfl⟩
  exact ⟨k,
    D.frobeniusClosure_power_mul_le K L hLK φ hφ n m hn hm hk,
    rfl⟩

section

variable (D : DegreeData G) [IsTopologicalGroup G]

/-- The power-fixed-field tower is Galois.  On the group side this is the
normality of `closure ⟨φⁿᵐ⟩` inside the procyclic group
`closure ⟨φⁿ⟩`. -/
theorem frobeniusPowerFixedField_normal [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    (extensionSubgroup S T
      (D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm)).Normal := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hSK := D.frobeniusFixedField_le K L hLK σ
  let hTK := D.frobeniusFixedField_le K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
  let C := D.frobeniusClosure K L hLK σ
  let Cm := D.frobeniusClosure K L hLK σm
  let : CommGroup C := D.frobeniusClosureCommGroup K L hLK σ
  have hCmC :=
    D.frobeniusClosure_power_mul_le K L hLK φ hφ n m hn hm
  constructor
  intro t ht s
  have htT : t.1 ∈ T.toSubgroup :=
    (mem_extensionSubgroup_iff S T hTS t).1 ht
  let tK : K.field.toSubgroup := ⟨t.1, hSK t.2⟩
  let sK : K.field.toSubgroup := ⟨s.1, hSK s.2⟩
  have htFixed : tK ∈ D.frobeniusFixedSubgroupWithin K L hLK σm := by
    rw [← D.extensionSubgroup_frobeniusFixedField K L hLK σm]
    exact (mem_extensionSubgroup_iff K.field T hTK tK).2 htT
  have hsFixed : sK ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    rw [← D.extensionSubgroup_frobeniusFixedField K L hLK σ]
    exact (mem_extensionSubgroup_iff K.field S hSK sK).2 s.2
  let a : C := ⟨QuotientGroup.mk sK, hsFixed⟩
  let b : C := ⟨QuotientGroup.mk tK, hCmC htFixed⟩
  have hconj :
      (QuotientGroup.mk sK :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) *
        QuotientGroup.mk tK * (QuotientGroup.mk sK)⁻¹ =
          QuotientGroup.mk tK := by
    exact congrArg Subtype.val (by
      change a * b * a⁻¹ = b
      simp)
  apply (mem_extensionSubgroup_iff S T hTS _).2
  let cK : K.field.toSubgroup := ⟨s.1 * t.1 * s.1⁻¹, by
    exact K.field.toSubgroup.mul_mem
      (K.field.toSubgroup.mul_mem (hSK s.2) (hSK t.2))
      (K.field.toSubgroup.inv_mem (hSK s.2))⟩
  refine ⟨cK, ?_, rfl⟩
  change QuotientGroup.mk cK ∈ Cm.toSubgroup
  change QuotientGroup.mk sK * QuotientGroup.mk tK *
      (QuotientGroup.mk sK)⁻¹ ∈ Cm.toSubgroup
  rw [hconj]
  exact htFixed

/-- The extension fixed by `φⁿᵐ` over the field fixed by `φⁿ` is
unramified. -/
theorem frobeniusPowerFixedField_isUnramified [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
    (DegreeData.AbstractExtension.mk T S hTS).IsUnramified D := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
  rw [(DegreeData.AbstractExtension.mk T S hTS).isUnramified_iff_inertia_le D]
  intro x hx
  have hxI : x ∈ D.fieldInertia S := ⟨hx.1, hx.2⟩
  rw [(D.frobeniusFixedField_fieldInertia K L hLK σ), ← (D.frobeniusFixedField_fieldInertia K L hLK σm)] at hxI
  exact hxI.1

/-- Finiteness of the power-fixed-field tower. -/
theorem frobeniusPowerFixedField_finite [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
    Finite (S.toSubgroup ⧸ extensionSubgroup S T hTS) := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm)
  let hTK := D.frobeniusFixedField_le K L hLK σm
  let hTKfinite :=
    D.frobeniusFixedField_finite K L hLK σm
  exact FiniteIntermediateField.finite_extension_of_le hTK (D.frobeniusFixedField_le K L hLK σ) (D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm)

end

section

variable (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK) (hφ : D.frobeniusExponent K L hLK φ = 1) (n m : ℕ) (hn : 0 < n)
    (hm : 0 < m)

/-- The relative degree of the tower fixed by φⁿᵐ over the field fixed
by φⁿ is exactly m. -/
private theorem frobeniusPowerFixedField_relIndex :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
      (n * m) (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    T.toSubgroup.relIndex S.toSubgroup = m := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
    (n * m) (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le
    K L hLK φ hφ n m hn hm
  have hTSramification :
      (T.toSubgroup ⊓ D.degree.toMonoidHom.ker).relIndex
          (S.toSubgroup ⊓ D.degree.toMonoidHom.ker) = 1 := by
    rw [Subgroup.relIndex_eq_one]
    intro x hx
    exact ⟨(D.frobeniusPowerFixedField_isUnramified
      K L hLK φ hφ n m hn hm) hx, hx.2⟩
  rw [relIndex_eq_map_relIndex_mul_inf_ker_relIndex
      D.degree.toMonoidHom hTS,
    hTSramification, Nat.mul_one]
  let SR := D.frobeniusFixedResidueField K L hLK σ
  let TR := D.frobeniusFixedResidueField K L hLK σm
  have hSindex : (D.fieldImage S).index = (SR.residueDegree : ℕ) := by
    have h := D.fieldImageAdd_index SR
    change (D.fieldImage S).index = (SR.residueDegree : ℕ) at h
    exact h
  have hTindex : (D.fieldImage T).index = (TR.residueDegree : ℕ) := by
    have h := D.fieldImageAdd_index TR
    change (D.fieldImage T).index = (TR.residueDegree : ℕ) at h
    exact h
  have hresidueMul :
      (T.toSubgroup.map D.degree.toMonoidHom).relIndex
          (S.toSubgroup.map D.degree.toMonoidHom) *
          (SR.residueDegree : ℕ) = (TR.residueDegree : ℕ) := by
    rw [← hSindex, ← hTindex, D.fieldImage_eq_map, D.fieldImage_eq_map]
    exact Subgroup.relIndex_mul_index (Subgroup.map_mono hTS)
  rw [D.frobeniusFixedResidueField_residueDegree K L hLK σ,
    D.frobeniusFixedResidueField_residueDegree K L hLK σm] at hresidueMul
  rw [show D.frobeniusExponent K L hLK σm = n * m by
      exact D.frobeniusExponent_powerOfDegreeOne
        K L hLK φ hφ (n * m) (Nat.mul_pos hn hm),
    show D.frobeniusExponent K L hLK σ = n by
      exact D.frobeniusExponent_powerOfDegreeOne
        K L hLK φ hφ n hn] at hresidueMul
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hn K.residueDegree.property)
  calc
    _ =
      (n * m) * (K.residueDegree : ℕ) := hresidueMul
    _ = m * (n * (K.residueDegree : ℕ)) := by ac_rfl

/-- The quotient between two successive Frobenius power fixed fields is
genuinely finite.  This is obtained from the computed finite relative index,
before taking its natural-valued cardinality. -/
theorem frobeniusPowerFixedField_quotientFinite :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
      (n * m) (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTS := D.frobeniusPowerFixedField_le
      K L hLK φ hφ n m hn hm
    Finite (S.toSubgroup ⧸ extensionSubgroup S T hTS) := by
  dsimp only
  let T := D.frobeniusFixedField K L hLK (D.frobeniusPowerOfDegreeOne K L hLK φ hφ
    (n * m) (Nat.mul_pos hn hm))
  apply (Subgroup.index_ne_zero_iff_finite).mp
  change T.toSubgroup.relIndex (D.frobeniusFixedField K L hLK (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).toSubgroup ≠ 0
  rw [D.frobeniusPowerFixedField_relIndex
    K L hLK φ hφ n m hn hm]
  exact hm.ne'

/-- Cardinality form of the preceding relative-degree computation. -/
theorem frobeniusPowerFixedField_quotientCard :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
      (n * m) (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTS := D.frobeniusPowerFixedField_le
      K L hLK φ hφ n m hn hm
    Nat.card (S.toSubgroup ⧸ extensionSubgroup S T hTS) = m := by
  apply D.frobeniusPowerFixedField_relIndex <;> assumption

end

/-- The restriction of the concrete element `φⁿ` is a degree-one
generator of `Gal(Σₘ/Σ)`.  This is the generator to which the unit-cohomology axiom
is applied; retaining the actual representative is essential for
the subsequent equation involving `σ = φⁿ`. -/
theorem frobeniusPowerFixedField_generator (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
    let hTSnormal : (extensionSubgroup S T hTS).Normal :=
      D.frobeniusPowerFixedField_normal K L hLK φ hφ n m hn hm
    letI := hTSnormal
    ∃ s : S.toSubgroup,
      D.frobeniusFixedFieldToClosure K L hLK σ s =
          D.frobeniusInClosure K L hLK σ ∧
      D.normalizedDegree (D.frobeniusFixedResidueField K L hLK σ) s =
        Multiplicative.ofAdd (1 : ZHat) ∧
      ∀ x : S.toSubgroup ⧸ extensionSubgroup S T hTS,
        x ∈ Subgroup.zpowers (QuotientGroup.mk s) := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK (D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm))
  let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
  let hTSnormal :=
    D.frobeniusPowerFixedField_normal K L hLK φ hφ n m hn hm
  let := hTSnormal
  let k : K.field.toSubgroup := Quotient.out σ.1
  have hkσ :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = σ.1 :=
    Quotient.out_eq' σ.1
  have hkClosure : QuotientGroup.mk k ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup := by
    rw [hkσ]
    exact (D.frobeniusInClosure K L hLK σ).2
  let s : S.toSubgroup := ⟨k.1, ⟨k, hkClosure, rfl⟩⟩
  have hsClosure :
      D.frobeniusFixedFieldToClosure K L hLK σ s =
        D.frobeniusInClosure K L hLK σ := by
    apply Subtype.ext
    exact hkσ
  have hsDegree :
      D.normalizedDegree (D.frobeniusFixedResidueField K L hLK σ) s =
        Multiplicative.ofAdd (1 : ZHat) := by
    rw [← D.frobeniusFixedField_normalizedDegree_compatibility
      K L hLK σ s, hsClosure]
    exact D.fixedFieldNormalizedDegree_generator K L hLK σ
  let SR := D.frobeniusFixedResidueField K L hLK σ
  let : (extensionSubgroup SR.field T hTS).Normal := by
    exact hTSnormal
  let : Finite
      (SR.field.toSubgroup ⧸ extensionSubgroup SR.field T hTS) := by
    apply D.frobeniusPowerFixedField_finite <;> assumption
  have hTSunramifiedR :
      (DegreeData.AbstractExtension.mk T SR.field hTS).IsUnramified D := by
    exact (D.frobeniusPowerFixedField_isUnramified
      K L hLK φ hφ n m hn hm)
  refine ⟨s, hsClosure, hsDegree, ?_⟩
  exact D.quotient_generator_of_unramified_degree_one
    SR T hTS hTSunramifiedR s hsDegree

end DegreeData
end degreeOnePowerFields

end

end ClassFormation
