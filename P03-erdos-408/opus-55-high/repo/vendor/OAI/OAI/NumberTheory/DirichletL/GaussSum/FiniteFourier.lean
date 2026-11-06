module

public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinIdeals
public import OAI.NumberTheory.DirichletL.Mellin.LogProfiles

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real

namespace ShortDraftFiniteGaussFourier
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]

theorem gauss_transform (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ x : F, χ x * ψ (h * x)) =
      if h = 0 then 0 else (χ h)⁻¹ * gaussSum χ ψ := by
  classical
  by_cases hh : h = 0
  · subst h
    simp only [zero_mul, map_zero_eq_one, mul_one, ite_true]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  · have hu : IsUnit h := isUnit_iff_ne_zero.mpr hh
    have hshift := gaussSum_mulShift_eq χ ψ hu.unit
    simp only [gaussSum, AddChar.mulShift_apply] at hshift
    simpa only [hu.unit_spec, ite_eq_right hh, inv_apply_eq_inv' χ h, gaussSum] using hshift

theorem product_gauss_transform
    {ι : Type*} [Fintype ι]
    (E : ι → Type*) [∀ i, Field (E i)] [∀ i, Fintype (E i)]
    (χ : ∀ i, MulChar (E i) ℂ) (ψ : ∀ i, AddChar (E i) ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : ∀ i, E i) :
    (∑ x : ∀ i, E i, ∏ i, χ i (x i) * ψ i (h i * x i)) =
      ∏ i, if h i = 0 then 0 else (χ i (h i))⁻¹ * gaussSum (χ i) (ψ i) := by
  classical
  calc
    (∑ x : ∀ i, E i, ∏ i, χ i (x i) * ψ i (h i * x i)) =
        ∏ i, ∑ x : E i, χ i x * ψ i (h i * x) := by
      simpa using (Fintype.prod_sum
        (fun i (x : E i) => χ i x * ψ i (h i * x))).symm
    _ = ∏ i, if h i = 0 then 0 else (χ i (h i))⁻¹ * gaussSum (χ i) (ψ i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact gauss_transform (χ i) (ψ i) (by grind) (h i)

end ShortDraftFiniteGaussFourier

namespace PoissonChildCRT
open scoped Classical

variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)

end PoissonChildCRT

namespace PoissonFirstLocal
open scoped Classical

end PoissonFirstLocal

open Finset Complex

namespace ActualCubicChar

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]

omit [IsDomain R] in
theorem cubic_roots_surjective (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    Function.Surjective (restrictRootsOfUnity ρ 3) := by
  intro η
  have hη : ((η : Fˣ) : F) ^ 3 = 1 :=
    (mem_rootsOfUnity' 3 (η : Fˣ)).mp η.property
  obtain ⟨j, _, hj⟩ := hζF.eq_pow_of_pow_eq_one hη
  let z : rootsOfUnity 3 R := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
  refine ⟨z ^ j, ?_⟩
  apply rootsOfUnity.coe_injective
  change ρ (ζ ^ j) = ((η : Fˣ) : F)
  simp_all

def cubic_roots_equiv (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    rootsOfUnity 3 R ≃* rootsOfUnity 3 F := by
  classical
  letI : Fintype (rootsOfUnity 3 R) := Fintype.ofFinite _
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  apply MulEquiv.ofBijective (restrictRootsOfUnity ρ 3)
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · exact cubic_roots_surjective ρ ζ hζ hζF
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hζ.card_rootsOfUnity, hζF.card_rootsOfUnity]

variable [Fintype F]

theorem euler_jacobi_sum_zero (m : ℕ)
    (hm : 2 * m < Fintype.card F - 1) :
    (∑ x : F, x ^ m * (1 - x) ^ m) = 0 := by
  classical
  simp_rw [sub_eq_add_neg, add_pow]
  simp only [one_pow, one_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have he : m + (m - j) < Fintype.card F - 1 := by
    have hle := Nat.sub_le m j
    omega
  calc
    (∑ x : F, x ^ m * ((-x) ^ (m - j) * ↑(m.choose j))) =
        ((-1 : F) ^ (m - j) * ↑(m.choose j)) *
          ∑ x : F, x ^ (m + (m - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 0 := by simp [FiniteField.sum_pow_lt_card_sub_one F _ he]

def euler_to_roots (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    Fˣ →* rootsOfUnity 3 F where
  toFun u := rootsOfUnity.mkOfPowEq ((u : F) ^ m) (by
    rw [← pow_mul, ← hq]
    exact FiniteField.pow_card_sub_one_eq_one (u : F) u.ne_zero)
  map_one' := by
    apply rootsOfUnity.coe_injective
    simp
  map_mul' u v := by
    apply rootsOfUnity.coe_injective
    simp [mul_pow]

def cubicResidueChar (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) : MulChar F R :=
  MulChar.ofUnitHom <|
    (Subgroup.subtype _).comp <|
      (cubic_roots_equiv ρ ζ hζ hζF).symm.toMonoidHom.comp
        (euler_to_roots m hq)

theorem cubicResidueChar_reduce_unit (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) (u : Fˣ) :
    ρ (cubicResidueChar ρ ζ hζ hζF m hq (u : F)) = (u : F) ^ m := by
  let e := cubic_roots_equiv ρ ζ hζ hζF
  simp only [cubicResidueChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (u : F) ^ m
  have he := e.apply_symm_apply (euler_to_roots m hq u)
  have he' := congrArg (fun v : rootsOfUnity 3 F => ((v : Fˣ) : F)) he
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (((euler_to_roots m hq u : rootsOfUnity 3 F) : Fˣ) : F) at he'
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (u : F) ^ m at he'
  omega

theorem cubicResidueChar_pow_three (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    cubicResidueChar ρ ζ hζ hζF m hq ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [(cubicResidueChar ρ ζ hζ hζF m hq).pow_apply_coe,
    MulChar.one_apply_coe]
  simp only [cubicResidueChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]
  let v : rootsOfUnity 3 R :=
    (cubic_roots_equiv ρ ζ hζ hζF).symm (euler_to_roots m hq u)
  change (((v : Rˣ) : R) ^ 3) = 1
  exact (mem_rootsOfUnity' 3 (v : Rˣ)).mp v.property

end ActualCubicChar

namespace ActualEisensteinCubic

section

open NumberField

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

def omega : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

def lambda : O := omega - 1

instance quotientFintype (P : Ideal O) [P.IsMaximal] :
    Fintype (O ⧸ P) := Fintype.ofFinite _

instance quotientField (P : Ideal O) [P.IsMaximal] :
    Field (O ⧸ P) := Ideal.Quotient.field P

theorem omega_primitive : IsPrimitiveRoot omega 3 :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot

def traceLambda : O := 1 + 2 * omega

theorem omega_reduced_primitive (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hpow : (ρ omega) ^ 3 = 1 := by
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hne : ρ omega ≠ 1 := by
    intro he
    apply hgood
    have hz : ρ (omega - 1) = 0 := by rw [map_sub, he, map_one, sub_self]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hz
  apply IsPrimitiveRoot.mk_of_lt _ (by decide) hpow
  intro l hl0 hl3
  have hl : l = 1 ∨ l = 2 := by omega
  rcases hl with rfl | rfl
  · simp_all
  grind

theorem card_sub_one_div_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    3 ∣ Nat.card (O ⧸ P) - 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let hζ := omega_reduced_primitive P hgood
  let u : (O ⧸ P)ˣ := (hζ.isUnit (by decide)).unit
  have hu : IsPrimitiveRoot u 3 := hζ.isUnit_unit (by decide)
  have h := orderOf_dvd_natCard u
  rw [← hu.eq_orderOf] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using h

def cubicChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  exact ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq

theorem cubicChar_reduce (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    (Ideal.Quotient.mk P) (cubicChar P hgood x) =
      x ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 0 < m := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  rw [Nat.card_eq_fintype_card]
  change (Ideal.Quotient.mk P)
      (ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
        omega_primitive (omega_reduced_primitive P hgood) m hq x) = x ^ m
  by_cases hx : x = 0
  · subst x
    rw [(ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
      omega_primitive (omega_reduced_primitive P hgood) m hq).map_zero,
      map_zero, zero_pow hm.ne']
  · let u : (O ⧸ P)ˣ := (isUnit_iff_ne_zero.mpr hx).unit
    have hu : (u : O ⧸ P) = x := (isUnit_iff_ne_zero.mpr hx).unit_spec
    rw [← hu]
    exact ActualCubicChar.cubicResidueChar_reduce_unit
      (Ideal.Quotient.mk P) omega omega_primitive
      (omega_reduced_primitive P hgood) m hq u

theorem cubicChar_pow_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : cubicChar P hgood ^ 3 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  change ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq ^ 3 = 1
  exact ActualCubicChar.cubicResidueChar_pow_three
    (Ideal.Quotient.mk P) omega omega_primitive
    (omega_reduced_primitive P hgood) m hq

theorem cubicChar_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : cubicChar P hgood ≠ 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 0 < m := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  intro hχ
  have hall : ∀ u : (O ⧸ P)ˣ, u ^ m = 1 := by
    intro u
    apply Units.ext
    have hr := cubicChar_reduce P hgood (u : O ⧸ P)
    rw [hχ, MulChar.one_apply_coe, map_one] at hr
    simpa only [Units.val_pow_eq_pow_val, Units.val_one,
      Nat.card_eq_fintype_card] using hr.symm
  have hdvd := (FiniteField.forall_pow_eq_one_iff (O ⧸ P) m).mp hall
  rw [hq] at hdvd
  have hle := Nat.le_of_dvd hm hdvd
  omega

theorem cubicChar_order (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : orderOf (cubicChar P hgood) = 3 := by
  have hdvd :=
    orderOf_dvd_of_pow_eq_one (cubicChar_pow_three P hgood)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact False.elim ((cubicChar_ne_one P hgood) (orderOf_eq_one_iff.mp h1))
  omega

theorem cubicJacobi_primary (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ z ∈ Algebra.adjoin ℤ {omega},
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) =
        -1 + z * lambda ^ 2 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  simpa only [lambda] using
    (exists_jacobiSum_eq_neg_one_add (n := 3) (by decide)
      (cubicChar_pow_three P hgood) (cubicChar_pow_three P hgood)
      (by simpa using card_sub_one_div_three P hgood)
      omega_primitive)

theorem cubicJacobi_mem_prime (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) ∈ P := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 2 * m < Fintype.card (O ⧸ P) - 1 := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, cubicChar_reduce P hgood]
  simp only [Nat.card_eq_fintype_card]
  exact ActualCubicChar.euler_jacobi_sum_zero m hm

theorem cubicJacobi_product (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ =
        (Nat.card (O ⧸ P) : O) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let ι : O →+* K := algebraMap O K
  let ψ := (cubicChar P hgood).ringHomComp ι
  have hchar : ringChar K ≠ ringChar (O ⧸ P) := by
    rw [ringChar.eq_zero]
    exact (CharP.char_is_prime (O ⧸ P) (ringChar (O ⧸ P))).ne_zero.symm
  have hψ : ψ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff RingOfIntegers.coe_injective).mpr
      (cubicChar_ne_one P hgood)
  have hχ2 : cubicChar P hgood * cubicChar P hgood ≠ 1 := by
    intro h
    have hd : orderOf (cubicChar P hgood) ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [cubicChar_order P hgood] at hd
    norm_num at hd
  have hψ2 : ψ * ψ ≠ 1 := by
    rw [show ψ * ψ =
      (cubicChar P hgood * cubicChar P hgood).ringHomComp ι by
        exact (MulChar.ringHomComp_mul _ _ _).symm]
    exact (MulChar.ringHomComp_ne_one_iff RingOfIntegers.coe_injective).mpr hχ2
  have hprod := jacobiSum_mul_jacobiSum_inv hchar hψ hψ hψ2
  apply RingOfIntegers.coe_injective
  change ι (jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹) =
    ι (Nat.card (O ⧸ P) : O)
  rw [map_mul, ← jacobiSum_ringHomComp, ← jacobiSum_ringHomComp,
    ← MulChar.ringHomComp_inv]
  simpa using hprod

def conjK : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

def conjO : O ≃+* O :=
  RingOfIntegers.mapRingEquiv conjK.toRingEquiv

theorem conjO_omega : conjO omega = omega ^ 2 := by
  apply RingOfIntegers.coe_injective
  change conjK (IsCyclotomicExtension.zeta 3 ℚ K) =
    (IsCyclotomicExtension.zeta 3 ℚ K) ^ 2
  exact IsCyclotomicExtension.fromZetaAut_spec
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

theorem conjO_cubic_root (x : O) (hx : x ^ 3 = 1) :
    conjO x = x ^ 2 := by
  obtain ⟨j, _, hj⟩ := omega_primitive.eq_pow_of_pow_eq_one hx
  rw [← hj, map_pow, conjO_omega]
  ring

theorem cubicChar_conj_eq_inv (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    conjO (cubicChar P hgood x) = (cubicChar P hgood)⁻¹ x := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let χ := cubicChar P hgood
  have hinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using cubicChar_pow_three P hgood
  rw [hinv, χ.pow_apply' (by decide)]
  by_cases hx : x = 0
  · simp_all
  · have hχ3 : χ x ^ 3 = 1 := by
      rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    exact conjO_cubic_root (χ x) hχ3

theorem cubicJacobi_conj (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ := by
  classical
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, cubicChar_conj_eq_inv P hgood]
  rfl

theorem cubicJacobi_mul_conj (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
        (Nat.card (O ⧸ P) : O) := by
  rw [cubicJacobi_conj P hgood]
  exact cubicJacobi_product P hgood

end

def quadraticCharO (P : Ideal O) [P.IsMaximal] :
    MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  exact (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O)

theorem quadraticCharO_sq (P : Ideal O) [P.IsMaximal] :
    quadraticCharO P ^ 2 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  change ((quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O)) ^ 2 = 1
  exact ((quadraticChar_isQuadratic (O ⧸ P)).comp (Int.castRingHom O)).sq_eq_one

def sexticChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O :=
  cubicChar P hgood ^ 2 * quadraticCharO P

theorem sexticChar_powers (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    sexticChar P hgood ^ 2 = cubicChar P hgood ∧
    sexticChar P hgood ^ 3 = quadraticCharO P ∧
    sexticChar P hgood ^ 6 = 1 := by
  have hc := cubicChar_pow_three P hgood
  have hq := quadraticCharO_sq P
  let c := cubicChar P hgood
  let q := quadraticCharO P
  have htwo : (c ^ 2 * q) ^ 2 = c := by
    calc
      (c ^ 2 * q) ^ 2 = c ^ 4 * q ^ 2 := by rw [mul_pow, ← pow_mul]
      _ = c := by rw [hq]; calc
        c ^ 4 * 1 = c ^ 3 * c := by group
        _ = c := by grind
  have hthree : (c ^ 2 * q) ^ 3 = q := by
    calc
      (c ^ 2 * q) ^ 3 = (c ^ 3) ^ 2 * (q ^ 2) * q := by simp [mul_pow]; group
      _ = q := by rw [hc, hq]; group
  refine ⟨htwo, hthree, ?_⟩
  calc
    (c ^ 2 * q) ^ 6 = ((c ^ 2 * q) ^ 3) ^ 2 := by group
    _ = 1 := by grind

theorem lambda_not_dvd_two : ¬ lambda ∣ (2 : O) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprime : Prime lambda :=
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'
  let I : Ideal O := Ideal.span {lambda}
  have hI : I.IsMaximal := by
    have hp : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hprime
    have hne : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hprime.ne_zero
    exact hp.isMaximal hne
  let : I.IsMaximal := hI
  let : Field (O ⧸ I) := Ideal.Quotient.field I
  let : Fintype (O ⧸ I) := Fintype.ofFinite _
  have hcard : Nat.card (O ⧸ I) = 3 := by
    change Nat.card (O ⧸ Ideal.span {omega - 1}) = 3
    rw [omega,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
        (by decide)]
    norm_num
  intro hdiv
  have hmem : (2 : O) ∈ I := (Ideal.mem_span_singleton).mpr hdiv
  have hzero : (2 : O ⧸ I) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  have hchar : ringChar (O ⧸ I) = 2 := by
    have hdvd := (ringChar.spec (O ⧸ I) 2).mp hzero
    exact (Nat.prime_dvd_prime_iff_eq
      (CharP.char_is_prime (O ⧸ I) (ringChar (O ⧸ I))) Nat.prime_two).mp hdvd
  have heven := FiniteField.even_card_of_char_two hchar
  simp_all

theorem conjK_ne_refl : conjK ≠ AlgEquiv.refl := by
  intro he
  have hw : omega ^ 2 = omega := by
    have hc : conjO omega = omega := by
      apply NumberField.RingOfIntegers.coe_injective
      change conjK (omega : K) = (omega : K)
      rw [he]
      rfl
    exact conjO_omega.symm.trans hc
  have hw1 : omega = 1 := by
    have hunit : IsUnit omega := omega_primitive.isUnit (by decide)
    apply (mul_left_cancel₀ hunit.ne_zero)
    calc
      omega * omega = omega ^ 2 := by ring
      _ = omega := hw
      _ = omega * 1 := by ring
  exact (omega_primitive.ne_one (by decide)) hw1

theorem galois_card_two : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ K,
    IsCyclotomicExtension.finrank (n := 3) K
      (Polynomial.cyclotomic.irreducible_rat (by decide))]
  decide

theorem galois_univ_pair [DecidableEq (K ≃ₐ[ℚ] K)] :
    (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {(AlgEquiv.refl : K ≃ₐ[ℚ] K), conjK} := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, galois_card_two, Finset.card_pair]
  exact conjK_ne_refl.symm

theorem norm_eq_mul_conjK (p : O) :
    ((Algebra.norm ℚ (p : K) : ℚ) : K) = (p : K) * conjK (p : K) := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  have h := Algebra.norm_eq_prod_automorphisms ℚ (p : K)
  rw [galois_univ_pair, Finset.prod_pair conjK_ne_refl.symm] at h
  simp_all

theorem norm_int_eq_mul_conjO (p : O) :
    ((Algebra.norm ℤ p : ℤ) : O) = p * conjO p := by
  apply NumberField.RingOfIntegers.coe_injective
  change ((Algebra.norm ℤ p : ℤ) : K) = (p : K) * conjK (p : K)
  have h := norm_eq_mul_conjK p
  rw [← Algebra.coe_norm_int p] at h
  simp_all

theorem generator_mul_conj_eq_sign_card (P : Ideal O) [P.IsMaximal]
    (p : O) (hP : P = Ideal.span {p}) :
    p * conjO p = (Nat.card (O ⧸ P) : O) ∨
      p * conjO p = -(Nat.card (O ⧸ P) : O) := by
  have habs : (Algebra.norm ℤ p).natAbs = Nat.card (O ⧸ P) := by
    calc
      (Algebra.norm ℤ p).natAbs = Ideal.absNorm (Ideal.span {p}) :=
        by simp
      _ = Ideal.absNorm P := by simp_all
      _ = Nat.card (O ⧸ P) := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : (Algebra.norm ℤ p) * (Algebra.norm ℤ p) =
      (Nat.card (O ⧸ P) : ℤ) * (Nat.card (O ⧸ P) : ℤ) := by
    apply (Int.natAbs_eq_iff_mul_self_eq).mp
    simpa using habs
  have hzero : (Algebra.norm ℤ p - (Nat.card (O ⧸ P) : ℤ)) *
      (Algebra.norm ℤ p + (Nat.card (O ⧸ P) : ℤ)) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hzero with hpos | hneg
  · left
    have heq := sub_eq_zero.mp hpos
    simp [← norm_int_eq_mul_conjO p, heq]
  · right
    have heq : Algebra.norm ℤ p = -(Nat.card (O ⧸ P) : ℤ) := add_eq_zero_iff_eq_neg.mp hneg
    simp [← norm_int_eq_mul_conjO p, heq]

theorem cubicJacobi_unit_multiple_of_principal (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p}) :
    ∃ u : Oˣ, jacobiSum (cubicChar P hgood) (cubicChar P hgood) = p * u := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hdiv : p ∣ J := (Ideal.mem_span_singleton).mp (hP ▸ cubicJacobi_mem_prime P hgood)
  obtain ⟨v, hv⟩ := hdiv
  have hqne : (Nat.card (O ⧸ P) : O) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hnorm := generator_mul_conj_eq_sign_card P p hP
  have hpne : p * conjO p ≠ 0 := by
    rcases hnorm with h | h
    · simp_all
    · simp_all
  have hprod : (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := by
    calc
      (p * conjO p) * (v * conjO v) = (p * v) * conjO (p * v) := by
        grind
      _ = J * conjO J := by simp_all
      _ = (Nat.card (O ⧸ P) : O) := cubicJacobi_mul_conj P hgood
  have hvnorm : v * conjO v = 1 ∨ v * conjO v = -1 := by
    rcases hnorm with hpos | hneg
    · simp_all
    · right
      apply mul_left_cancel₀ hpne
      simp_all
  have hvunit : IsUnit v := by
    rcases hvnorm with h | h
    · exact IsUnit.of_mul_eq_one (conjO v) h
    · apply IsUnit.of_mul_eq_one (-conjO v)
      simp_all
  refine ⟨hvunit.unit, ?_⟩
  simpa using hv

theorem cubicJacobi_eq_neg_primary_generator_of_principal (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  obtain ⟨u, hJu⟩ := cubicJacobi_unit_multiple_of_principal P hgood p hP
  change J = p * (u : O) at hJu
  obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
  have hJmod : lambda ^ 2 ∣ J + 1 := by
    refine ⟨z, ?_⟩
    dsimp [J]
    rw [hJ]
    ring
  have hucong : lambda ^ 2 ∣ (u : O) + 1 := by
    have heq : (u : O) + 1 = (J + 1) - (p - 1) * (u : O) := by
      rw [hJu]
      ring
    rw [heq]
    exact dvd_sub hJmod (dvd_mul_of_dvd_left hprimary _)
  have hunit : u = 1 ∨ u = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u
    refine ⟨(-1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_neg, Int.cast_one, sub_neg_eq_add] using hucong
  rcases hunit with h1 | hneg
  · have htwo : lambda ^ 2 ∣ (2 : O) := by
      simpa [h1, one_add_one_eq_two] using hucong
    exact False.elim (lambda_not_dvd_two ((dvd_pow_self lambda (by decide)).trans htwo))
  · rw [hneg] at hJu
    simpa using hJu

theorem cubicJacobi_generates_prime (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    P = Ideal.span {jacobiSum (cubicChar P hgood) (cubicChar P hgood)} := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hnormJ : Algebra.norm ℤ J = (Nat.card (O ⧸ P) : ℤ) := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → O))
    change ((Algebra.norm ℤ J : ℤ) : O) = (Nat.card (O ⧸ P) : O)
    rw [norm_int_eq_mul_conjO]
    exact cubicJacobi_mul_conj P hgood
  have habsJ : Ideal.absNorm (Ideal.span {J}) = Nat.card (O ⧸ P) := by
    rw [Ideal.absNorm_span_singleton, hnormJ]
    simp
  have habsP : Ideal.absNorm P = Nat.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hle : Ideal.span {J} ≤ P :=
    (Ideal.span_singleton_le_iff_mem P).mpr (cubicJacobi_mem_prime P hgood)
  obtain ⟨Q, hQ⟩ := (Ideal.dvd_iff_le).mpr hle
  have hq : Nat.card (O ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hQnorm : Ideal.absNorm Q = 1 := by
    have heq : Nat.card (O ⧸ P) = Nat.card (O ⧸ P) * Ideal.absNorm Q := by
      calc
        Nat.card (O ⧸ P) = Ideal.absNorm (Ideal.span {J}) := habsJ.symm
        _ = Ideal.absNorm (P * Q) := by simp_all
        _ = Ideal.absNorm P * Ideal.absNorm Q := by simp
        _ = Nat.card (O ⧸ P) * Ideal.absNorm Q := by simp_all
    exact (mul_left_cancel₀ hq (by omega))
  have hQtop := Ideal.absNorm_eq_one_iff.mp hQnorm
  change P = Ideal.span {J}
  simp_all

theorem cubicJacobi_exists_primary_generator (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ p : O, P = Ideal.span {p} ∧ lambda ^ 2 ∣ p - 1 ∧
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  refine ⟨-J, ?_, ?_, by ring⟩
  · have h := cubicJacobi_generates_prime P hgood
    simpa using h
  · obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
    refine ⟨-z, ?_⟩
    grind

theorem cubicGauss_cube {E : Type*} [Field E] (ι : O →+* E)
    (hι : Function.Injective ι) (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
    (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 =
      -(ι p) * (Nat.card (O ⧸ P) : E) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := cubicChar P hgood
  let ξ := χ.ringHomComp ι
  have hχ3 : χ ^ 3 = 1 := cubicChar_pow_three P hgood
  have hχne : χ ≠ 1 := cubicChar_ne_one P hgood
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have hd : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [cubicChar_order P hgood] at hd
    norm_num at hd
  have hξne : ξ ≠ 1 := (MulChar.ringHomComp_ne_one_iff hι).mpr hχne
  have hξ2 : ξ * ξ ≠ 1 := by
    rw [show ξ * ξ = (χ * χ).ringHomComp ι by
      exact (MulChar.ringHomComp_mul χ χ ι).symm]
    exact (MulChar.ringHomComp_ne_one_iff hι).mpr hχ2
  have hχinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using hχ3
  have hξinv : ξ⁻¹ = ξ ^ 2 := by
    change (χ.ringHomComp ι)⁻¹ = (χ.ringHomComp ι) ^ 2
    rw [MulChar.ringHomComp_inv, MulChar.ringHomComp_pow, hχinv]
  have hξmul : ξ * ξ = ξ⁻¹ := by rw [hξinv, pow_two]
  have hχneg : χ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by grind) hχ3
  have hξneg : ξ (-1) = 1 := by
    change ι (χ (-1)) = 1
    rw [hχneg, map_one]
  have hξinvneg : ξ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hξneg, inv_one]
  have hgs : gaussSum ξ ψ * gaussSum ξ⁻¹ ψ = (Nat.card (O ⧸ P) : E) := by
    have h := gaussSum_mul_gaussSum_eq_card hξne hψ
    have hshift := mul_gaussSum_inv_eq_gaussSum ξ⁻¹ ψ
    rw [hξinvneg, one_mul] at hshift
    rw [hshift] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hJ : jacobiSum ξ ξ = -(ι p) := by
    change jacobiSum (χ.ringHomComp ι) (χ.ringHomComp ι) = -(ι p)
    rw [jacobiSum_ringHomComp]
    rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
      map_neg]
  have hgj : gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ = gaussSum ξ ψ * gaussSum ξ ψ := by
    simpa only [hξmul] using jacobiSum_mul_nontrivial hξ2 ψ
  grind

theorem primary_generator_mul_conj_eq_card (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    p * conjO p = (Nat.card (O ⧸ P) : O) := by
  have h := cubicJacobi_mul_conj P hgood
  rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
    map_neg] at h
  simp_all

theorem quadraticCharO_ne_one (P : Ideal O) [P.IsMaximal]
    (hchar : ringChar (O ⧸ P) ≠ 2) : quadraticCharO P ≠ 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  change (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O) ≠ 1
  exact (MulChar.ringHomComp_ne_one_iff
    (Int.cast_injective (α := O))).2 (quadraticChar_ne_one hchar)

theorem sexticChar_order (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (sexticChar P hgood) = 6 := by
  have h2 := (sexticChar_powers P hgood).1
  have h3 := (sexticChar_powers P hgood).2.1
  have h6 := (sexticChar_powers P hgood).2.2
  have hdiv :=
    orderOf_dvd_of_pow_eq_one h6
  have hne2 : orderOf (sexticChar P hgood) ≠ 2 := by
    intro he
    have hχ2 := pow_orderOf_eq_one (sexticChar P hgood)
    rw [he, h2] at hχ2
    exact cubicChar_ne_one P hgood hχ2
  have hne3 : orderOf (sexticChar P hgood) ≠ 3 := by
    intro he
    have hχ3 := pow_orderOf_eq_one (sexticChar P hgood)
    rw [he, h3] at hχ3
    exact quadraticCharO_ne_one P hchar hχ3
  have hne1 : orderOf (sexticChar P hgood) ≠ 1 := by
    intro he
    have hχ1 := orderOf_eq_one_iff.mp he
    rw [hχ1] at h2
    exact cubicChar_ne_one P hgood (by simp_all)
  have hne0 : orderOf (sexticChar P hgood) ≠ 0 := by
    intro he
    norm_num [he] at hdiv
  have hpos := Nat.pos_of_ne_zero hne0
  have hle := Nat.le_of_dvd (by norm_num) hdiv
  have hne4 : orderOf (sexticChar P hgood) ≠ 4 := by
    intro he
    norm_num [he] at hdiv
  have hne5 : orderOf (sexticChar P hgood) ≠ 5 := by
    intro he
    norm_num [he] at hdiv
  omega

theorem sexticChar_reduce_unit (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (u : (O ⧸ P)ˣ) :
    (Ideal.Quotient.mk P) (sexticChar P hgood (u : O ⧸ P)) =
      (u : O ⧸ P) ^ ((Nat.card (O ⧸ P) - 1) / 6) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let N := Fintype.card (O ⧸ P)
  let m := (N - 1) / 6
  have hthree : 3 ∣ N - 1 := by
    simpa only [N, Nat.card_eq_fintype_card] using card_sub_one_div_three P hgood
  have hodd : N % 2 = 1 := FiniteField.odd_card_of_char_ne_two hchar
  have hN : 1 < N := Fintype.one_lt_card
  have hsix : 6 ∣ N - 1 := by omega
  have hsize : N - 1 = 6 * m := by
    dsimp [m]
    exact by omega
  have hthird : (N - 1) / 3 = 2 * m := by omega
  have hhalf : N / 2 = 3 * m := by omega
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hquad : ρ (quadraticCharO P (u : O ⧸ P)) =
      (u : O ⧸ P) ^ (N / 2) := by
    change (quadraticChar (O ⧸ P) (u : O ⧸ P) : O ⧸ P) = _
    exact quadraticChar_eq_pow_of_char_ne_two' hchar (u : O ⧸ P)
  have hcub : ρ (cubicChar P hgood (u : O ⧸ P)) =
      (u : O ⧸ P) ^ ((N - 1) / 3) := by
    simpa only [N, Nat.card_eq_fintype_card] using cubicChar_reduce P hgood (u : O ⧸ P)
  have hfermat : (u : O ⧸ P) ^ (N - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero u)
  change ρ ((cubicChar P hgood ^ 2 * quadraticCharO P) (u : O ⧸ P)) = _
  rw [MulChar.mul_apply, MulChar.pow_apply', map_mul, map_pow, hcub, hquad]
  rw [hthird, hhalf]
  simpa only [Nat.card_eq_fintype_card, N, m] using
    (show ((u : O ⧸ P) ^ (2 * m)) ^ 2 * (u : O ⧸ P) ^ (3 * m) =
      (u : O ⧸ P) ^ m by
      calc
        ((u : O ⧸ P) ^ (2 * m)) ^ 2 * (u : O ⧸ P) ^ (3 * m) =
            (u : O ⧸ P) ^ (7 * m) := by
              ring
        _ = (u : O ⧸ P) ^ m * (u : O ⧸ P) ^ (N - 1) := by
          rw [hsize, ← pow_add]; ring
        _ = (u : O ⧸ P) ^ m := by simp_all)
  omega

theorem quotient_char_ne_two_of_two_not_mem (P : Ideal O) [P.IsMaximal]
    (h2 : (2 : O) ∉ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  intro heq
  have hz : ((ringChar (O ⧸ P) : ℕ) : O ⧸ P) = 0 := ringChar.Nat.cast_ringChar
  rw [heq] at hz
  apply h2
  exact (Ideal.Quotient.eq_zero_iff_mem).mp (by simpa)

end ActualEisensteinCubic

end

end OAI
