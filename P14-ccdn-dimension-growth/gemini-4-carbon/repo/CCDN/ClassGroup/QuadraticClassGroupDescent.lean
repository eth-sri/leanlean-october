module

public import CCDN.ClassGroup.TwoTorsion
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
import CCDN.ForMathlib.FieldTheory
import CCDN.ForMathlib.FiniteGroupPowerTorsion
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification

@[expose] public section
namespace CCDN
noncomputable section
open NumberField Ideal
open scoped NumberField Pointwise nonZeroDivisors

theorem quadratic_absolute_discriminant_square_le
    (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (hd : Module.finrank F K = 2) :
    (NumberField.discr F).natAbs ^ 2 ≤ (NumberField.discr K).natAbs := by
  rw [← hd]
  refine Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
    ⟨Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 K)), ?_⟩
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) K (𝓞 K)]
  exact Nat.mul_comm _ _

private theorem quadratic_automorphism_eq_one_or
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) (τ : K ≃ₐ[F] K) :
    τ = 1 ∨ τ = σ := by
  classical
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  have hc : Fintype.card (K ≃ₐ[F] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hd]
  by_cases hτ : τ = 1
  · exact Or.inl hτ
  · have he : (Finset.univ.erase (1 : K ≃ₐ[F] K)).card ≤ 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hc]
    exact Or.inr (Finset.card_le_one.mp he _ (by simp [hτ]) _ (by simp [hσ]))

private theorem quadratic_automorphism_involutive
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) : Function.Involutive σ := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  have hs : σ ^ 2 = 1 := by
    simpa only [IsGalois.card_aut_eq_finrank, hd] using (pow_card_eq_one' (x := σ))
  exact fun x => by
    simpa only [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] using
      congrArg (fun τ : K ≃ₐ[F] K => τ x) hs

private def fractionalIdealUnitAction {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (σ : R ≃+* R) :
    (FractionalIdeal R⁰ K)ˣ →* (FractionalIdeal R⁰ K)ˣ :=
  Units.map (FractionalIdeal.ringEquivOfRingEquiv K K σ).toMonoidHom

private lemma fractionalIdealUnitAction_principal {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (σ : R ≃+* R) (b : Kˣ) :
    fractionalIdealUnitAction (K := K) σ (toPrincipalIdeal R K b) =
      toPrincipalIdeal R K
        (Units.map (IsFractionRing.ringEquivOfRingEquiv σ : K ≃+* K).toMonoidHom b) :=
  Units.ext <| by
    simp only [fractionalIdealUnitAction, Units.coe_map, coe_toPrincipalIdeal]
    exact FractionalIdeal.ringEquivOfRingEquiv_spanSingleton K K σ b

private lemma classGroup_mk_principal {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (b : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K b) = 1 := by
  apply ClassGroup.mk_eq_one_iff.mpr
  rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(b : K), rfl⟩⟩

private theorem fractionalIdeal_conjugate_coeIdeal {R K : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (σ : R ≃+* R) (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv K K σ (I : FractionalIdeal R⁰ K) =
      (I.map σ.toRingHom : FractionalIdeal R⁰ K) := by
  let : RingHomInvPair (σ : R →+* R) σ.symm := RingHomInvPair.of_ringEquiv σ
  let : RingHomInvPair (σ.symm : R →+* R) σ := RingHomInvPair.of_ringEquiv σ.symm
  ext x
  change x ∈ Submodule.map (IsFractionRing.semilinearEquivOfRingEquiv K K σ).toLinearMap
    (I : FractionalIdeal R⁰ K).val ↔ x ∈ (I.map σ.toRingHom : FractionalIdeal R⁰ K)
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hy
    exact (FractionalIdeal.mem_coeIdeal R⁰).mpr
      ⟨σ r, Ideal.mem_map_of_mem _ hr, (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ r).symm⟩
  · intro hx
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hx
    obtain ⟨s, hs, rfl⟩ := (Ideal.mem_map_iff_of_surjective σ.toRingHom σ.surjective).mp hr
    exact ⟨algebraMap R K s, (FractionalIdeal.mem_coeIdeal R⁰).mpr ⟨s, hs, rfl⟩,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap σ s⟩

private def stronglyAmbiguousClassGroup (F K : Type*) [Field F] [Field K] [NumberField K]
    [Algebra F K] (σ : K ≃ₐ[F] K) : Subgroup (ClassGroup (𝓞 K)) :=
  ((ClassGroup.mk K).comp
    ((fractionalIdealUnitAction (K := K)
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv).eqLocus (MonoidHom.id _)).subtype).range

private abbrev stronglyAmbiguousTwoTorsion (F K : Type*) [Field F] [Field K] [NumberField K]
    [Algebra F K] (σ : K ≃ₐ[F] K) :=
  (powMonoidHom 2 : stronglyAmbiguousClassGroup F K σ →*
    stronglyAmbiguousClassGroup F K σ).ker

private theorem classGroupTwoTorsionCard_le_stronglyAmbiguous
    (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) :
    classGroupTwoTorsionCard K ≤
      (Nat.card (stronglyAmbiguousTwoTorsion F K σ) * 2 ^ Module.finrank ℚ F) ^ 2 := by
  classical
  have hσ_inv := quadratic_automorphism_involutive hd σ
  have hσO : Function.Involutive (RingOfIntegers.mapAlgEquiv σ).toRingEquiv :=
    fun x => RingOfIntegers.ext (hσ_inv x)
  let σO := (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
  let act : classGroupTwoTorsion K →* classGroupTwoTorsion K :=
    { toFun := fun c => ⟨ClassGroup.mulEquiv σO c, by
        change (ClassGroup.mulEquiv σO c.val) ^ 2 = 1
        rw [← map_pow, show c.val ^ 2 = 1 from c.property, map_one]⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  have hact_inv : Function.Involutive act := fun c => Subtype.ext <| by
    change ClassGroup.map (σO : 𝓞 K →+* 𝓞 K) (show Function.Injective (σO : 𝓞 K →+* 𝓞 K) from σO.injective)
      (ClassGroup.map (σO : 𝓞 K →+* 𝓞 K) (show Function.Injective (σO : 𝓞 K →+* 𝓞 K) from σO.injective) c.val) = c.val
    rw [ClassGroup.map_map]
    have hh : (σO : 𝓞 K →+* 𝓞 K).comp (σO : 𝓞 K →+* 𝓞 K) = RingHom.id (𝓞 K) := RingHom.ext hσO
    simpa only [hh] using ClassGroup.map_id c.val
  let Fix := act.eqLocus (MonoidHom.id _)
  have hinv_sq : classGroupTwoTorsionCard K ≤ Nat.card Fix ^ 2 := by
    let τ : classGroupTwoTorsion K →* classGroupTwoTorsion K := (MonoidHom.id _) * act
    have hker : τ.ker ≤ Fix := fun x hx => by
      change x * act x = 1 at hx; change act x = x
      have hx2 : x ^ 2 = 1 := Subtype.ext x.property
      exact mul_left_cancel (a := x) (hx.trans (by simpa only [pow_two] using hx2.symm))
    have hrange : τ.range ≤ Fix := by
      rintro _ ⟨y, rfl⟩; change act (y * act y) = y * act y; rw [map_mul, hact_inv, mul_comm]
    calc classGroupTwoTorsionCard K = Nat.card τ.ker * Nat.card τ.range :=
          (Subgroup.card_ker_mul_card_range τ).symm
      _ ≤ Nat.card Fix * Nat.card Fix := Nat.mul_le_mul
          (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hker))
          (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hrange))
      _ = Nat.card Fix ^ 2 := (pow_two _).symm
  let relNorm : (𝓞 K)ˣ →* (𝓞 F)ˣ := Units.map (RingOfIntegers.norm F)
  let Q_u := (𝓞 F)ˣ ⧸ relNorm.range
  have hQu_sq (x : Q_u) : x ^ 2 = 1 := QuotientGroup.induction_on x fun u => by
    rw [← QuotientGroup.mk_pow]
    refine (QuotientGroup.eq_one_iff _).mpr ⟨Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom u, ?_⟩
    apply Units.ext
    change RingOfIntegers.norm F (algebraMap (𝓞 F) (𝓞 K) (u : 𝓞 F)) = (u : 𝓞 F) ^ 2
    simpa only [hd] using RingOfIntegers.norm_algebraMap (L := K) F (u : 𝓞 F)
  obtain ⟨ζ, hζ⟩ := exists_zpow_surjective (NumberField.Units.torsion F)
  let par (e : ℤ) : Fin 2 := ⟨(e % 2).toNat, by omega⟩
  have hzpow (x : Q_u) (e : ℤ) : x ^ e = x ^ (par e).val := by
    rw [zpow_eq_zpow_emod' e (hQu_sq x), ← zpow_natCast]
    congr 1; exact (Int.toNat_of_nonneg (Int.emod_nonneg e (by norm_num))).symm
  let φ_q : (𝓞 F)ˣ →* Q_u := QuotientGroup.mk' relNorm.range
  let code : Fin 2 × (Fin (NumberField.Units.rank F) → Fin 2) → Q_u := fun e =>
    φ_q (ζ : (𝓞 F)ˣ) ^ e.1.val * ∏ i, φ_q (NumberField.Units.fundSystem F i) ^ (e.2 i).val
  have hcode : Function.Surjective code := fun y => by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨⟨η, e⟩, hu, _⟩ := NumberField.Units.exist_unique_eq_mul_prod F u
    obtain ⟨k, hk⟩ := hζ η
    refine ⟨(par k, fun i => par (e i)), ?_⟩
    change φ_q (ζ : (𝓞 F)ˣ) ^ (par k).val *
      ∏ i, φ_q (NumberField.Units.fundSystem F i) ^ (par (e i)).val = φ_q u
    rw [hu, map_mul, map_prod]; congr 1
    · rw [← hk, Subgroup.coe_zpow, map_zpow]; exact (hzpow _ k).symm
    · exact Finset.prod_congr rfl fun i _ => by rw [map_zpow]; exact (hzpow _ (e i)).symm
  let : Finite Q_u := Finite.of_surjective code hcode
  have hQu_card : Nat.card Q_u ≤ 2 ^ Module.finrank ℚ F := by
    have hc : Nat.card Q_u ≤ 2 ^ (NumberField.Units.rank F + 1) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        pow_succ, mul_comm] using Nat.card_le_card_of_surjective code hcode
    have hrk : NumberField.Units.rank F + 1 ≤ Module.finrank ℚ F := by
      have := Fintype.card_pos (α := InfinitePlace F)
      have := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
      have := InfinitePlace.card_add_two_mul_card_eq_rank (K := F)
      unfold NumberField.Units.rank; omega
    exact hc.trans (Nat.pow_le_pow_right (by norm_num) hrk)
  have hwit (c : Fix) : ∃ (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : Kˣ) (u : (𝓞 F)ˣ),
      ClassGroup.mk K J = c.val.val ∧
      fractionalIdealUnitAction (K := K) (RingOfIntegers.mapAlgEquiv σ).toRingEquiv J =
        toPrincipalIdeal (𝓞 K) K s * J ∧
      Algebra.norm F (s : K) = ((u : 𝓞 F) : F) := by
    have hc_fix : ClassGroup.mulEquiv (RingOfIntegers.mapAlgEquiv σ).toRingEquiv c.val.val =
        c.val.val := Subtype.ext_iff.mp c.property
    obtain ⟨I, hIc⟩ := ClassGroup.mk0_surjective c.val.val
    rw [← hIc, ClassGroup.mulEquiv_mk0] at hc_fix
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hc_fix
    change Ideal.span {x} * (I : Ideal (𝓞 K)).map (RingOfIntegers.mapAlgEquiv σ).toRingHom =
      Ideal.span {y} * (I : Ideal (𝓞 K)) at hxy
    have hn := congrArg (Ideal.relNorm (𝓞 F)) hxy
    simp only [map_mul, Ideal.relNorm_singleton] at hn
    have hnmap : Ideal.relNorm (𝓞 F) ((I : Ideal (𝓞 K)).map (RingOfIntegers.mapAlgEquiv σ).toRingHom) =
        Ideal.relNorm (𝓞 F) (I : Ideal (𝓞 K)) :=
      Ideal.relNorm_map_algEquiv (RingOfIntegers.mapAlgEquiv σ) I
    rw [hnmap] at hn
    have hnI : Ideal.relNorm (𝓞 F) (I : Ideal (𝓞 K)) ≠ 0 := fun h =>
      (mem_nonZeroDivisors_iff_ne_zero.mp I.property) (Ideal.relNorm_eq_bot_iff.mp h)
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (mul_right_cancel₀ hnI hn)
    let a : Kˣ := Units.mk0 (x : K) (RingOfIntegers.coe_ne_zero_iff.mpr hx)
    let b : Kˣ := Units.mk0 (y : K) (RingOfIntegers.coe_ne_zero_iff.mpr hy)
    have hcomp : toPrincipalIdeal (𝓞 K) K a *
        fractionalIdealUnitAction (K := K) σO (FractionalIdeal.mk0 K I) =
        toPrincipalIdeal (𝓞 K) K b * FractionalIdeal.mk0 K I := Units.ext <| by
      have hh := congrArg (fun M : Ideal (𝓞 K) => (M : FractionalIdeal (𝓞 K)⁰ K)) hxy
      simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] at hh
      simp only [Units.val_mul, coe_toPrincipalIdeal, fractionalIdealUnitAction,
        Units.coe_map, FractionalIdeal.coe_mk0]
      change FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) *
          FractionalIdeal.ringEquivOfRingEquiv K K σO (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K) * (I : FractionalIdeal (𝓞 K)⁰ K)
      rwa [fractionalIdeal_conjugate_coeIdeal]
    have hsc : fractionalIdealUnitAction (K := K) (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
        (FractionalIdeal.mk0 K I) = toPrincipalIdeal (𝓞 K) K (b / a) * FractionalIdeal.mk0 K I := by
      apply mul_left_cancel (a := toPrincipalIdeal (𝓞 K) K a)
      rw [hcomp, map_div, ← mul_assoc, mul_div_cancel]
    have hnorm : Algebra.norm F ((b / a : Kˣ) : K) = ((u : 𝓞 F) : F) := by
      have hnF := congrArg (algebraMap (𝓞 F) F) hu
      rw [map_mul, Algebra.algebraMap_intNorm (K := F) (L := K),
        Algebra.algebraMap_intNorm (K := F) (L := K)] at hnF
      simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, Algebra.norm_inv]
      change Algebra.norm F (y : K) * (Algebra.norm F (x : K))⁻¹ = _
      rw [← div_eq_mul_inv, div_eq_iff (Algebra.norm_ne_zero_iff.mpr (mod_cast hx))]
      exact hnF.symm.trans (mul_comm _ _)
    exact ⟨FractionalIdeal.mk0 K I, b / a, u, (ClassGroup.mk_mk0 K I).trans hIc, hsc, hnorm⟩
  choose wJ ws wu hw_cls hw_sc hw_nm using hwit
  let obs : Fix → Q_u := fun c => QuotientGroup.mk (wu c)
  let emb : Fix →* ClassGroup (𝓞 K) := (classGroupTwoTorsion K).subtype.comp Fix.subtype
  let S_sub := (stronglyAmbiguousClassGroup F K σ).comap emb
  have hobs (c e : Fix) (hce : obs c = obs e) : c / e ∈ S_sub := by
    change c.val.val / e.val.val ∈ stronglyAmbiguousClassGroup F K σ
    rw [← hw_cls c, ← hw_cls e, ← map_div]
    obtain ⟨v_u, hv_u⟩ : wu c / wu e ∈ relNorm.range :=
      (QuotientGroup.eq_one_iff _).mp (by
        rw [QuotientGroup.mk_div]; change obs c / obs e = 1; rw [hce, div_self'])
    let eu : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom v_u
    have hprin_eu : toPrincipalIdeal (𝓞 K) K eu = 1 := Units.ext <| by
      simp only [coe_toPrincipalIdeal, Units.val_one]
      change FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K (v_u : 𝓞 K)) = 1
      rw [← FractionalIdeal.coeIdeal_span_singleton (S := (𝓞 K)⁰) (P := K)]
      simp only [Ideal.span_singleton_eq_top.mpr v_u.isUnit, FractionalIdeal.coeIdeal_top]
    let d_sc := (ws c / ws e) / eu
    have hquot : fractionalIdealUnitAction (K := K) (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
        (wJ c / wJ e) = toPrincipalIdeal (𝓞 K) K d_sc * (wJ c / wJ e) := by
      dsimp [d_sc]
      rw [map_div, hw_sc c, hw_sc e, map_div (toPrincipalIdeal (𝓞 K) K), hprin_eu, div_one,
        map_div (toPrincipalIdeal (𝓞 K) K)]
      exact mul_div_mul_comm _ _ _ _
    have hnm1 : Algebra.norm F (d_sc : K) = 1 := by
      have hh1 := congrArg (Units.map (algebraMap (𝓞 F) F).toMonoidHom) hv_u
      rw [map_div] at hh1
      have hh := congrArg (fun z : Fˣ => (z : F)) hh1
      simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hh
      change Algebra.norm F ((v_u : 𝓞 K) : K) = ((wu c : 𝓞 F) : F) * (((wu e : 𝓞 F) : F))⁻¹ at hh
      dsimp [d_sc]
      simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, Algebra.norm_inv]
      change Algebra.norm F (ws c : K) * (Algebra.norm F (ws e : K))⁻¹ *
        (Algebra.norm F ((v_u : 𝓞 K) : K))⁻¹ = 1
      rw [hw_nm c, hw_nm e, hh, mul_inv_cancel₀]
      exact hh ▸ Algebra.norm_ne_zero_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr v_u.ne_zero)
    have hmul_conj : (d_sc : K) * σ (d_sc : K) = 1 := by
      let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
      have hprod := Algebra.norm_eq_prod_automorphisms F (d_sc : K)
      have hp := Fintype.prod_eq_mul (f := fun τ : K ≃ₐ[F] K => τ (d_sc : K)) 1 σ hσ.symm
        fun τ hτ => False.elim ((quadratic_automorphism_eq_one_or hd σ hσ τ).elim hτ.1 hτ.2)
      calc (d_sc : K) * σ (d_sc : K) = (1 : K ≃ₐ[F] K) (d_sc : K) * σ (d_sc : K) := by
            rw [AlgEquiv.one_apply]
        _ = 1 := by rw [← hp, ← hprod, hnm1, map_one]
    have hfrac_aut : (IsFractionRing.ringEquivOfRingEquiv
        (RingOfIntegers.mapAlgEquiv σ).toRingEquiv : K ≃+* K) = σ.toRingEquiv := by
      have hh : (IsFractionRing.ringEquivOfRingEquiv
          (RingOfIntegers.mapAlgEquiv σ).toRingEquiv : K ≃+* K).toRingHom = σ.toRingHom :=
        IsFractionRing.ringHom_ext (A := 𝓞 K) fun x =>
          IsFractionRing.ringEquivOfRingEquiv_algebraMap
            (RingOfIntegers.mapAlgEquiv σ).toRingEquiv x
      exact RingEquiv.ext (RingHom.congr_fun hh)
    have hcompat (b : Kˣ) : fractionalIdealUnitAction (K := K)
        (RingOfIntegers.mapAlgEquiv σ).toRingEquiv (toPrincipalIdeal (𝓞 K) K b) =
        toPrincipalIdeal (𝓞 K) K (Units.map σ.toRingEquiv.toMonoidHom b) := by
      rw [fractionalIdealUnitAction_principal, hfrac_aut]
    have hσne : σ.toRingEquiv ≠ RingEquiv.refl K := fun h =>
      hσ (AlgEquiv.ext (RingEquiv.congr_fun h))
    obtain ⟨b, hb⟩ := RingEquiv.exists_invariant_of_involutive σ.toRingEquiv hσ_inv hσne
      (fractionalIdealUnitAction (K := K) (RingOfIntegers.mapAlgEquiv σ).toRingEquiv)
      (toPrincipalIdeal (𝓞 K) K) hcompat (wJ c / wJ e) d_sc hquot hmul_conj
    exact ⟨⟨toPrincipalIdeal (𝓞 K) K b * (wJ c / wJ e), hb⟩,
      by dsimp; rw [map_mul, classGroup_mk_principal, one_mul]⟩
  let rep : Fix ⧸ S_sub → Fix := fun q => Classical.choose (QuotientGroup.mk_surjective q)
  have hrep (q : Fix ⧸ S_sub) : QuotientGroup.mk (rep q) = q :=
    Classical.choose_spec (QuotientGroup.mk_surjective q)
  have hinj_q : Function.Injective (fun q : Fix ⧸ S_sub => obs (rep q)) := fun x y h => by
    rw [← hrep x, ← hrep y]; apply div_eq_one.mp; rw [← QuotientGroup.mk_div]
    exact (QuotientGroup.eq_one_iff _).mpr (hobs _ _ h)
  let incl : S_sub → stronglyAmbiguousTwoTorsion F K σ := fun c =>
    ⟨⟨c.val.val.val, c.property⟩, Subtype.ext c.val.val.property⟩
  have hincl : Function.Injective incl := fun c e h =>
    Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun x : stronglyAmbiguousTwoTorsion F K σ => x.val.val) h)))
  have hFix_le : Nat.card Fix ≤
      Nat.card (stronglyAmbiguousTwoTorsion F K σ) * 2 ^ Module.finrank ℚ F := calc
    Nat.card Fix = Nat.card S_sub * S_sub.index := S_sub.card_mul_index.symm
    _ ≤ Nat.card (stronglyAmbiguousTwoTorsion F K σ) * Nat.card Q_u :=
      Nat.mul_le_mul (Nat.card_le_card_of_injective incl hincl)
        (Nat.card_le_card_of_injective _ hinj_q)
    _ ≤ Nat.card (stronglyAmbiguousTwoTorsion F K σ) * 2 ^ Module.finrank ℚ F :=
      Nat.mul_le_mul_left _ hQu_card
  exact hinv_sq.trans (Nat.pow_le_pow_left hFix_le 2)

private def IsQuadraticRamifiedPrime (F K : Type*) [Field F] [Field K] [NumberField F]
    [NumberField K] [Algebra F K] (Q : Ideal (𝓞 K)) : Prop :=
  Q.IsPrime ∧ Q ≠ ⊥ ∧ Q.ramificationIdx (𝓞 F) = 2

private theorem invariant_integral_ideal_ramified_factorization
    (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (hinv : σ • I = I) :
    ∃ (J : Ideal (𝓞 F)) (t : Finset (Ideal (𝓞 K))),
      J ≠ 0 ∧ (∀ Q ∈ t, IsQuadraticRamifiedPrime F K Q) ∧
        I = J.map (algebraMap (𝓞 F) (𝓞 K)) * ∏ Q ∈ t, Q := by
  classical
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  let : IsGaloisGroup (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) := IsGaloisGroup.of_isFractionRing _ _ _ F K
  have horbit (Q : Ideal (𝓞 K)) [Q.IsPrime] :
      (Q.under (𝓞 F)).primesOver (𝓞 K) = {Q, σ • Q} := by
    ext P; constructor
    · intro hP
      have : P.IsPrime := hP.1; have : P.LiesOver (Q.under (𝓞 F)) := hP.2
      obtain ⟨τ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Q.under (𝓞 F)) Q P (K ≃ₐ[F] K)
      rcases quadratic_automorphism_eq_one_or hd σ hσ τ with rfl | rfl <;> simp
    · intro hP
      rcases Set.mem_insert_iff.mp hP with rfl | hP
      · exact ⟨inferInstance, inferInstance⟩
      · rw [Set.mem_singleton_iff.mp hP]; exact ⟨inferInstance, inferInstance⟩
  have hram_id (Q : Ideal (𝓞 K)) [Q.IsPrime] :
      ((Q.under (𝓞 F)).primesOver (𝓞 K)).ncard *
        (Q.ramificationIdx (𝓞 F) * Q.inertiaDeg (𝓞 F)) = 2 := by
    have hh := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (Q.under (𝓞 F)) (𝓞 K) (K ≃ₐ[F] K)
    rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 F)) Q (K ≃ₐ[F] K),
      Ideal.inertiaDegIn_eq_inertiaDeg (Q.under (𝓞 F)) Q (K ≃ₐ[F] K),
      IsGalois.card_aut_eq_finrank, hd] at hh
  have hmove_unram (Q : Ideal (𝓞 K)) [Q.IsPrime] (hm : σ • Q ≠ Q) :
      Q.ramificationIdx (𝓞 F) = 1 := by
    have hh := hram_id Q
    rw [horbit Q, show ({Q, σ • Q} : Set (Ideal (𝓞 K))).ncard = 2 by simp [hm.symm]] at hh
    have := Q.ramificationIdx_pos (𝓞 F); have := Q.inertiaDeg_pos (𝓞 F); nlinarith
  have hfix_ext (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ0 : Q ≠ ⊥) (hf : σ • Q = Q) :
      (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 K)) = Q ^ Q.ramificationIdx (𝓞 F) := by
    have hp : Q.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hQ0
    have : (Q.under (𝓞 F)).IsMaximal := (inferInstance : (Q.under (𝓞 F)).IsPrime).isMaximal hp
    have hset : ((Q.under (𝓞 F)).primesOver (𝓞 K)).toFinset = {Q} := by
      ext P; simp [horbit Q, hf]
    rw [Ideal.map_algebraMap_eq_finsetProd_pow hp, hset]; simp
  have hrem {I₀ A R : Ideal (𝓞 K)} (hI0 : σ • I₀ = I₀) (hA : σ • A = A) (hA0 : A ≠ 0)
      (he : I₀ = A * R) : σ • R = R :=
    mul_left_cancel₀ hA0 (calc A * (σ • R) = σ • (A * R) := by rw [smul_mul', hA]
      _ = A * R := by rw [← he, hI0, he])
  suffices ∀ I₀ : Ideal (𝓞 K), I₀ ≠ 0 → σ • I₀ = I₀ →
      ∃ (J : Ideal (𝓞 F)) (t : Finset (Ideal (𝓞 K))),
        J ≠ 0 ∧ (∀ Q ∈ t, IsQuadraticRamifiedPrime F K Q) ∧
          I₀ = J.map (algebraMap (𝓞 F) (𝓞 K)) * ∏ Q ∈ t, Q from this I hI hinv
  intro I₀
  induction I₀ using (wellFounded_dvdNotUnit (α := Ideal (𝓞 K))).induction with
  | h I₀ ih =>
    intro hI0 hinv0
    by_cases hu : IsUnit I₀
    · refine ⟨1, ∅, one_ne_zero, by simp, ?_⟩
      rw [show I₀ = 1 by simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp hu,
        Finset.prod_empty, mul_one]
      simpa only [Ideal.one_eq_top] using (Ideal.map_top (algebraMap (𝓞 F) (𝓞 K))).symm
    obtain ⟨Q, hQir, R, hR⟩ := WfDvdMonoid.exists_irreducible_factor hu hI0
    have hQprime : Prime Q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hQir
    have : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    have hQ0 : Q ≠ 0 := hQprime.ne_zero
    have hp0 : Q.under (𝓞 F) ≠ 0 := Ideal.under_ne_bot (𝓞 F) hQ0
    by_cases hfix : σ • Q = Q
    · have hR0 : R ≠ 0 := fun hz => hI0 (by simp [hz] at hR; exact hR)
      obtain ⟨J, t, hJ, ht, hJt⟩ := ih R
        ⟨hR0, Q, hQir.not_isUnit, by simpa [mul_comm] using hR⟩ hR0 (hrem hinv0 hfix hQ0 hR)
      have hdvd2 : Q.ramificationIdx (𝓞 F) ∣ 2 :=
        ⟨((Q.under (𝓞 F)).primesOver (𝓞 K)).ncard * Q.inertiaDeg (𝓞 F),
          by have hh := hram_id Q; nlinarith only [hh]⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with he | he
      · have hmap := hfix_ext Q hQ0 hfix
        rw [he, pow_one] at hmap
        exact ⟨Q.under (𝓞 F) * J, t, mul_ne_zero hp0 hJ, ht,
          by rw [Ideal.map_mul, hmap, hR, hJt]; ac_rfl⟩
      · by_cases hQt : Q ∈ t
        · have hsq : Q ^ 2 = (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 K)) := by
            have hmap := hfix_ext Q hQ0 hfix; rwa [he, eq_comm] at hmap
          refine ⟨Q.under (𝓞 F) * J, t.erase Q, mul_ne_zero hp0 hJ,
            fun P hP => ht P (Finset.mem_of_mem_erase hP), ?_⟩
          have hpr := Finset.mul_prod_erase t (fun P => P) hQt
          rw [hR, hJt, Ideal.map_mul, ← hsq, ← hpr, pow_two]; ac_rfl
        · refine ⟨J, insert Q t, hJ, fun P hP => ?_, ?_⟩
          · exact (Finset.mem_insert.mp hP).elim (fun h => h ▸ ⟨inferInstance, hQ0, he⟩) (ht P)
          · rw [hR, hJt, Finset.prod_insert hQt]; ac_rfl
    · have hσQprime : Prime (σ • Q) := Ideal.prime_of_isPrime (fun hz => hQ0 <| by
        simpa only [inv_smul_smul, show (⊥ : Ideal (𝓞 K)) = 0 from rfl, smul_zero] using
          congrArg (fun A : Ideal (𝓞 K) => σ⁻¹ • A) hz) inferInstance
      have hσQdiv : σ • Q ∣ I₀ := ⟨σ • R, by rw [← smul_mul', ← hR, hinv0]⟩
      have hσQnot : ¬ σ • Q ∣ Q := fun hh =>
        hfix (associated_iff_eq.mp ((Prime.dvd_prime_iff_associated hσQprime hQprime).mp hh))
      obtain ⟨T, hT⟩ : σ • Q ∣ R := (hσQprime.dvd_mul.mp (hR ▸ hσQdiv)).resolve_left hσQnot
      have hIeq : I₀ = (Q * (σ • Q)) * T := by rw [hR, hT]; ac_rfl
      have hA0 : Q * (σ • Q) ≠ 0 := mul_ne_zero hQ0 hσQprime.ne_zero
      have hT0 : T ≠ 0 := fun hz => hI0 (by simp [hz] at hIeq; exact hIeq)
      have hσσ : σ * σ = 1 := AlgEquiv.ext (quadratic_automorphism_involutive hd σ)
      have hAinv : σ • (Q * (σ • Q)) = Q * (σ • Q) := by
        rw [smul_mul', ← mul_smul, hσσ, one_smul, mul_comm]
      obtain ⟨J, t, hJ, ht, hJt⟩ := ih T
        ⟨hT0, Q * (σ • Q), fun hu' => hQir.not_isUnit (isUnit_of_mul_isUnit_left hu'),
          by simpa [mul_comm] using hIeq⟩ hT0 (hrem hinv0 hAinv hA0 hIeq)
      have hmv_ext : (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 K)) = Q * (σ • Q) := by
        have : (Q.under (𝓞 F)).IsMaximal := (inferInstance : (Q.under (𝓞 F)).IsPrime).isMaximal hp0
        have he := hmove_unram Q hfix
        have he' : (σ • Q).ramificationIdx (𝓞 F) = 1 := by rw [Ideal.ramificationIdx_smul, he]
        have hset : ((Q.under (𝓞 F)).primesOver (𝓞 K)).toFinset = {Q, σ • Q} := by
          ext P; simp [horbit Q]
        rw [Ideal.map_algebraMap_eq_finsetProd_pow hp0, hset]
        simp [Ne.symm hfix, he, he']
      exact ⟨Q.under (𝓞 F) * J, t, mul_ne_zero hp0 hJ, ht,
        by rw [Ideal.map_mul, hmv_ext, hIeq, hJt]; ac_rfl⟩

theorem quadratic_classGroupTwoTorsion_descent
    (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
    [Algebra F K] (hd : Module.finrank F K = 2) :
    classGroupTwoTorsionCard K ≤
      (classGroupTwoTorsionCard F *
        2 ^ (Module.finrank ℚ K * (NumberField.discr K).natAbs.primeFactors.card +
          Module.finrank ℚ F)) ^ 2 := by
  classical
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  have : Nontrivial (K ≃ₐ[F] K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [IsGalois.card_aut_eq_finrank, hd]; omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : K ≃ₐ[F] K)
  let fib (p : ℕ) : Finset (Ideal (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) (Ideal.span {(p : ℤ)})).toFinset
  have hfib_card (p : ℕ) (hp : p.Prime) : (fib p).card ≤ Module.finrank ℚ K := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    let P : Ideal ℤ := Ideal.span {(p : ℤ)}
    have : P.IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).mpr hpz
    let : Fintype (P.primesOver (𝓞 K)) :=
      (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) P).fintype
    have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 K)
    rw [RingOfIntegers.rank] at hsum
    rw [show (fib p).card = Fintype.card (P.primesOver (𝓞 K)) from Set.Finite.card_toFinset _, ← hsum]
    calc Fintype.card (P.primesOver (𝓞 K)) = ∑ _Q : P.primesOver (𝓞 K), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun Q _ => by
        have : Q.val.IsPrime := Q.property.1
        exact Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_pos (Q.val.ramificationIdx_pos ℤ) (Q.val.inertiaDeg_pos ℤ)).ne'
  let S_cov := (NumberField.discr K).natAbs.primeFactors.biUnion fib
  have hS_card : S_cov.card ≤
      Module.finrank ℚ K * (NumberField.discr K).natAbs.primeFactors.card :=
    Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum fun p hp => hfib_card p (Nat.prime_of_mem_primeFactors hp)).trans_eq
        (by simp [Nat.mul_comm]))
  have hS_mem (Q : Ideal (𝓞 K)) (hQ : IsQuadraticRamifiedPrime F K Q) : Q ∈ S_cov := by
    have : Q.IsPrime := hQ.1
    have : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ.2.1
    obtain ⟨p, _, _, hpQ, hp, _⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hdiv : (p : ℤ) ∣ NumberField.discr K := by
      by_contra h
      have : Algebra.IsUnramifiedAt ℤ Q :=
        (NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) hpz).mp h Q inferInstance
          (by simpa only [Int.cast_natCast] using hpQ)
      have habs : Q.ramificationIdx ℤ = 1 := Q.ramificationIdx_eq_one ℤ
      have hdvd := Ideal.ramificationIdx_above_dvd (R := ℤ) (Q.under (𝓞 F)) Q
      rw [hQ.2.2, habs] at hdvd; norm_num at hdvd
    have hpf : p ∈ (NumberField.discr K).natAbs.primeFactors :=
      Nat.Prime.mem_primeFactors hp
        (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdiv)
        (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K))
    exact Finset.mem_biUnion.mpr ⟨p, hpf, (Set.Finite.mem_toFinset _).mpr ⟨inferInstance,
      (Ideal.liesOver_span_iff (inferInstance : Q.IsPrime).ne_top hpz).mpr
        (by simpa only [map_natCast] using hpQ)⟩⟩
  let S₀ : Finset (Ideal (𝓞 K))⁰ :=
    (S_cov.filter fun x => x ≠ 0).attach.image fun Q =>
      ⟨Q.1, mem_nonZeroDivisors_iff_ne_zero.mpr
        (Finset.mem_filter (p := fun x => x ≠ 0).mp Q.2).2⟩
  have hS₀_card : S₀.card ≤ S_cov.card :=
    Finset.card_image_le.trans (Finset.card_attach.trans_le (Finset.card_filter_le _ _))
  have hcover (c : stronglyAmbiguousClassGroup F K σ) :
      ∃ a : ClassGroup (𝓞 F), ∃ t₀ : S₀.powerset,
        c.val = ClassGroup.extendedHom (𝓞 F) (𝓞 K) a *
          ClassGroup.mk0 (∏ Q ∈ t₀.val, Q) := by
    obtain ⟨J₀, hJc⟩ := c.property
    let J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := J₀.val
    have hJ : fractionalIdealUnitAction (K := K)
        (RingOfIntegers.mapAlgEquiv σ).toRingEquiv J = J := J₀.property
    have hσO : Function.Involutive (RingOfIntegers.mapAlgEquiv σ).toRingEquiv :=
      fun x => RingOfIntegers.ext (quadratic_automorphism_involutive hd σ (x : K))
    let σO := (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
    let d_den : 𝓞 K := (J : FractionalIdeal (𝓞 K)⁰ K).den
    have hd_ne : d_den ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp (J : FractionalIdeal (𝓞 K)⁰ K).den.property
    have hσd_ne : σO d_den ≠ 0 := by simpa only [map_zero] using σO.injective.ne hd_ne
    let u_den : Kˣ := Units.mk0 (algebraMap (𝓞 K) K (σO d_den * d_den))
      (by simpa only [map_zero] using (IsFractionRing.injective (𝓞 K) K).ne (mul_ne_zero hσd_ne hd_ne))
    let I : Ideal (𝓞 K) := Ideal.span {σO d_den} * (J : FractionalIdeal (𝓞 K)⁰ K).num
    have hI_coe : (I : FractionalIdeal (𝓞 K)⁰ K) =
        (toPrincipalIdeal (𝓞 K) K u_den * J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
      simp only [I, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton,
        Units.val_mul, coe_toPrincipalIdeal]
      rw [← (J : FractionalIdeal (𝓞 K)⁰ K).den_mul_self_eq_num']
      change FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K (σO d_den)) *
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K d_den) * (J : FractionalIdeal (𝓞 K)⁰ K)) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K (σO d_den * d_den)) *
          (J : FractionalIdeal (𝓞 K)⁰ K)
      rw [map_mul, map_mul, mul_assoc]
    have hI0 : I ≠ 0 := fun hh => (toPrincipalIdeal (𝓞 K) K u_den * J).ne_zero
      (hI_coe.symm.trans (by rw [hh]; exact FractionalIdeal.coeIdeal_bot))
    let I₀ : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩
    have hIu : FractionalIdeal.mk0 K I₀ = toPrincipalIdeal (𝓞 K) K u_den * J := Units.ext hI_coe
    have hσu : Units.map (IsFractionRing.ringEquivOfRingEquiv σO : K ≃+* K).toMonoidHom u_den =
        u_den := Units.ext <| by
      change (IsFractionRing.ringEquivOfRingEquiv σO : K ≃+* K)
        (algebraMap (𝓞 K) K (σO d_den * d_den)) = (u_den : K)
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, map_mul, hσO, mul_comm]; rfl
    have hIfix : fractionalIdealUnitAction (K := K) σO (FractionalIdeal.mk0 K I₀) =
        FractionalIdeal.mk0 K I₀ := by
      rw [hIu, map_mul, fractionalIdealUnitAction_principal, hσu, hJ]
    have hI_inv : σ • I = I := by
      change I.map σO.toRingHom = I
      apply FractionalIdeal.coeIdeal_inj (K := K) |>.mp
      have hh := congrArg (fun U : (FractionalIdeal (𝓞 K)⁰ K)ˣ => (U : FractionalIdeal (𝓞 K)⁰ K)) hIfix
      simp only [fractionalIdealUnitAction, Units.coe_map, FractionalIdeal.coe_mk0] at hh
      change FractionalIdeal.ringEquivOfRingEquiv K K σO (I : FractionalIdeal (𝓞 K)⁰ K) =
        (I : FractionalIdeal (𝓞 K)⁰ K) at hh
      simpa only [fractionalIdeal_conjugate_coeIdeal] using hh
    have hc_eq : ClassGroup.mk0 I₀ = c.val := by
      rw [← ClassGroup.mk_mk0 K I₀, hIu, map_mul, classGroup_mk_principal, one_mul]
      exact hJc
    obtain ⟨A, t, hA, ht, hfact⟩ :=
      invariant_integral_ideal_ramified_factorization F K hd σ hσ I hI0 hI_inv
    let toS₀ (Q : {Q // Q ∈ t}) : (Ideal (𝓞 K))⁰ :=
      ⟨Q.1, mem_nonZeroDivisors_iff_ne_zero.mpr (ht Q.1 Q.2).2.1⟩
    let t₀ : Finset (Ideal (𝓞 K))⁰ := t.attach.image toS₀
    have ht₀S : t₀ ⊆ S₀ := by
      intro x hx
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hx
      have hQS : Q.1 ∈ S_cov.filter fun x => x ≠ 0 :=
        Finset.mem_filter.mpr ⟨hS_mem Q.1 (ht Q.1 Q.2), (ht Q.1 Q.2).2.1⟩
      exact Finset.mem_image.mpr ⟨⟨Q.1, hQS⟩, Finset.mem_attach _ _, rfl⟩
    let A₀ : (Ideal (𝓞 F))⁰ := ⟨A, mem_nonZeroDivisors_iff_ne_zero.mpr hA⟩
    have hmap0 : A.map (algebraMap (𝓞 F) (𝓞 K)) ≠ 0 := Ideal.map_ne_bot_of_ne_bot hA
    let M₀ : (Ideal (𝓞 K))⁰ := ⟨A.map (algebraMap (𝓞 F) (𝓞 K)), mem_nonZeroDivisors_iff_ne_zero.mpr hmap0⟩
    have hI₀_eq : I₀ = M₀ * ∏ Q ∈ t₀, Q := Subtype.ext <| by
      change I = A.map (algebraMap (𝓞 F) (𝓞 K)) * ((∏ Q ∈ t₀, Q : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      rw [SubmonoidClass.coe_finsetProd]; dsimp only [t₀]
      rw [Finset.prod_image (fun a _ b _ (h : toS₀ a = toS₀ b) =>
        Subtype.ext (congrArg (fun x : (Ideal (𝓞 K))⁰ => x.1) h))]
      simpa only [toS₀, Finset.prod_attach t (fun Q => Q)] using hfact
    refine ⟨ClassGroup.mk0 A₀, ⟨t₀, Finset.mem_powerset.mpr ht₀S⟩, ?_⟩
    rw [← hc_eq, hI₀_eq, map_mul, ClassGroup.extendedHom_mk0]
  have hram_bd : Nat.card (stronglyAmbiguousTwoTorsion F K σ) ≤
      classGroupTwoTorsionCard F * 2 ^ S₀.card := by
    have hh := MonoidHom.card_powMonoidHom_ker_le_of_coset_cover
      (ClassGroup.extendedHom (𝓞 F) (𝓞 K)) (stronglyAmbiguousClassGroup F K σ)
      (fun t₀ : S₀.powerset => ClassGroup.mk0 (∏ Q ∈ t₀.val, Q)) hcover 2
    simpa only [Fintype.card_coe, Finset.card_powerset, stronglyAmbiguousTwoTorsion,
      classGroupTwoTorsionCard, classGroupTwoTorsion] using hh
  have hstr_bd : Nat.card (stronglyAmbiguousTwoTorsion F K σ) ≤
      classGroupTwoTorsionCard F *
        2 ^ (Module.finrank ℚ K * (NumberField.discr K).natAbs.primeFactors.card) :=
    hram_bd.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (hS₀_card.trans hS_card)))
  exact (classGroupTwoTorsionCard_le_stronglyAmbiguous F K hd σ hσ).trans
    ((Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hstr_bd) 2).trans_eq
      (by rw [mul_assoc, ← pow_add]))

theorem quadratic_field_classGroupTwoTorsionCard_le
    (K : Type*) [Field K] [NumberField K] (hd : Module.finrank ℚ K = 2) :
    classGroupTwoTorsionCard K ≤
      2 ^ (4 * (NumberField.discr K).natAbs.primeFactors.card + 2) := by
  have hh := quadratic_classGroupTwoTorsion_descent ℚ K hd
  have hQ1 : classGroupTwoTorsionCard ℚ = 1 := by
    let eO : ℤ ≃+* 𝓞 ℚ := Rat.ringOfIntegersEquiv.symm
    have : IsPrincipalIdealRing (𝓞 ℚ) := IsPrincipalIdealRing.of_surjective eO eO.surjective
    exact Nat.le_antisymm
      ((classGroupTwoTorsionCard_le_classNumber ℚ).trans
        (NumberField.classNumber_eq_one_iff.mpr inferInstance).le)
      (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos (α := classGroupTwoTorsion ℚ)).ne')
  rw [hQ1, hd, Module.finrank_self, one_mul, ← pow_mul] at hh
  convert hh using 1; congr 1; ring

end
end CCDN
