module

public import DedekindZetaZeroFree.Theta.Profiles.RayClasses.AffineResiduePackets
public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceQuotients.CodifferentGenerators
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveResidueCharacterKernels
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.GeneratorIdealCoefficients

@[expose] public section

/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

noncomputable section
open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta
variable {F : Type} [Field F] [NumberField F]

section

variable (hF : NumberField.IsTotallyComplex F) (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤) (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (E : RayCharacterData F m hm η)

theorem coprimeIdealResidueCoefficient_integral_lift (α : 𝓞 F) (hα : α ∈ a) :
    coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E
      (fractionalIdealQuotientMk
        (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
        ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
          FractionalIdeal (𝓞 F)⁰ F)
        ⟨(algebraMap (𝓞 F) F) α, coprimeIdealResidue_mem a ha α hα⟩) =
      (η a)⁻¹ * unitCharExtend
        ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η))
        (Ideal.Quotient.mk m α) := by
  classical
  let x : {x : F // x ∈ (rayIdealFractionalIdeal F a ha :
      FractionalIdeal (𝓞 F)⁰ F)} :=
    ⟨algebraMap (𝓞 F) F α, coprimeIdealResidue_mem a ha α hα⟩
  rw [coprimeIdealResidueCoefficient_mk]
  have hηa : η a ≠ 0 := by
    rw [ne_eq, η.eq_zero_iff']
    simp [ha, hcop]
  have hv : η (Ideal.span {α}) = η (integralElementIdeal
      (rayIdealFractionalIdeal F a ha) x) * η a := by
    rw [← (ResidueCoefficientAux.coefficient_mul a ha x α rfl), η.map_mul']
  by_cases hu : IsUnit (Ideal.Quotient.mk m α)
  · obtain ⟨u, hu⟩ := hu
    have hc := (ResidueCoefficientAux.quotient_unit_iff m α).mp (hu ▸ u.isUnit)
    have hn : α ≠ 0 := by
      intro hz
      have : m = ⊤ := by simpa [hz] using hc
      exact hmt this
    rw [← hu, unitCharExtend_coe]
    change η (integralElementIdeal (rayIdealFractionalIdeal F a ha) x) =
      (η a)⁻¹ * (residueRayCharacter hF hm hmt η u : ℂ)
    rw [residueRayCharacter_apply hF hm hmt η α hn hc u hu, hv]
    field_simp
  · rw [unitCharExtend_nonunit _ hu, mul_zero]
    have hz := (η.eq_zero_iff' _).mpr (Or.inr (fun h => hu ((ResidueCoefficientAux.quotient_unit_iff m α).mpr h)))
    exact (mul_eq_zero.mp (hv.symm.trans hz)).resolve_right hηa

theorem coprimeIdealResidueCoefficient_eq_residueRayCharacter (q : coprimeIdealResidue F m a hm ha) :
    coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q =
      (η a)⁻¹ * unitCharExtend
        ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η))
        (coprimeIdealResidueReduction F m a hm ha hcop q) := by
  obtain ⟨x, rfl⟩ := fractionalIdealQuotientMk_surjective
    (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
    ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F) q
  obtain ⟨α, hα, hx⟩ := ResidueCoefficientAux.integral_lift a ha x
  have hxeq : x = ⟨algebraMap (𝓞 F) F α,
      coprimeIdealResidue_mem a ha α hα⟩ := Subtype.ext hx.symm
  rw [hxeq, coprimeIdealResidueReduction_mk m a hm ha hcop α hα]
  exact coprimeIdealResidueCoefficient_integral_lift hF m a hm ha hcop hmt η E α hα

end

theorem coprimeIdealResiduePacket_eq_gauss_conjugate_coefficient
    (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (hprim : η.IsPrimitive) :
    letI : Finite (𝓞 F ⧸ m) := m.finiteQuotientOfFreeOfNeBot hm
    letI : Fintype (𝓞 F ⧸ m) := Fintype.ofFinite _
    letI := rayTraceQuotientModule m hm
    ∀ (β₀ : ((m : FractionalIdeal (𝓞 F)⁰ F)⁻¹ *
        codifferentFractionalIdeal F).coeToSubmodule)
      (hgen : Function.Bijective (LinearMap.toSpanSingleton (𝓞 F ⧸ m)
        (rayTraceQuotient m)
        (fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β₀)))
      (b : Ideal (𝓞 F)) (hb : b ≠ ⊥) (hbcop : m ⊔ b = ⊤)
      (hbimage : (b : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton (𝓞 F)⁰ (β₀ : F) *
          (m : FractionalIdeal (𝓞 F)⁰ F) * (codifferentFractionalIdeal F)⁻¹)
      (e₀ : AddChar (𝓞 F ⧸ m) ℂ)
      (he₀ : e₀ = rayTraceGeneratorChar m hm
        (fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β₀))
      (τ : ℂ)
      (hτ : τ = finiteRingGaussSum e₀
        ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η)))
      (a : Ideal (𝓞 F)) (ha : a ≠ ⊥) (hcop : a ⊔ m = ⊤)
      (E : RayCharacterData F m hm η)
      (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
        (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
          FractionalIdeal (𝓞 F)⁰ F)}),
      coprimeIdealResiduePacket hF m a hm ha hcop hmt η E β =
        τ * η b * (starRingEnd ℂ)
          (η (integralElementIdeal (Theta.traceDualIdealUnit F
            (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm)) β)) := by
  let FractionalIdeal₀ := FractionalIdeal (𝓞 F)⁰ F
  classical
  letI : Finite (𝓞 F ⧸ m) := m.finiteQuotientOfFreeOfNeBot hm
  letI : Fintype (𝓞 F ⧸ m) := Fintype.ofFinite _
  letI := rayTraceQuotientModule m hm
  intro β₀ hgen b hb hbcop hbimage e₀ he₀ τ hτ a ha hcop E β
  let I := rayIdealFractionalIdeal F a ha
  let M := rayIdealFractionalIdeal F m hm
  let L := Theta.traceDualIdealUnit F M
  let J := Theta.traceDualIdealUnit F (I * M)
  have hL : (L : FractionalIdeal₀) =
      (m : FractionalIdeal₀)⁻¹ * codifferentFractionalIdeal F := by
    rw [Theta.coe_traceDualIdealUnit_eq_dual_one_mul_inv]
    exact mul_comm _ _
  have hIJ : (I : FractionalIdeal₀) *
      (J : FractionalIdeal₀) = L := by
    change (I : FractionalIdeal₀) *
      (Theta.traceDualIdealUnit F (I * M) : FractionalIdeal₀) =
      (Theta.traceDualIdealUnit F M : FractionalIdeal₀)
    rw [Theta.coe_traceDualIdealUnit_eq_dual_one_mul_inv,
      Theta.coe_traceDualIdealUnit_eq_dual_one_mul_inv, Units.val_mul,
      mul_inv_rev]
    calc
      _ = FractionalIdeal.dual ℤ ℚ 1 * (M : FractionalIdeal₀)⁻¹ *
          ((I : FractionalIdeal₀) * (I : FractionalIdeal₀)⁻¹) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel₀ (Units.ne_zero I), mul_one]
  obtain ⟨γ, hγ, δ, hδ, hγδ⟩ := Ideal.isCoprime_iff_exists.mp
    (Ideal.isCoprime_iff_sup_eq.mpr hcop)
  have hγres : Ideal.Quotient.mk m γ = 1 := by
    have hh := congrArg (Ideal.Quotient.mk m) hγδ
    simpa [Ideal.Quotient.eq_zero_iff_mem.mpr hδ] using hh
  let xγ : {x : F // x ∈ (I : FractionalIdeal₀)} :=
    ⟨algebraMap (𝓞 F) F γ, coprimeIdealResidue_mem a ha γ hγ⟩
  let ξ : {x : F // x ∈ (L : FractionalIdeal₀)} :=
    ⟨(γ : F) * β.val, by
      rw [← hIJ]
      exact FractionalIdeal.mul_mem_mul xγ.property β.property⟩
  let ξ₀ : {x : F // x ∈ (L : FractionalIdeal₀)} :=
    ⟨β₀.val, by rw [hL]; exact β₀.property⟩
  let t : rayTraceQuotient m := fractionalIdealQuotientMk _
    (codifferentFractionalIdeal F) ⟨ξ.val, by rw [← hL]; exact ξ.property⟩
  let t₀ : rayTraceQuotient m := fractionalIdealQuotientMk _
    (codifferentFractionalIdeal F) β₀
  obtain ⟨k, hk⟩ := hgen.2 t
  have htk : t = k • t₀ := hk.symm
  have hcoeff := integralElementIdeal_trace_residue_coefficient hF hm hmt η L hL
    ξ₀ ξ k hgen.2 htk
  have hb₀ : integralElementIdeal L ξ₀ = b := by
    apply FractionalIdeal.coeIdeal_injective (K := F)
    change (integralElementIdeal L ξ₀ : FractionalIdeal₀) =
      (b : FractionalIdeal₀)
    rw [integralElementIdeal_trace_coe hm L hL, hbimage]
  have hC : η (integralElementIdeal L ξ) =
      unitCharExtend ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η)) k * η b := by
    simpa [hb₀] using hcoeff.2.2.1
  have hγcoeff : η (integralElementIdeal I xγ) = (η a)⁻¹ := by
    have hh := coprimeIdealResidueCoefficient_integral_lift hF m a hm ha hcop hmt η E γ hγ
    rw [coprimeIdealResidueCoefficient_mk, hγres] at hh
    simp [unitCharExtend] at hh
    exact hh
  have hξideal : integralElementIdeal L ξ =
      integralElementIdeal I xγ * integralElementIdeal J β := by
    apply FractionalIdeal.coeIdeal_injective (K := F)
    change (integralElementIdeal L ξ : FractionalIdeal₀) =
      ((integralElementIdeal I xγ * integralElementIdeal J β : Ideal (𝓞 F)) :
        FractionalIdeal₀)
    rw [FractionalIdeal.coeIdeal_mul, integralElementIdeal_coe,
      integralElementIdeal_coe, integralElementIdeal_coe]
    change FractionalIdeal.spanSingleton (𝓞 F)⁰ ((γ : F) * β.val) *
      (L : FractionalIdeal₀)⁻¹ =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) * (I : FractionalIdeal₀)⁻¹ *
        (FractionalIdeal.spanSingleton (𝓞 F)⁰ β.val * (J : FractionalIdeal₀)⁻¹)
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← hIJ, mul_inv_rev]
    ac_rfl
  have hrel : (η a)⁻¹ * η (integralElementIdeal J β) =
      unitCharExtend ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η)) k * η b := by
    rw [hξideal, η.map_mul', hγcoeff] at hC
    exact hC
  have hphase : ∀ q : coprimeIdealResidue F m a hm ha,
      coprimeIdealResiduePhase m a hm ha q β =
        e₀ (k * coprimeIdealResidueReduction F m a hm ha hcop q) := by
    intro q
    obtain ⟨x, rfl⟩ := fractionalIdealQuotientMk_surjective
      (I : FractionalIdeal₀) ((I * M) : FractionalIdeal₀) q
    obtain ⟨α, hα, hx⟩ := ResidueCoefficientAux.integral_lift a ha x
    have hxeq : x = ⟨algebraMap (𝓞 F) F α,
        coprimeIdealResidue_mem a ha α hα⟩ := Subtype.ext hx.symm
    rw [hxeq, coprimeIdealResidueReduction_mk m a hm ha hcop α hα]
    have hqeq : fractionalIdealQuotientMk (I : FractionalIdeal₀)
        ((I * M) : FractionalIdeal₀) (γ • x) =
        fractionalIdealQuotientMk (I : FractionalIdeal₀)
          ((I * M) : FractionalIdeal₀) x := by
      apply (Submodule.Quotient.eq _).mpr
      change (γ : F) * x.val - x.val ∈ ((I * M) : FractionalIdeal₀)
      have hd : (δ : F) ∈ (M : FractionalIdeal₀) :=
        coprimeIdealResidue_mem m hm δ hδ
      have hdγ : (γ : F) + (δ : F) = 1 := by exact_mod_cast hγδ
      have heq : (γ : F) * x.val - x.val = -(x.val * (δ : F)) := by
        calc
          _ = (γ : F) * x.val - ((γ : F) + (δ : F)) * x.val := by rw [hdγ, one_mul]
          _ = _ := by ring
      rw [heq]
      exact ((I * M : (FractionalIdeal₀)ˣ) :
        FractionalIdeal₀).coeToSubmodule.neg_mem
          (FractionalIdeal.mul_mem_mul x.property hd)
    have hpeq := congrArg (fun z => coprimeIdealResiduePhase m a hm ha z β) hqeq
    rw [coprimeIdealResiduePhase_mk, coprimeIdealResiduePhase_mk] at hpeq
    rw [he₀, rayTraceGeneratorChar_apply,
      rayTraceQuotientPairing_balance, ← htk]
    have hp := rayTraceQuotientPairing_mk m hm α
      (⟨ξ.val, by rw [← hL]; exact ξ.property⟩ :
        ((m : FractionalIdeal₀)⁻¹ * codifferentFractionalIdeal F).coeToSubmodule)
    change rationalTracePhase (Algebra.trace ℚ F ((α : F) * β.val)) =
      rayTraceQuotientPairing m hm (Ideal.Quotient.mk m α) t
    rw [hp, ← rationalTracePhase_apply_real]
    change rationalTracePhase (Algebra.trace ℚ F ((α : F) * β.val)) =
      rationalTracePhase (Algebra.trace ℚ F ((α : F) * ((γ : F) * β.val)))
    have hh : rationalTracePhase (Algebra.trace ℚ F ((γ : F) * x.val * β.val)) =
        rationalTracePhase (Algebra.trace ℚ F (x.val * β.val)) := hpeq
    rw [← hx] at hh
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hh.symm
  let χ := (Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η)
  letI : Nontrivial (𝓞 F ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hmt
  have he : IsPrimitiveRingAddChar e₀ := by
    rw [he₀]
    exact rayTraceGeneratorChar_primitive m hm t₀ hgen
  have hχ : IsPrimitiveRingUnitChar χ := by
    intro A hA
    let f := Ideal.comap (Ideal.Quotient.mk m) A
    have hmf : m ≤ f := by
      intro z hz
      change Ideal.Quotient.mk m z ∈ A
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact A.zero_mem
    have hstrict : m < f := by
      refine lt_of_le_of_ne hmf ?_
      intro heq
      apply hA
      apply bot_unique
      intro z hz
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hw : w ∈ f := hz
      rw [← heq] at hw
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hw
    obtain ⟨u, hu, hne⟩ := residueRayCharacter_exists_kernel_ne_one hF hm hmt η hprim f hstrict
    refine ⟨u, ?_, ?_⟩
    · obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 F ⧸ m)
      have hf : Ideal.Quotient.mk f w = 1 := by
        rw [← Ideal.Quotient.factor_mk hmf, hw]
        exact congrArg Units.val hu
      have hmem : w - 1 ∈ f := (Ideal.Quotient.mk_eq_one_iff_sub_mem w).mp hf
      change Ideal.Quotient.mk m w - 1 ∈ A at hmem
      simpa [hw] using hmem
    · change (residueRayCharacter hF hm hmt η u : ℂ) ≠ 1
      exact fun h => hne (Units.ext h)
  have hpacket : coprimeIdealResiduePacket hF m a hm ha hcop hmt η E β =
      (η a)⁻¹ * finiteRingFourier e₀ (unitCharExtend χ) k := by
    letI := coprimeIdealResidue_finite m a hm ha hcop
    letI := Fintype.ofFinite (coprimeIdealResidue F m a hm ha)
    unfold coprimeIdealResiduePacket finiteRingFourier
    rw [Finset.mul_sum]
    calc
      _ = ∑ q : coprimeIdealResidue F m a hm ha,
          (η a)⁻¹ * (unitCharExtend χ
            (coprimeIdealResidueReduction F m a hm ha hcop q) *
            e₀ (k * coprimeIdealResidueReduction F m a hm ha hcop q)) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [coprimeIdealResidueCoefficient_eq_residueRayCharacter, hphase]
        exact mul_assoc _ _ _
      _ = _ := Equiv.sum_comp (coprimeIdealResidueReduction F m a hm ha hcop).toEquiv
        (fun z : 𝓞 F ⧸ m => (η a)⁻¹ * (unitCharExtend χ z * e₀ (k * z)))
  rw [primitiveUnitChar_fourier e₀ he χ hχ k, ← hτ] at hpacket
  have hηa : η a ≠ 0 := by
    rw [ne_eq, η.eq_zero_iff']
    simp [ha, hcop]
  have hnorma : ‖η a‖ = 1 := rayClassCharacter_norm_eq_one hm η a ha hcop
  have hnormb : ‖η b‖ = 1 :=
    rayClassCharacter_norm_eq_one hm η b hb (sup_comm m b ▸ hbcop)
  have hrel' : η (integralElementIdeal J β) =
      η a * unitCharExtend χ k * η b := by
    have hh := congrArg (fun z : ℂ => η a * z) hrel
    simpa only [← mul_assoc, mul_inv_cancel₀ hηa, one_mul] using hh
  change coprimeIdealResiduePacket hF m a hm ha hcop hmt η E β =
    τ * η b * (starRingEnd ℂ) (η (integralElementIdeal J β))
  rw [hpacket, hrel', map_mul, map_mul, ← RCLike.inv_eq_conj hnorma]
  have hbconj : η b * (starRingEnd ℂ) (η b) = 1 := by
    rw [Complex.mul_conj', hnormb]
    norm_num
  calc
    _ = (η a)⁻¹ * ((starRingEnd ℂ) (unitCharExtend χ k) * τ) *
        (η b * (starRingEnd ℂ) (η b)) := by rw [hbconj, mul_one]
    _ = _ := by ring

end DedekindZetaZeroFree.Hecke.Theta

end
