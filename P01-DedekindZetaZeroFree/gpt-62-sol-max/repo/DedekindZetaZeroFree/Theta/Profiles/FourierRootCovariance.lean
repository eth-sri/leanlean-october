module

public import DedekindZetaZeroFree.Theta.Profiles.IdelicDilation

@[expose] public section

open scoped NumberField Classical
open NumberField MeasureTheory

namespace DedekindZetaZeroFree.MomentSources

variable {F : Type} [Field F] [NumberField F] {S : SArithmeticData F}
  {η : RayClassCharacter F S.modulus} (R : PrincipalMellin.ActualRecipe S η)

local notation "root" => KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12

/-- Translation of a Fourier period by an upper root. Only invariance under
rational roots and translation invariance of Haar measure are needed. -/
theorem fourier_left_root (μ : Measure (KPAdditiveQuotient F)) [μ.IsAddHaarMeasure]
    (θ : Functions R) (hθ : ∀ (t : F) (g : Group R), θ
      (root (algebraMap F (KPAdeles F) t) * g) = θ g)
    (a : KPAdeles F) (g : Group R) :
    fourier R μ θ (root a * g) =
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk a) : ℂ) * fourier R μ θ g := by
  let f : KPAdditiveQuotient F → ℂ := fun q => θ (root (Quotient.out q) * g)
  have hrep (b : KPAdeles F) : f (QuotientAddGroup.mk b) = θ (root b * g) := by
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add (AdeleRing.principalSubgroup (𝓞 F) F) b
    obtain ⟨t, ht⟩ := r.property
    dsimp [f]
    rw [hr, ← ht, add_comm, KPGlobalTorusFunctionData.N_add, mul_assoc, hθ]
  let b : KPAdditiveQuotient F := QuotientAddGroup.mk a
  have hshift (q : KPAdditiveQuotient F) : θ (root (Quotient.out q) * (root a * g)) = f (q + b) := by
    have hq : q + b = (QuotientAddGroup.mk (Quotient.out q + a) : KPAdditiveQuotient F) := by
      rw [QuotientAddGroup.mk_add]
      exact congrArg (fun z => z + b) (Quotient.out_eq q).symm
    rw [hq, hrep, KPGlobalTorusFunctionData.N_add, mul_assoc]
  let χ := adelicTraceQuotientCharacter F
  have hc : (χ b : ℂ) * star (χ b : ℂ) = 1 := by
    change (χ b : ℂ) * (starRingEnd ℂ) (χ b : ℂ) = 1
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  change (∫ q, θ (root (Quotient.out q) * (root a * g)) * star (χ q : ℂ) ∂μ) =
    (χ b : ℂ) * ∫ q, f q * star (χ q : ℂ) ∂μ
  calc
    _ = ∫ q, (χ b : ℂ) * (f (q + b) * star (χ (q + b) : ℂ)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with q
      rw [hshift q, AddChar.map_add_eq_mul, Circle.coe_mul, star_mul]
      linear_combination -(f (q + b) * star (χ q : ℂ)) * hc
    _ = _ := by
      rw [integral_const_mul]
      exact congrArg ((χ b : ℂ) * ·) (integral_add_right_eq_self (μ := μ)
        (fun q => f q * star (χ q : ℂ)) b)

theorem finite_root_injection (q : KPFinitePlace F) (t : q.adicCompletion F) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inr q) (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t)) =
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t) := by
  exact (congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12
    R.A.primitive_zeta12) (KPRationalAdelicSplitting.N_local F R.A.zeta12
      R.A.primitive_zeta12 (Sum.inr q) t)).symm

end DedekindZetaZeroFree.MomentSources
