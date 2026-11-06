module
public import OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion
public import OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceDictionary
public import OAI.NumberTheory.DirichletL.Moments.PositiveSummability

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentCommonMaskEnergy
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentLattice
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O

theorem finite_shared_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a f : ι→κ→ℂ) (ρ : κ→ℝ) (hρ : ∀j,0≤ρ j)
    (ha : ∀i j,‖a i j‖≤ρ j) (E : ℝ) (hE : 0≤E)
    (hf : ∀j,(∑i,‖f i j‖^2)≤E) :
    (∑i,‖∑j,a i j*f i j‖^2)≤(∑j,ρ j)^2*E := by
  have hb (j : κ) : (∑i,‖a i j*f i j‖^2)≤(ρ j*Real.sqrt E)^2 := by
    calc
      _≤∑i,(ρ j)^2*‖f i j‖^2 := Finset.sum_le_sum (fun i _=>by
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2) (sq_nonneg _))
      _=(ρ j)^2*(∑i,‖f i j‖^2) := (Finset.mul_sum _ _ _).symm
      _≤(ρ j)^2*E := mul_le_mul_of_nonneg_left (hf j) (sq_nonneg _)
      _=_ := by rw [mul_pow,Real.sq_sqrt hE]
  have hh := CompletedGauss.finite_tsum_energy_bound
    (fun j i=>a i j*f i j) (fun j=>ρ j*Real.sqrt E)
    (fun j=>mul_nonneg (hρ j) (Real.sqrt_nonneg _)) (summable_of_hasFiniteSupport (Set.toFinite _)) hb
  simpa only [tsum_fintype,←Finset.sum_mul,mul_pow,Real.sq_sqrt hE] using hh.2

lemma triple_sum {τ : Type*} {υ : Type*} {ξ : Type*} {A : Type*} [AddCommMonoid A]
    (S : Finset τ) (T : Finset υ) (U : Finset ξ)
    [Fintype ({x // x∈S}×{x // x∈T}×{x // x∈U})]
    (g : τ→υ→ξ→A) :
    (∑j : {x // x∈S}×{x // x∈T}×{x // x∈U},g j.1.val j.2.1.val j.2.2.val)=
      ∑x∈S,∑y∈T,∑z∈U,g x y z := by
  have hh : (∑j : {x // x∈S}×{x // x∈T}×{x // x∈U},g j.1.val j.2.1.val j.2.2.val)=
      ∑j∈S×ˢ(T×ˢU),g j.1 j.2.1 j.2.2 := by
    apply Finset.sum_bij (fun j _=>(j.1.val,j.2.1.val,j.2.2.val))
    · intro j _
      exact Finset.mem_product.mpr ⟨j.1.property,Finset.mem_product.mpr ⟨j.2.1.property,j.2.2.property⟩⟩
    · intro i _ j _ h
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst h)
      · apply Prod.ext
        · exact Subtype.ext (congrArg (fun x=>x.2.1) h)
        · exact Subtype.ext (congrArg (fun x=>x.2.2) h)
    · intro j hj
      obtain ⟨h1,h23⟩:=Finset.mem_product.mp hj
      obtain ⟨h2,h3⟩:=Finset.mem_product.mp h23
      exact ⟨(⟨j.1,h1⟩,⟨j.2.1,h2⟩,⟨j.2.2,h3⟩),Finset.mem_univ _,rfl⟩
    · intro j _
      rfl
  simpa only [Finset.sum_product] using hh

theorem actual_shared_energy {α : Type*} [DecidableEq α]
    (F : Finset α) (b M : α→ℝ) (hM : ∀j∈F,0≤M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,j∈F → ∀I∈pool i j,Prime I) → (∀i j,j∈F → 0<P i j) →
      (∀i j,j∈F → ∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,j∈F → ∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false (W₁ i)
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false (W₂ i)
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ i) (pool i j) (β i j) (P i j)‖^2)≤E) →
      (∑i,‖HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
        HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
        ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j)‖^2)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E := by
  obtain ⟨C,hC,hmass⟩:=uniform_mass_subpower F b M hM (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι _ R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE he
  let κ := {D : Finset (Ideal O) // D∈R.powerset} ×
    {D : Finset (Ideal O) // D∈R.powerset} × {J : Finset α // J∈F.powerset}
  let a (i : ι) (j : κ) := signedCoefficient (χ i) R j.1.val j.2.1.val j.2.2.val (pool i) (β i) (P i)
  let f (i : ι) (j : κ) := HeckeDyadic.polynomial (χ i) false (W₁ i)
    (X₁ i/(Ideal.absNorm (∏I∈j.1.val,I):ℝ)) 0 0 *
    HeckeDyadic.polynomial (χ i) false (W₂ i)
    (X₂ i/(Ideal.absNorm (∏I∈j.2.1.val,I):ℝ)) 0 0 *
    ∏k∈F\j.2.2.val,naturalSlot (χ i) (pool i k) (β i k) (P i k)
  let ρ (j : κ) := uniformMajorant R j.1.val j.2.1.val j.2.2.val b M
  have hρ (j : κ) : 0≤ρ j := uniformMajorant_nonneg _ _ _ _ _ _
    (fun k hk=>hM k (Finset.mem_powerset.mp j.2.2.property hk))
  have ha (i : ι) (j : κ) : ‖a i j‖≤ρ j := by
    exact signedCoefficient_uniform (χ i) R hR _ _
      (Finset.mem_powerset.mp j.1.property) (Finset.mem_powerset.mp j.2.1.property)
      _ (pool i) (β i) (P i) b M
      (fun k hk=>hp i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hP i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hM k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hβ i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hs i k (Finset.mem_powerset.mp j.2.2.property hk))
  have hh:=finite_shared_energy a f ρ hρ ha E hE
    (fun j=>he j.1.val j.1.property j.2.1.val j.2.1.property j.2.2.val j.2.2.property)
  have hid (i : ι) : (∑j,a i j*f i j)=
      HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
      HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
      ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j) := by
    exact (triple_sum R.powerset R.powerset F.powerset
      (fun D₁ D₂ J=>signedCoefficient (χ i) R D₁ D₂ J (pool i) (β i) (P i)*
        (HeckeDyadic.polynomial (χ i) false (W₁ i) (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
         HeckeDyadic.polynomial (χ i) false (W₂ i) (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
         ∏k∈F\J,naturalSlot (χ i) (pool i k) (β i k) (P i k)))).trans
      (simultaneous_deletion (χ i) R hR (W₁ i) (W₂ i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
        F (pool i) (hp i) (β i) (P i)).symm
  have hm : (∑j,ρ j)≤C*(Ideal.absNorm (∏I∈R,I):ℝ)^(ε/2) := by
    exact (triple_sum R.powerset R.powerset F.powerset
      (fun D₁ D₂ J=>uniformMajorant R D₁ D₂ J b M)).trans_le (hmass R hR)
  have hr : ((Ideal.absNorm (∏I∈R,I):ℝ)^(ε/2))^2=(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  simp_rw [hid] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _=>hρ j)) hm 2) hE).trans_eq
      (by rw [mul_pow,hr]))

lemma sqrt_inverse_cpow (X : ℝ) (hX : 0<X) :
    (Real.sqrt X:ℂ)⁻¹=(X:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hX.le (1/2:ℝ))

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ false W X 0 0=(Real.sqrt X:ℂ)⁻¹*idealSum χ W X := by
  rw [sqrt_inverse_cpow X hX]
  unfold HeckeDyadic.polynomial idealSum
  congr 1
  have he:=tsum_subtype_eq_of_support_subset
    (s:={I : Ideal O | I≠0}) (f:=fun I : Ideal O=>idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi;subst I;exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=_ at he
  simpa only [HeckeDyadic.summand,HeckeDyadic.coefficient,Bool.false_eq_true,ite_false,
    HeckeDyadic.norm,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.NonzeroIdeal,UnrestrictedIdealReindex.NonzeroIdeal] using he

def heightCoefficient (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) : ℂ :=
  β I*(I.absNorm:ℂ)^(Complex.I*t)

lemma heightCoefficient_norm (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoefficient β t I‖=‖β I‖ := by
  have hn : (0:ℝ)<I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [heightCoefficient,norm_mul]
  have hp : ‖(I.absNorm:ℂ)^(Complex.I*t)‖=1 := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hn (Complex.I*t)
  rw [hp,mul_one]

theorem original_positive_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hP : ∀i,0<P i) (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) X₁ 0 0 *
         HeckeDyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₂ 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  rw [F.masked_positive R hR,twistedIdealSum_scale _ W₁ a₁ b₁ ha₁ hs₁ hW₁ t X₁ hX₁,
    twistedIdealSum_scale _ W₂ a₂ b₂ ha₂ hs₂ hW₂ t X₂ hX₂,
    plain_zero_height _ _ X₁ hX₁,plain_zero_height _ _ X₂ hX₂]
  have hn : (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹=
      (Real.sqrt X₁:ℂ)⁻¹*(Real.sqrt X₂:ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹ := by
    rw [Real.sqrt_mul (mul_pos hX₁ hX₂).le,Real.sqrt_mul hX₁.le,
      Real.sqrt_prod _ (fun i _=>(hP i).le),Complex.ofReal_mul,Complex.ofReal_mul,
      Complex.ofReal_prod,mul_inv_rev,mul_inv_rev,Finset.prod_inv_distrib]
    ring
  have hc (i : α) : (∑I∈pool i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t))=
      ∑I∈pool i,idealCoeff (excluded F.character R) I*heightCoefficient (β i) t I := by
    apply Finset.sum_congr rfl
    intro I hI
    unfold heightCoefficient
    ring
  simp_rw [hc]
  simp only [naturalSlot,Finset.prod_mul_distrib]
  rw [hn]
  ring

lemma positive_height_phase_norm (X t : ℝ) (hX : 0<X) : ‖(X:ℂ)^(Complex.I*t)‖=1 := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hX (Complex.I*t)

theorem original_positive_deletion {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (hp : ∀i,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    let χ:=(naturalRow η z hz).character
    let S:=CompletedGauss.primeSupport R
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        ∑D₁∈S.powerset,∑D₂∈S.powerset,∑J∈(Finset.univ : Finset α).powerset,
          signedCoefficient χ S D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
          (HeckeDyadic.polynomial χ false (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
            (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
           HeckeDyadic.polynomial χ false (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
            (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
           ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)) := by
  dsimp only
  rw [original_positive_normalized (naturalRow η z hz) R hR W₁ W₂ a₁ b₁ a₂ b₂
    ha₁ ha₂ hs₁ hs₂ hW₁ hW₂ pool β P hP t X₁ X₂ hX₁ hX₂]
  congr 1
  exact simultaneous_deletion (naturalRow η z hz).character (CompletedGauss.primeSupport R)
    (support_prime R) (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
    (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₁ X₂ hX₁ hX₂ Finset.univ pool
    (fun i _=>hp i) (fun i=>heightCoefficient (β i) t) P

theorem original_retained_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hr₁ : 1≤X₁*b₁) (hr₂ : 1≤X₂*b₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      (((clippedScale X₁):ℂ)^(Complex.I*t)*((clippedScale X₂):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded F.character R) false
          (retainedProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ X₁ hX₁ hr₁ t) (clippedScale X₁) 0 0 *
         HeckeDyadic.polynomial (excluded F.character R) false
          (retainedProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ X₂ hX₂ hr₂ t) (clippedScale X₂) 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  exact original_positive_normalized F R hR (dilated W₁ (clipDilation X₁))
    (dilated W₂ (clipDilation X₂)) (a₁/max 1 b₁) b₁ (a₂/max 1 b₂) b₂
    (div_pos ha₁ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (div_pos ha₂ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W₁ a₁ b₁ (max 1 b₁) (clipDilation X₁) ha₁ (le_max_left _ _)
      (clipDilation_ge_one X₁ hX₁) (clipDilation_le b₁ X₁ hX₁ hr₁) hs₁)
    (dilated_support W₂ a₂ b₂ (max 1 b₂) (clipDilation X₂) ha₂ (le_max_left _ _)
      (clipDilation_ge_one X₂ hX₂) (clipDilation_le b₂ X₂ hX₂ hr₂) hs₂)
    (dilated_contDiff W₁ hW₁ _) (dilated_contDiff W₂ hW₂ _) pool β P hP t
    _ _ (by unfold clippedScale;positivity) (by unfold clippedScale;positivity)

theorem original_retained_zero {α : Type*} [Fintype α]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hz : X₁*b₁<1 ∨ X₂*b₂<1) :
    retainedPositiveRow η m A z W₁ W₂ pool β P t X₁ X₂=0 := by
  unfold retainedPositiveRow positiveSlotRow
  rw [←clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,
    ←clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]
  rcases hz with h|h
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t X₁ hX₁ hs₁ h]
    simp
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t X₂ hX₂ hs₂ h]
    simp

end SevenEighths.CenteredMomentCommonMaskEnergy

end

end OAI
