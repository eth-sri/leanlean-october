module

public import OAI.NumberTheory.DirichletL.Energy.State
public import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalControl
public import OAI.NumberTheory.DirichletL.Moments.InductionEnergy
public import OAI.NumberTheory.DirichletL.Moments.PlainPositiveEnergy
public import OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorCoefficients
public import OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorNatural

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional (Profiles)
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem exists_positive_floor {α : Type*} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ bΦ Bmask ε Lslot lo hi κ : ℝ)
    (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hbΦ : 0<bΦ) (hmask : 0≤Bmask)
    (hε : 0<ε) (hLs : 0≤Lslot) (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤T → (∀i,|v i|≤T) →
    ∀(Q : Ideal O),Q≤M → ∀s : NaturalState Z Bmask bΦ,
      s.fixedModulus=internalQ Q η₀ → s.width≤ε/16 → 6*κ*(∑i,w i)≤s.width →
    ∀p : Profiles a₀ b₀,∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^degree*Z^(s.width+ε) := by
  let e : ℝ := ε/(4*(Bmask+1))
  have he : 0<e := div_pos hε (by positivity)
  have hcost : Bmask*e≤ε/4 := by
    have hh := mul_le_mul_of_nonneg_left (show Bmask≤Bmask+1 by linarith) he.le
    have hid : e*(Bmask+1)=ε/4 := by dsimp [e]; field_simp
    rw [hid] at hh
    linarith
  let L := ε/16
  let loss := ε/4
  let F := (Finset.univ : Finset α)
  obtain ⟨J,S,C,hC,hbound⟩ := natural_pair_slots M H hH F W a b ha hWs hW a₀ b₀ ha₀
    (L+1) Lslot loss lo hi κ (by dsimp [L]; positivity) hLs (by dsimp [loss]; positivity) hbeta hκ
  obtain ⟨B,hB,hcoeff⟩ := slot_coefficient_bounds W a b lo hi ha hWs hW.continuous
  obtain ⟨Cd,hCd,hdelete⟩ := CenteredMomentCommonMaskRadialEnergy.actual_radial_shared_energy
    F (fun _=>b) (fun _=>B) (fun _ _=>hB.le) e he
  obtain ⟨n,T₀,Ct,hCt,ht⟩ :=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a₀ b₀ ha₀ S
  let Fc : ℝ := fixedConductorFactor
  have hFc : 0<Fc := by
    unfold Fc fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨4*n+J,T₀,Cd*C*Ct^4*Fc^4*bΦ^4,by positivity,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_ge_atTop (Fc*bΦ)] with Z hZ hconst
  intro θ w σ v t T hw hwL hσlo hσhi hT hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  let η := s.character
  let R := s.puncture
  let r := s.radial
  let r' : Radial := {r with keep := fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  let Qbound := Fc*bΦ*Z^L
  have hZ1 := s.base_ge_one
  have hZ0 := zero_lt_one.trans_le hZ1
  have hz (z : O) (hk : r'.keep z) := s.row_ne_zero z hk.1
  have hex (z : O) (hk : r'.keep z) : ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z := by
    intro hh
    have hx := s.nonexceptional z hk.1
    rw [hQ] at hx
    exact hx ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff η (internalQ Q η₀)
      fixedBadMask (ConcretePrimeRowBridge.idealGenerator R) 1 z fixedBadMask_ne_zero
      (ConcretePrimeRowBridge.idealGenerator_ne_zero R s.puncture_ne_zero) one_ne_zero (hz z hk)
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hh)
  have hmod (z : O) (hk : r'.keep z) : ((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound := by
    rw [naturalCharacter_eq η z (hz z hk)]
    have hrow : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^s.rowWidth := by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←s.scale_eq]
      exact (div_le_iff₀ r.scale_pos).mp (s.radial_support hk.2)
    exact ((naturalRow η z (hz z hk)).modulus_power_bound Z s.characterWidth s.rowWidth bΦ hZ0
      hbΦ.le s.modulus_bound hrow).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1 (by dsimp [L] at *; unfold NaturalState.width at hs; linarith)) (by positivity))
  have hcap (z : O) (hk : r'.keep z) : ((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^(L+1) := by
    rw [Real.rpow_add hZ0,Real.rpow_one,mul_comm]
    exact (hmod z hk).trans (mul_le_mul_of_nonneg_right hconst (by positivity))
  let V (j : Fin 2) := CenteredMomentLattice.normPowerProfile (p.profile j) a₀ b₀ ha₀ (p.support j)
    ((p.profile j).smooth ⊤) t
  have hV (j : Fin 2) : Function.support (V j)⊆Set.Icc a₀ b₀ :=
    (CenteredMomentTwist.normPowerProfile_support _ _ _ ha₀ (p.support j) _ _).trans (p.support j)
  let semin (S : Finset (ℕ×ℕ)) (φ : 𝓢(ℝ,ℂ)) := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) φ
  let E := C*diagonalControl r.profile*max 1 r.scale*(semin S (V 0)*semin S (V 1))^2*Qbound^4*
    (1+|t|+T)^J*Z^(loss+κ*(∑i,w i))
  have hd := diagonalControl_nonneg r.profile
  have hE : 0≤E := by dsimp [E]; positivity
  let P (i : α) := Z^(w i)
  let pool (i : α) := primePool M H b (P i)
  let coeff (i : α) (I : Ideal O) := idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight W (P i) (σ i) (v i) I
  have hp (i : α) (_ : i∈F) (I : Ideal O) (hI : I∈pool i) := (Finset.mem_filter.mp hI).2.1
  have hc (i : α) (hi : i∈F) (I : Ideal O) (hI : I∈pool i) :=
    hcoeff (relativeCharacter M H hH η₀ (θ i)) (P i) (σ i) (v i) t
      (Real.rpow_pos_of_pos hZ0 _) (hσlo i) (hσhi i) I (hp i hi I hI).ne_zero
  have hE' := hdelete (CompletedGauss.primeSupport R) (support_prime R) (naturalCharacter η)
    (V 0) (V 1) X₁ X₂ a₀ b₀ a₀ b₀ pool (fun i=>heightCoefficient (coeff i) t) P
    r'.keep r.profile r.scale E hX₁ hX₂ hb₀ hb₀ (hV 0) (hV 1) hp
    (fun _ _=>Real.rpow_pos_of_pos hZ0 _) (fun i hi I hI=>(hc i hi I hI).1)
    (fun i hi I hI=>(hc i hi I hI).2) r.scale_pos r.nonneg hE (by
      intro D₁ hD₁ D₂ hD₂ A hA
      have hn (D : Finset (Ideal O)) (hD : D∈(CompletedGauss.primeSupport R).powerset) :
          0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
          (Finset.prod_ne_zero_iff.mpr (fun I hi=>(support_prime R I (Finset.mem_powerset.mp hD hi)).ne_zero)))
      exact hZ θ w σ v t T (fun i _=>hw i) (fun i _=>hwL i) (fun i _=>hσlo i) (fun i _=>hσhi i)
        hT (fun i _=>hv i) η Q r' Qbound hQM (by dsimp [Qbound]; positivity) hz hex hcap hmod
        (V 0) (V 1) (hV 0) (hV 1) _ _ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂))
        (F\A) Finset.sdiff_subset)
  rw [primeSupport_product_radical R s.puncture_ne_zero] at hE'
  have hprod : (semin S (V 0)*semin S (V 1))^2 ≤ Ct^4*(p.control T₀)^2*(1+|t|+T)^(4*n) := by
    have hB (j : Fin 2) : semin S (V j) ≤ Ct*semin T₀ (p.profile j)*(1+|t|+T)^n := by
      apply (ht (p.profile j) (p.support j) t).trans
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (show 1+|t|≤1+|t|+T by linarith) n) (by positivity)
    calc
      _ ≤ (Ct*semin T₀ (p.profile 0)*(1+|t|+T)^n*
        (Ct*semin T₀ (p.profile 1)*(1+|t|+T)^n))^2 := by
        dsimp only [semin] at *
        gcongr <;> (first | exact hB 0 | exact hB 1)
      _ = _ := by change _ = Ct^4*(semin T₀ (p.profile 0)*semin T₀ (p.profile 1))^2*_; ring
  have hrad : (R.radical.absNorm:ℝ)^e≤Z^(Bmask*e) := by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by positivity) s.radical_bound he.le
  have hscale : max 1 r.scale=Z^s.rowWidth := by
    change max 1 s.radial.scale=_
    rw [s.scale_eq,max_eq_right (Real.one_le_rpow hZ1 s.row_nonneg)]
  have hQpow : Qbound^4 = Fc^4*bΦ^4*Z^(4*L) := by
    dsimp [Qbound]
    rw [mul_pow,mul_pow,←Real.rpow_natCast (Z^L),←Real.rpow_mul hZ0.le]
    congr 2 <;> ring
  have hbudget : Bmask*e+s.rowWidth+4*L+(loss+κ*(∑i,w i))≤s.width+ε := by
    dsimp [L,loss,NaturalState.width] at *
    linarith [s.character_nonneg]
  have hpow : Z^(Bmask*e)*Z^s.rowWidth*Z^(4*L)*Z^(loss+κ*(∑i,w i))≤Z^(s.width+ε) := by
    simp only [←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 hbudget
  calc
    _ = _ := ?_
    _ ≤ _ := hE'
    _ ≤ Cd*Z^(Bmask*e)*(C*diagonalControl r.profile*Z^s.rowWidth*
        (Ct^4*(p.control T₀)^2*(1+|t|+T)^(4*n))*(Fc^4*bΦ^4*Z^(4*L))*
        (1+|t|+T)^J*Z^(loss+κ*(∑i,w i))) := by
      dsimp only [E]
      rw [hscale,hQpow]
      gcongr
    _ = (Cd*C*Ct^4*Fc^4*bΦ^4*diagonalControl r.profile*(p.control T₀)^2*(1+|t|+T)^(4*n+J))*
        (Z^(Bmask*e)*Z^s.rowWidth*Z^(4*L)*Z^(loss+κ*(∑i,w i))) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hk : r.keep z
  · by_cases hΦ : r.profile (‖eisEmbedding z‖^2/r.scale)=0
    · simp [r', r, hk, hΦ]
    · simp only [r', show s.radial.keep z from hk, hk, hΦ, ne_eq, not_false_eq_true, and_self, ite_true, NaturalState.mask]
      rw [original_positive_normalized (naturalRow η z (s.row_ne_zero z hk)) R s.puncture_ne_zero
        (p.profile 0) (p.profile 1) a₀ b₀ a₀ b₀ ha₀ ha₀ (p.support 0) (p.support 1)
        ((p.profile 0).smooth ⊤) ((p.profile 1).smooth ⊤)
        pool coeff P (fun _=>Real.rpow_pos_of_pos hZ0 _) t X₁ X₂ hX₁ hX₂]
      rw [norm_mul,norm_mul,positive_height_phase_norm X₁ t hX₁,
        positive_height_phase_norm X₂ t hX₂,one_mul,one_mul,naturalCharacter_eq η z (s.row_ne_zero z hk)]
      rfl
  · simp [r', r, hk, show ¬s.radial.keep z from hk]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
