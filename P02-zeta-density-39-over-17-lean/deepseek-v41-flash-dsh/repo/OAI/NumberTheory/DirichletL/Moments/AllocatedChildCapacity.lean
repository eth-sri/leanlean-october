module
public import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource
public import OAI.NumberTheory.DirichletL.Moments.CommonMaskChildCapacity
public import OAI.NumberTheory.DirichletL.Moments.CommonRawScale
public import OAI.NumberTheory.DirichletL.Moments.LiveCapacity

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle CenteredMomentDivisorRaw CenteredMomentDivisorRetained CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

def clippingLoss (Z U₁ U₂ : ℝ) : ℝ :=
  max (-Real.logb Z U₁) 0+max (-Real.logb Z U₂) 0

lemma clipped_log (Z U : ℝ) (hZ : 1<Z) (hU : 0<U) :
    Real.logb Z (clippedScale U)=Real.logb Z U+max (-Real.logb Z U) 0 := by
  by_cases h : 1≤U
  · rw [clippedScale,max_eq_right h,max_eq_right (neg_nonpos.mpr (Real.logb_nonneg hZ h))]
    ring
  · have hu : U≤1 := (lt_of_not_ge h).le
    have hl : Real.logb Z U≤0 := Real.logb_nonpos hZ hU.le hu
    rw [clippedScale,max_eq_left hu,max_eq_left (neg_nonneg.mpr hl),Real.logb_one]
    ring

lemma clipped_pair_log (Z U₁ U₂ : ℝ) (hZ : 1<Z) (h₁ : 0<U₁) (h₂ : 0<U₂) :
    Real.logb Z (clippedScale U₁)+Real.logb Z (clippedScale U₂)=
      Real.logb Z U₁+Real.logb Z U₂+clippingLoss Z U₁ U₂ := by
  rw [clipped_log Z U₁ hZ h₁,clipped_log Z U₂ hZ h₂]
  unfold clippingLoss
  ring

lemma clipping_loss_bound (Z U₁ U₂ b₁ b₂ : ℝ) (hZ : 1<Z)
    (h₁ : 0<U₁) (h₂ : 0<U₂) (hs₁ : 1≤U₁*b₁) (hs₂ : 1≤U₂*b₂) :
    0≤clippingLoss Z U₁ U₂ ∧
      clippingLoss Z U₁ U₂≤Real.logb Z (max 1 b₁*max 1 b₂) := by
  have one (U b : ℝ) (hU : 0<U) (hs : 1≤U*b) :
      max (-Real.logb Z U) 0≤Real.logb Z (max 1 b) := by
    have hb : 0<max 1 b := zero_lt_one.trans_le (le_max_left _ _)
    have hc : clippedScale U≤max 1 b*U := by
      apply max_le
      · exact hs.trans (by nlinarith [le_max_right (1:ℝ) b])
      · nlinarith [le_max_left (1:ℝ) b]
    have hl := Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (clippedScale_ge_one U)) hc
    rw [clipped_log Z U hZ hU,Real.logb_mul hb.ne' hU.ne'] at hl
    linarith
  refine ⟨add_nonneg (le_max_right _ _) (le_max_right _ _),?_⟩
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₁)))
    (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₂)))]
  exact add_le_add (one U₁ b₁ h₁ hs₁) (one U₂ b₂ h₂ hs₂)

lemma profile_polynomial_survives (χ : Character) (V : Plain) (U : ℝ) (hU : 0<U)
    (t X σ v : ℝ) (hn : HeckeDyadic.polynomial χ false (V.profile U hU t) X σ v≠0) :
    1≤U*V.b := by
  by_contra hs
  rw [V.profile_zero U hU t (lt_of_not_ge hs)] at hn
  exact hn (by simp [HeckeDyadic.polynomial,HeckeDyadic.summand])

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def plainLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) : ℝ :=
  Real.logb Z (clippedScale (rawScale D a X₁ 0))+
    Real.logb Z (clippedScale (rawScale D a X₂ 1))

def remainingLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (P : ι→ℝ) : ℝ := ∑i∈liveIndices D a,Real.logb Z (P i)

def preVolume (s : Data ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

lemma selectedNorm_ge_one (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) :
    1≤selectedNorm D a := by
  have hn (j : Fin 2) : (1:ℝ)≤Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  exact one_le_mul_of_one_le_of_one_le (hn 0) (hn 1)

lemma remainingLogs_le (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (hZ : 1<Z) (P : ι→ℝ) (hP : ∀i,1≤P i) :
    remainingLogs D a Z P≤∑i,Real.logb Z (P i) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>Real.logb_nonneg hZ (hP i))

lemma raw_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (X₁ X₂ : ℝ) (P : ι→ℝ) (hP : ∀i,0<P i) :
    rawScale D a X₁ 0*rawScale D a X₂ 1*(∏i∈liveIndices D a,P i)=
      (X₁*X₂*∏i,P i)/formalReductionFactor D a P := by
  have hr : 0<formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>hP i))
  apply (eq_div_iff hr.ne').mpr
  simpa only [rawScale,div_mul_div_comm,rawRemaining,selectedNorm] using
    CenteredMomentDivisorRaw.raw_scale_identity D a (X₁*X₂) P

lemma raw_log_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) (P : ι→ℝ) (hP : ∀i,0<P i) :
    Real.logb Z (rawScale D a X₁ 0)+Real.logb Z (rawScale D a X₂ 1)+remainingLogs D a Z P=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P) := by
  have hr : 0<formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>hP i))
  have hh := congrArg (Real.logb Z) (raw_volume D a X₁ X₂ P hP)
  rw [Real.logb_div (mul_pos (mul_pos h₁ h₂) (Finset.prod_pos (fun i _=>hP i))).ne' hr.ne',
    Real.logb_mul (mul_pos (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)).ne'
      (Finset.prod_pos (fun i _=>hP i)).ne',
    Real.logb_mul (rawScale_pos D a X₁ h₁ 0).ne' (rawScale_pos D a X₂ h₂ 1).ne',
    Real.logb_prod _ _ (fun i _=>(hP i).ne')] at hh
  exact hh

theorem affine_exact (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,0<P i) :
    plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+
        clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) := by
  have hv := raw_log_volume D a Z X₁ X₂ h₁ h₂ P hP
  rw [plainLogs,clipped_pair_log Z _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)]
  nlinarith

omit [DecidableEq ι] in
lemma common_slot_logs_le (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (Z : ℝ) (hZ : 1<Z) (hP : ∀i,1≤s.P i) :
    (∑i : CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤
      ∑i,Real.logb Z (s.P i) := by
  rw [Finset.sum_coe_sort (CenteredMomentCommonProfile.liveIndices B.val) (fun i : ι=>Real.logb Z (s.P i))]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>Real.logb_nonneg hZ (hP i))

theorem excess_le_remaining (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,0<P i)
    (hs₁ : 1≤rawScale D a X₁ 0*b₁) (hs₂ : 1≤rawScale D a X₂ 1*b₂) :
    max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0≤
      max (Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+Real.logb Z (max 1 b₁*max 1 b₂)) 0 := by
  rw [affine_exact D a Z X₁ X₂ κ M hZ h₁ h₂ P hP]
  have hc := (clipping_loss_bound Z _ _ b₁ b₂ hZ
    (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂).2
  exact max_le_max (by linarith) le_rfl

end SevenEighths.CenteredMomentAllocatedChildCapacity

end

end OAI
