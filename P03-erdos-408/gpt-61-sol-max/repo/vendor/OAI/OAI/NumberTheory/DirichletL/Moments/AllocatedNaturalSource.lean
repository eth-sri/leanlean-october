module

public import Mathlib.RingTheory.Radical.Basic
public import OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy
public import OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy
public import OAI.NumberTheory.DirichletL.Moments.CommonRadialData

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentAllocatedNaturalSource
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained


structure Plain where
  W : ℝ→ℂ
  a : ℝ
  b : ℝ
  a_pos : 0<a
  support : Function.support W⊆Set.Icc a b
  smooth : ContDiff ℝ ∞ W

def Plain.profile (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ)  :=
  if h : 1≤U*V.b then retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t else 0

lemma Plain.profile_retained (V : Plain)  U   hU   t   h  :
    V.profile U hU t=retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t := by
  simp [Plain.profile,h]

lemma Plain.profile_zero (V : Plain)  U   hU   t  (h : U*V.b<1) :
    V.profile U hU t=0 := by simp [Plain.profile,not_le.mpr h]

lemma polynomial_zero  χ   X  :
    HeckeDyadic.polynomial χ false (0 : 𝓢(ℝ,ℂ)) X 0 0=0 := by
  simp [HeckeDyadic.polynomial,HeckeDyadic.summand]

theorem retained_normalized (η : Character) (z : HeckeFamily.O) (hz : z≠0) (R : Ideal HeckeFamily.O) (hR : R≠0)
    {α : Type*} [Fintype α] [DecidableEq α] (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal HeckeFamily.O))  β   P  (hP : ∀i,0<P i)
     t U₁ U₂   hU₁   hU₂  :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z V₁.W V₂.W pool β P t U₁ U₂=
      (((clippedScale U₁):ℂ)^(Complex.I*t)*((clippedScale U₂):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile U₁ hU₁ t) (clippedScale U₁) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile U₂ hU₂ t) (clippedScale U₂) 0 0 *
         ∏i,naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  by_cases h₁ : 1≤U₁*V₁.b
  · by_cases h₂ : 1≤U₂*V₂.b
    · rw [V₁.profile_retained U₁ hU₁ t h₁,V₂.profile_retained U₂ hU₂ t h₂]
      exact original_retained_normalized (naturalRow η z hz) R hR _ _ _ _ _ _ V₁.a_pos V₂.a_pos
        V₁.support V₂.support V₁.smooth V₂.smooth pool β P hP t U₁ U₂ hU₁ hU₂ h₁ h₂
    · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
        (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
        (Or.inr (lt_of_not_ge h₂)),V₂.profile_zero U₂ hU₂ t (lt_of_not_ge h₂),polynomial_zero]
      simp
  · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
      (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
      (Or.inl (lt_of_not_ge h₁)),V₁.profile_zero U₁ hU₁ t (lt_of_not_ge h₁),polynomial_zero]
    simp

variable {α : Type*} [Fintype α] [DecidableEq α]

def rawScale (D ) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) (X : ℝ) (j : Fin 2)  :=
  X/Ideal.absNorm (selectedPlain D a j)

lemma rawScale_pos (D : Ideal HeckeFamily.O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
     X  (hX : 0<X)  j  : 0<rawScale D a X j := by
  apply div_pos hX
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D Finset.univ a _))

theorem allocated_normalized (η : Character) (z : HeckeFamily.O) (hz : z≠0) (R : Ideal HeckeFamily.O) (hR : R≠0)
    (D : Ideal HeckeFamily.O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain)  pool   β   P  (hP : ∀i,0<P i)
     t X₁ X₂   hX₁   hX₂  :
    allocatedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂=
      (((clippedScale (rawScale D a X₁ 0)):ℂ)^(Complex.I*t)*
       ((clippedScale (rawScale D a X₂ 1)):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (clippedScale (rawScale D a X₁ 0)) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t) (clippedScale (rawScale D a X₂ 1)) 0 0 *
         ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
           (pool i) (heightCoefficient (β i) t) (P i)) := by
  have h:=retained_normalized η z hz R hR V₁ V₂
    (fun i : liveIndices D a=>pool i) (fun i : liveIndices D a=>β i) (fun i : liveIndices D a=>P i)
    (fun i=>hP i) t _ _ (rawScale_pos D a X₁ hX₁ 0) (rawScale_pos D a X₂ hX₂ 1)
  have hp': (∏i : liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i))=
      ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i) := Finset.prod_coe_sort (liveIndices D a) (fun i : α=>naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i))
  rw [hp'] at h
  exact h

omit [Fintype α] [DecidableEq α] in

theorem slot_controls (ν : α→Ideal HeckeFamily.O→ℂ) (W : α→ℝ→ℂ) (P b M : α→ℝ)
    (hP : ∀i,0<P i) (hν : ∀i I,‖ν i I‖≤1)
    (hW : ∀i x,‖W i x‖≤M i) (hs : ∀i,Function.support (W i)⊆Set.Iic (b i)) :
    (∀i I,‖ν i I*W i ((I.absNorm:ℝ)/P i)‖≤M i) ∧
    (∀i I,ν i I*W i ((I.absNorm:ℝ)/P i)≠0 → (I.absNorm:ℝ)≤b i*P i) := by
  constructor
  · intro i I
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hν i I) (norm_nonneg _)).trans (by simpa using hW i _)
  · intro i I hn
    exact (div_le_iff₀ (hP i)).mp (hs i (right_ne_zero_of_mul hn))

def SharedBound (F : Finset α) (b M : α→ℝ) (C ε : ℝ)  :=
    ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal HeckeFamily.O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal HeckeFamily.O))(β : ι→α→Ideal HeckeFamily.O→ℂ)(P : ι→α→ℝ),
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
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

lemma primeSupport_product_radical  R  (hR : R≠0) :
    (∏I∈CompletedGauss.primeSupport R,I)=R.radical := by
  ext x
  change x∈(∏I∈CompletedGauss.primeSupport R,I) ↔ ∃n : ℕ,x^n∈R
  simp_rw [←Ideal.span_singleton_le_iff_mem,←Ideal.dvd_iff_le,←Ideal.span_singleton_pow]
  exact (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd hR).symm

def child (χ : Character) (D ) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal HeckeFamily.O)) (β : α→Ideal HeckeFamily.O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (D₁ D₂ : Finset (Ideal HeckeFamily.O)) (J : Finset α)  :=
  HeckeDyadic.polynomial χ false (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
  HeckeDyadic.polynomial χ false (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
  ∏i∈liveIndices D a\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)

structure Slots (α : Type*) (b M : α→ℝ) where
  pool : α→Finset (Ideal HeckeFamily.O)
  ν : α→Ideal HeckeFamily.O→ℂ
  W : α→ℝ→ℂ
  P : α→ℝ
  prime : ∀i,∀I∈pool i,Prime I
  P_pos : ∀i,0<P i
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤M i
  support : ∀i,Function.support (W i)⊆Set.Iic (b i)

def Slots.coefficient {b M } (s : Slots α b M) (i : α) (I : Ideal HeckeFamily.O)  :=
  s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)

omit [Fintype α] [DecidableEq α] in
lemma Slots.controls {b M : α→ℝ} (s : Slots α b M) :
    (∀i I,‖s.coefficient i I‖≤M i) ∧
    (∀i I,s.coefficient i I≠0 → (I.absNorm:ℝ)≤b i*s.P i) :=
  slot_controls s.ν s.W s.P b M s.P_pos s.ν_bound s.W_bound s.support



def commonSlots (s : CenteredMomentCommonRadialData.Input α) (C : Ideal HeckeFamily.O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    Slots (CenteredMomentCommonProfile.liveIndices B.val) (fun i=>s.hi i) (fun i=>s.M i) where
  pool:=fun i=>s.slots i
  ν:=fun i=>s.ν i
  W:=fun i=>s.W i
  P:=fun i=>s.P i
  prime:=fun i=>s.prime i
  P_pos:=fun i=>s.P_pos i
  ν_bound:=fun i=>s.ν_bound i
  W_bound:=fun i=>s.W_bound i
  support:=fun i _ hx=>(s.support i hx).2

end SevenEighths.CenteredMomentAllocatedNaturalSource

end

end OAI
