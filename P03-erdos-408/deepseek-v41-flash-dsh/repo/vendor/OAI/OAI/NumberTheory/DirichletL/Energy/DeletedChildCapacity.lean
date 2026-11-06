module

public import OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity
public import OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityDefect

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyDeletedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedChildCapacity
open CenteredMomentRetainedProfile CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentDivisorRaw CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstSecondCapacityLedger CenteredMomentLiveCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma deletion_norm (F : Finset (Ideal O)) (hF : ∀I∈F,I≠0) :
    (1:ℝ) ≤ (∏I∈F,I).absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Finset.prod_ne_zero_iff.mpr hF))

def postmaskLength (Z U : ℝ) (F : Finset (Ideal O)) : ℝ :=
  length Z (clippedScale U/((∏I∈F,I).absNorm:ℝ))

lemma postmaskLength_le (Z U : ℝ) (F : Finset (Ideal O))
    (hZ : 1<Z) (hF : ∀I∈F,I≠0) :
    postmaskLength Z U F≤Real.logb Z (clippedScale U) :=
  postmask_length_le Z U _ hZ (deletion_norm F hF)

theorem child_survives (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0) :
    1≤rawScale D a X₁ 0*V₁.b ∧ 1≤rawScale D a X₂ 1*V₂.b := by
  unfold child at hne
  have hp:=left_ne_zero_of_mul hne
  exact ⟨profile_polynomial_survives χ V₁ _ (rawScale_pos D a X₁ h₁ 0) t _ 0 0
    (left_ne_zero_of_mul hp),
    profile_polynomial_survives χ V₂ _ (rawScale_pos D a X₂ h₂ 1) t _ 0 0
      (right_ne_zero_of_mul hp)⟩

def deletedExcess (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι) : ℝ :=
  excess (liveIndices D a\J) (fun i=>Real.logb Z (P i))
    (postmaskLength Z (rawScale D a X₁ 0) F₁)
    (postmaskLength Z (rawScale D a X₂ 1) F₂) M κ

lemma deletedExcess_le (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0) :
    deletedExcess D a Z X₁ X₂ κ M P F₁ F₂ J≤
      max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0 := by
  have h₁:=postmaskLength_le Z (rawScale D a X₁ 0) F₁ hZ hF₁
  have h₂:=postmaskLength_le Z (rawScale D a X₂ 1) F₂ hZ hF₂
  have hsum:(∑i∈liveIndices D a\J,Real.logb Z (P i))≤remainingLogs D a Z P :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _=>Real.logb_nonneg hZ (hP i))
  have hh:=mul_le_mul_of_nonneg_left hsum (by positivity : 0≤6*κ)
  unfold deletedExcess excess plainLogs
  exact max_le_max (by linarith) le_rfl

theorem child_excess_from_parent (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J≤
      max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0 := by
  obtain ⟨hs₁,hs₂⟩:=child_survives χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J hne
  apply (deletedExcess_le D a Z X₁ X₂ κ Mactual P F₁ F₂ J hZ hκ hP hF₁ hF₂).trans
  apply (excess_le_remaining D a Z X₁ X₂ V₁.b V₂.b κ Mactual hZ h₁ h₂ P
    (fun i=>zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le_max _ le_rfl
  have hr:=affine_reduction_le_parent D a Z κ hZ hκ P hP
  linarith

theorem child_paid_width (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ₁ δ₂ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth : Mactual-Mnom≤δ₂) (hw : 0≤w) (hell : 0≤ell)
    (hδ₁ : 0≤δ₁) (hδ₂ : 0≤δ₂) (hθ : 0≤θ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    Mactual+deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J/6≤
      Mnom+δ₂+w+ell+δ₁/6+θ/3 := by
  have he:=child_excess_from_parent χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
    w ell δ₁ θ h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hne hparent hshift hclip
  have hh:=width_defect_cost (Mactual-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mactual-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mactual by ring] at hh
  linarith

end SevenEighths.CenteredMomentEnergyDeletedChildCapacity

end

end OAI
