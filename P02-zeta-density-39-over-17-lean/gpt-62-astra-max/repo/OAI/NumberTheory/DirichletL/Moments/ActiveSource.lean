module
public import OAI.NumberTheory.DirichletL.Moments.SecondLocalization

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentActiveSource
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentLiveDomain CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentFirstSectors CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

def activeSource (S : Finset (Ideal O)) (β : Ideal O → ℂ) : Finset (Ideal O) :=
  S.filter (fun I => β I≠0)

@[simp] theorem mem_activeSource (S : Finset (Ideal O)) (β : Ideal O → ℂ) (I : Ideal O) :
    I∈activeSource S β ↔ I∈S ∧ β I≠0 := Finset.mem_filter

theorem supportedColumns_active (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    supportedColumns (activeSource S β)=(supportedColumns S).filter (fun I => β I≠0) := by
  ext I
  simp only [supportedColumns,activeSource,Finset.mem_filter]
  tauto

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then
    secondRetainedPair I J hI hJ W K T Z ξ else 0 else 0

theorem secondRetainedEnergy_eq_sum (η : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t S β W K T Z ξ=
      ∑I∈supportedColumns S,∑J∈supportedColumns S,
        ((β I*CenteredMomentHeckeColumnWindow.heightCoeff η t I)*
          star (β J*CenteredMomentHeckeColumnWindow.heightCoeff η t J))*
          retainedKernel I J W K T Z ξ := by
  unfold secondRetainedEnergy
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [retainedKernel,dite_eq_left (Finset.mem_filter.mp I.property).2,
    dite_eq_left (Finset.mem_filter.mp J.property).2]

theorem secondRetainedEnergy_active (η : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t (activeSource S β) β W K T Z ξ=
      secondRetainedEnergy η t S β W K T Z ξ := by
  rw [secondRetainedEnergy_eq_sum,secondRetainedEnergy_eq_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : β I=0
  · simp [hi]
  · rw [ite_eq_left hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj : β J=0 <;> simp [hj]

theorem commonLabel_witnesses (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (h : (C,D)∈commonLabels (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β))) :
    ∃I∈S,∃J∈S,Supported I ∧ Supported J ∧ β I≠0 ∧ β J≠0 ∧
      commonPart I J=C ∧ commonPart J I=D := by
  obtain ⟨⟨I,J⟩,hp,he⟩ := Finset.mem_image.mp h
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hp
  obtain ⟨hi,hIs⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj,hJs⟩ := Finset.mem_filter.mp hj
  obtain ⟨hi,hβi⟩ := mem_activeSource S β I |>.mp hi
  obtain ⟨hj,hβj⟩ := mem_activeSource S β J |>.mp hj
  exact ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,(Prod.mk.inj he).1,(Prod.mk.inj he).2⟩

theorem commonLabel_norm_bounds (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (h : (C,D)∈commonLabels (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β))) :
    (Ideal.absNorm C:ℝ)≤H ∧ (Ideal.absNorm D:ℝ)≤H := by
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩ := commonLabel_witnesses S β C D h
  constructor
  · rw [←hC]
    exact (Nat.cast_le.mpr (absNorm_commonPart_le I J hIs.1)).trans (hH I hi hβi)
  · rw [←hD]
    exact (Nat.cast_le.mpr (absNorm_commonPart_le J I hJs.1)).trans (hH J hj hβj)

theorem residualPool_data (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C : Ideal O) (hC : C≠0) (a : Ideal O)
    (ha : a∈residualPool C hC (supportedColumns (activeSource S β))) :
    C*a∈S ∧ β (C*a)≠0 ∧ Supported (C*a) ∧ a≠0 ∧
      1≤(Ideal.absNorm a:ℝ) ∧ (Ideal.absNorm a:ℝ)≤H/(Ideal.absNorm C:ℝ) := by
  have hm := (mem_residualPool C hC _ a).mp ha
  obtain ⟨hm,hsa⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm,hβ⟩ := (mem_activeSource S β (C*a)).mp hm
  have ha0 : a≠0 := right_ne_zero_of_mul hsa.1
  have hpos := CenteredMomentFirstScale.norm_pos C hC
  have hab := hH (C*a) hm hβ
  rw [map_mul,Nat.cast_mul] at hab
  refine ⟨hm,hβ,hsa,ha0,?_,?_⟩
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ha0)
  · exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hab)

end SevenEighths.CenteredMomentActiveSource

end

end OAI
