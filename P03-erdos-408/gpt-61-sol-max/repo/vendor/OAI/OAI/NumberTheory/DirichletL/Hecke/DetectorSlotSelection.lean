module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountCrossing

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorSlotSelection

section
variable {α : Type*} (s : Finset α) (w g : α→ℝ)
include α s w g

section
variable (G mesh : ℝ) (hG : 0≤G) (hmesh : 0≤mesh) (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
include G mesh hG hmesh hw hwm

theorem whole_slots        
       
       
    (hg : ∀ i∈s, 0≤g i) (hgG : ∀ i∈s, g i≤G)
     q z  (hq : 0≤q) (hqG : q≤G) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*g i) :
    ∃ T : Finset α, T⊆s ∧ (∑ i∈T, w i)≤z ∧ q*z-G*mesh≤∑ i∈T, w i*g i := by
  classical
  induction s using Finset.strongInductionOn generalizing q z with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a,ha,hmax⟩ := s.exists_max_image g hs
      by_cases hza : z≤w a
      · refine ⟨∅,Finset.empty_subset _,by simpa using hz,?_⟩
        have hzmesh : z≤mesh := hza.trans (hwm a ha)
        have hprod := mul_le_mul hqG hzmesh hz hG
        simpa only [Finset.sum_empty] using (sub_nonpos.mpr hprod)
      have haz : w a<z := lt_of_not_ge hza
      let s' := s.erase a
      have hss : s'⊂s := Finset.erase_ssubset ha
      have hsub : s'⊆s := Finset.erase_subset a s
      have hsum : ∑ i∈s, w i=w a+∑ i∈s', w i := by
        simpa [s',add_comm] using (Finset.sum_erase_add s w ha).symm
      have hgain : ∑ i∈s, w i*g i=w a*g a+∑ i∈s', w i*g i := by
        simpa [s',add_comm] using (Finset.sum_erase_add s (fun i => w i*g i) ha).symm
      let W := ∑ i∈s', w i
      let A := ∑ i∈s', w i*g i
      have hW : 0<W := by rw [hsum] at hzs; dsimp [W]; linarith
      have hA : 0≤A := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i (hsub hi)) (hg i (hsub hi)))
      have hAg : A≤W*g a := by
        calc
          _ ≤ ∑ i∈s', w i*g a := Finset.sum_le_sum (fun i hi =>
            mul_le_mul_of_nonneg_left (hmax i (hsub hi)) (hw i (hsub hi)))
          _ = _ := by dsimp [W]; rw [Finset.sum_mul]
      let q' := A/W
      have hq' : 0≤q' := div_nonneg hA hW.le
      have hq'a : q'≤g a := (div_le_iff₀ hW).mpr (by simpa [mul_comm] using hAg)
      have hq'G : q'≤G := hq'a.trans (hgG a ha)
      have he : q'*W=A := div_mul_cancel₀ A hW.ne'
      have hz' : 0≤z-w a := sub_nonneg.mpr haz.le
      have hzs' : z-w a≤∑ i∈s', w i := by rw [hsum] at hzs; linarith
      obtain ⟨T,hTs,hTz,hTgain⟩ := ih s' hss
        (fun i hi => hw i (hsub hi)) (fun i hi => hwm i (hsub hi))
        (fun i hi => hg i (hsub hi)) (fun i hi => hgG i (hsub hi))
        q' (z-w a) hq' hq'G hz' hzs' he.le
      have haT : a∉T := fun h => (Finset.mem_erase.mp (hTs h)).1 rfl
      refine ⟨insert a T,Finset.insert_subset_iff.mpr ⟨ha,hTs.trans hsub⟩,?_,?_⟩
      · rw [Finset.sum_insert haT]
        linarith
      · rw [Finset.sum_insert haT]
        have hprefix : q*z≤w a*g a+q'*(z-w a) := by
          rw [hsum,hgain] at hmean
          change q*(w a+W)≤w a*g a+A at hmean
          rw [←he] at hmean
          by_cases hqq : q≤q'
          · have h1 := mul_le_mul_of_nonneg_right hqq hz
            have h2 := mul_le_mul_of_nonneg_left hq'a (hw a ha)
            nlinarith
          · have hqq' : 0≤q-q' := by linarith
            have h1 := mul_le_mul_of_nonneg_left hzs hqq'
            rw [hsum] at h1
            grind
        linarith
    · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      
      refine ⟨∅,Finset.empty_subset _,by simpa using hz,?_⟩
      nlinarith

theorem whole_positive_slots        
       
       
    (hgG : ∀ i∈s, g i≤G)
     q z  (hq : 0≤q) (hqG : q≤G) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0) :
    ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧
      (∑ i∈T, w i)≤z ∧ q*z-G*mesh≤∑ i∈T, w i*g i := by
  classical
  obtain ⟨T,hTs,hTz,hTgain⟩ := whole_slots s w (fun i => max (g i) 0) G mesh hG hmesh
    hw hwm (fun i hi => le_max_right _ _) (fun i hi => max_le (hgG i hi) hG)
    q z hq hqG hz hzs hmean
  let P := T.filter (fun i => 0<g i)
  have hPT : P⊆T := Finset.filter_subset _ _
  refine ⟨P,hPT.trans hTs,fun i hi => (Finset.mem_filter.mp hi).2,?_,?_⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hPT (fun i hi _ => hw i (hTs hi))).trans hTz
  · have he : (∑ i∈T, w i*max (g i) 0)=∑ i∈P, w i*g i := by
      calc
        _ = ∑ i∈P, w i*max (g i) 0 := by
          symm
          apply Finset.sum_subset hPT
          grind
        _ = _ := Finset.sum_congr rfl (fun i hi => by
          rw [max_eq_left (Finset.mem_filter.mp hi).2.le])
    rwa [he] at hTgain

end

theorem selected_product_spike      
     U δ mesh q z  (hU : 1≤U) (hδ : 0≤δ) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hg : ∀ i∈s, g i≤δ/2) (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0)
    : ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧ (∑ i∈T, w i)≤z ∧
      ∀ Q : α→ℂ, (∀ i∈s, 0<g i → U^(2*w i*g i)≤‖Q i‖^2) →
        U^(2*q*z-δ*mesh)≤‖∏ i∈T, Q i‖^2 := by
  obtain ⟨T,hTs,hTpos,hTz,hgain⟩ := whole_positive_slots s w g (δ/2) mesh
    (by positivity) hmesh hw hwm hg q z hq hqδ hz hzs hmean
  refine ⟨T,hTs,hTpos,hTz,?_⟩
  intro Q hQ
  have hUp : 0<U := by linarith
  calc
    _ ≤ U^(∑ i∈T, 2*w i*g i) := Real.rpow_le_rpow_of_exponent_le hU (by
      have he : (∑ i∈T, 2*w i*g i)=2*(∑ i∈T, w i*g i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      linarith)
    _ = ∏ i∈T, U^(2*w i*g i) := Real.rpow_sum_of_pos hUp _ _
    _ ≤ ∏ i∈T, ‖Q i‖^2 := Finset.prod_le_prod₀ (fun i hi => Real.rpow_nonneg hUp.le _)
      (fun i hi => hQ i (hTs hi) (hTpos i hi))
    _ = _ := by rw [norm_prod,Finset.prod_pow]

end

end SevenEighths.HeckeDetectorSlotSelection



end OAI
