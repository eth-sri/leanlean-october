module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Energy.Bands
public import OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergySlotHeight
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentCommonMaskEnergy
open HeckePrimeAnnular CenteredMomentPrimeSlotShift


variable {α:Type*}[Fintype α]

lemma height_coefficient (ν:Ideal HeckeFamily.O→ℂ) W  P σ freq t (hP:0<P)
     I (hI:I≠0):
    heightCoefficient (fun J=>ν J*annularWeight W P σ freq J) t I=
      (P:ℂ)^(Complex.I*t)*(ν I*annularWeight W P σ (t+freq) I):=by
  have hN:0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hh:=norm_height_split (I.absNorm:ℝ) P σ t freq hN hP
  unfold heightCoefficient annularWeight
  calc
    _=(ν I*W ((I.absNorm:ℝ)/P))*
      (((((I.absNorm:ℝ)/P:ℝ):ℂ)^(-HeckeDyadic.shift σ freq))*(I.absNorm:ℂ)^(Complex.I*t)):=by ring
    _=_:=by rw [show (I.absNorm:ℂ)=((I.absNorm:ℝ):ℂ) by simp,hh];ring

lemma row_slot_phase (η:Character)(m A z:HeckeFamily.O)(pool:Finset (Ideal HeckeFamily.O))
    (β γ:Ideal HeckeFamily.O→ℂ) phase  t (he:∀I∈pool,β I=phase*γ I):
    rowSlot η m A z pool β t=phase*rowSlot η m A z pool γ t:=by
  unfold rowSlot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [he I hI]
  ring

section
variable (η : Character) (m A z : HeckeFamily.O) (W₁ W₂ : ℝ→ℂ) (pool : α→Finset (Ideal HeckeFamily.O)) (β γ : α→Ideal HeckeFamily.O→ℂ) (phase : α→ℂ) (ν : α→Ideal HeckeFamily.O→ℂ) (W : α→ℝ→ℂ) (P σ freq : α→ℝ) (hP : ∀i,0<P i) (hpool : ∀i I,I∈pool i→I≠0) (t rowt X₁ X₂ : ℝ) (keep : HeckeFamily.O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (he : ∀i I,I∈pool i→β i I=phase i*γ i I)


include he in
lemma positive_row_phase    
        
      :
    positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      (∏i,phase i)*positiveSlotRow η m A z W₁ W₂ pool γ P t X₁ X₂:=by
  have hs (i:α):rowSlot η m A z (pool i) (β i) t=
      phase i*rowSlot η m A z (pool i) (γ i) t:=
    row_slot_phase η m A z (pool i) (β i) (γ i) (phase i) t (he i)
  unfold positiveSlotRow
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  ring

include he in
theorem energy_phase    
        
        
     (hp:∀i,‖phase i‖=1):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool γ P X₁ X₂ keep Φ K:=by
  have hprod:‖∏i,phase i‖=1:=by rw [norm_prod];simp only [hp,Finset.prod_const_one]
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_row_phase η m A z W₁ W₂ pool β γ phase P t X₁ X₂ he]
  simp only [norm_mul,hprod,one_mul]

include hP hpool in
theorem inherited_height_energy    
       
       
        :
    energy η m A rowt W₁ W₂ pool
      (fun i=>heightCoefficient (fun I=>ν i I*annularWeight (W i) (P i) (σ i) (freq i) I) t)
      P X₁ X₂ keep Φ K=
    energy η m A rowt W₁ W₂ pool
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+freq i) I)
      P X₁ X₂ keep Φ K:=by
  apply energy_phase η m A W₁ W₂ pool _ _ (fun i=>(P i:ℂ)^(Complex.I*t)) P rowt X₁ X₂ keep Φ K
  · intro i I hi
    solve_by_elim [height_coefficient]
  · intro i
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (hP i) (Complex.I*t)

end

end SevenEighths.CenteredMomentEnergySlotHeight



end OAI
