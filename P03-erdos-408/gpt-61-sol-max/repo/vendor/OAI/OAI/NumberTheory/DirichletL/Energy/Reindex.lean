module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Energy.SlotHeight

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyReindex
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy


variable {α β:Type*}[Fintype α][Fintype β]

section
variable (e:α≃β) (η:Character)

lemma positive_reindex    m A z  W₁ W₂ 
     pool  coeff  P  t X₁ X₂ :
    positiveSlotRow η m A z W₁ W₂ (pool∘e) (coeff∘e) (P∘e) t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ pool coeff P t X₁ X₂:=by
  unfold positiveSlotRow
  simp only [Function.comp_apply,e.prod_comp P,
    e.prod_comp (fun i=>CenteredMomentHeckeSlots.rowSlot η m A z (pool i) (coeff i) t)]

theorem energy_reindex    m A  W₁ W₂ 
     pool  coeff  P  t X₁ X₂ 
     keep  Φ  K :
    energy η m A t W₁ W₂ (pool∘e) (coeff∘e) (P∘e) X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_reindex]

end

omit [Fintype α] [Fintype β] in
theorem energy_subset_map (e:α↪β)(T:Finset α)(η:Character)(m A:HeckeFamily.O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal HeckeFamily.O))(coeff:β→Ideal HeckeFamily.O→ℂ)(P:β→ℝ) t X₁ X₂ 
     keep  Φ  K :
    energy η m A t W₁ W₂ (fun i:T=>pool (e i)) (fun i:T=>coeff (e i))
      (fun i:T=>P (e i)) X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i:T.map e=>pool i) (fun i:T.map e=>coeff i)
      (fun i:T.map e=>P i) X₁ X₂ keep Φ K:=
  OAI.SevenEighths.CenteredMomentEnergyReindex.energy_reindex (Finset.equivMap e T) η m A W₁ W₂ (fun i => pool ↑i) (fun i => coeff ↑i) (fun i => P ↑i) t X₁ X₂ keep Φ K

end SevenEighths.CenteredMomentEnergyReindex



end OAI
