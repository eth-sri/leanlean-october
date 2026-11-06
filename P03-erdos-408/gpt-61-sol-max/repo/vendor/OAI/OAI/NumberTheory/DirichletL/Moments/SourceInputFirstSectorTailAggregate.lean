module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.Moments.SupportedTailAggregate

public import OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailPair
public import OAI.NumberTheory.DirichletL.Moments.FirstSectorLocalization

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstTailAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstScale CenteredMomentSectorLocalization CenteredMomentHeckeExpansion


private theorem pair_mass {α : Type*} [Fintype α] (c w : α → ℂ) (F : α → α → ℂ)
    (hw : ∀ i,‖w i‖≤1)  B  (_hB : 0≤B)
    (hF : ∀ i j,c i≠0 → c j≠0 → ‖F i j‖≤B) :
    ‖∑ i,∑ j,((c i*w i)*star (c j*w j))*F i j‖≤(∑ i,‖c i‖)^2*B := by solve_by_elim [_root_.SharedProofs.shared_pair_mass]

theorem local_discarded_energy_bound  Adec  (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (m A : ActualEisensteinCubic.O) (t : ℝ) (S : Finset (Ideal ActualEisensteinCubic.O)) (c : Ideal ActualEisensteinCubic.O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤Real.exp H*X) →
      X^2/K≤Tsec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A t S c W K X Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*(Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := local_discarded_pair_bound Adec ε hε
  refine ⟨s,C,hC,?_⟩
  intro η m A t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := (Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤B := by dsimp only [B];positivity
  have hpair (I J : supportedColumns S) (hi : c I≠0) (hj : c J≠0) :
      ‖CenteredMomentFirstSectorLocalization.discardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ‖≤B := by
    have hni := hN I (Finset.mem_filter.mp I.property).1 hi
    have hnj := hN J (Finset.mem_filter.mp J.property).1 hj
    apply (ht W I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
      K X H Tsec Z Csec ξ hK hX hZ hCs hni hnj hsec hthreshold).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hni hε.le) hK.le
  have hp := pair_mass (fun I : supportedColumns S => c I)
    (fun I => CenteredMomentHeckeExpansion.rowWeight η m A 1 t I)
    (fun I J => CenteredMomentFirstSectorLocalization.discardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K X Z ξ)
    (fun I => rowWeight_norm_le_one η m A 1 t I (Finset.mem_filter.mp I.property).2.1) B hB hpair
  have hm : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  apply hp.trans
  convert mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (show 0 ≤ ∑ I : supportedColumns S, ‖c I‖ from
      Finset.sum_nonneg (fun I _ => norm_nonneg (c I))) hm 2) hB using 1 ; dsimp only [B];ring

end SevenEighths.CenteredMomentSourceInputFirstSectorTail



end OAI
