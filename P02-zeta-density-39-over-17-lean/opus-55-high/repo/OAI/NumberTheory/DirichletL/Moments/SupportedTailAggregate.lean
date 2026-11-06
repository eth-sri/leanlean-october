module
public import OAI.NumberTheory.DirichletL.Moments.SecondTail
public import OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate
public import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedTailAggregate
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondTail CenteredMomentFirstTailAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstScale CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O

private theorem pair_mass {α : Type*} [Fintype α] (c w : α → ℂ) (F : α → α → ℂ)
    (hw : ∀ i,‖w i‖≤1) (B : ℝ) (_hB : 0≤B)
    (hF : ∀ i j,c i≠0 → c j≠0 → ‖F i j‖≤B) :
    ‖∑ i,∑ j,((c i*w i)*star (c j*w j))*F i j‖≤(∑ i,‖c i‖)^2*B := by pm_2883

def secondDiscardedEnergy (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*heightCoeff η t I)*star (c J*heightCoeff η t J))*
      secondDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem second_discarded_energy_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤Real.exp H*X) →
      X^2/K≤Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedEnergy η t S c W K Tsec Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z ^(ξ/4))^Adec) := by
  pm_3085 s C hC ht second_discarded_pair_bound Adec
  intro η t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z ^(ξ/4))^Adec)
  pm_6949
  have hweight (I : supportedColumns S) : ‖heightCoeff η t I‖≤1 := by
    rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp I.property).2]
    exact rowWeight_norm_le_one η fixedBadMask 1 1 t I (Finset.mem_filter.mp I.property).2.1
  have hp := pair_mass (fun I : supportedColumns S => c I) (fun I=> heightCoeff η t I)
    (fun I J=> secondDiscardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ) hweight B hB
    (fun I J hi hj => ht W I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 K X H Tsec Z Csec ξ hK hX hZ hCs
      (hN I (Finset.mem_filter.mp I.property).1 hi) (hN J (Finset.mem_filter.mp J.property).1 hj) hsec hthreshold)
  pm_2884

end SevenEighths.CenteredMomentSupportedTailAggregate

end

end OAI
