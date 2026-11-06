module
public import OAI.NumberTheory.DirichletL.Detector.GaussianDensityBudget
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianWeightedMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k R : ℝ) : ℝ := R^k*gaussianJointMoment V hV J R

section
variable (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ)
include V hV J
lemma gaussianWeightedMoment_nonneg (k R : ℝ) (hR : 0≤R) : 0≤gaussianWeightedMoment V hV J k R := by
  unfold gaussianWeightedMoment
  exact mul_nonneg (Real.rpow_nonneg hR _) (gaussianJointMoment_nonneg V hV J R)

lemma gaussianWeightedMoment_power_bound (k A : ℝ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→ gaussianWeightedMoment V hV J k R≤C*R^(-A) := by
  obtain ⟨C,hC,hb⟩ := gaussianJointMoment_power_bound V hV J (A+k)
  refine ⟨C,hC,?_⟩
  intro R hR
  have hh := mul_le_mul_of_nonneg_left (hb R hR) (Real.rpow_nonneg hR.le k)
  change R^k*gaussianJointMoment V hV J R≤_
  calc
    _ ≤ R^k*(C*R^(-(A+k))) := hh
    _ = C*R^(-A) := by
      rw [←mul_assoc,mul_comm (R^k) C,mul_assoc,←Real.rpow_add hR]
      congr 2
      ring

lemma gaussianWeightedMoment_polynomial_decay (k : ℝ) (N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→ gaussianWeightedMoment V hV J k R≤C/(1+R)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianWeightedMoment_power_bound V hV J k 0
  obtain ⟨C,hC,hdecay⟩ := gaussianWeightedMoment_power_bound V hV J k (N:ℝ)
  pm_3927

theorem gaussianWeightedMoment_summed (k s : ℝ) (hs : 0< s) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z))≤C*Z ^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  pm_3547 B hB hbound gaussianWeightedMoment_polynomial_decay V hV J k N
  pm_3930
  have hb (j : ℕ) : ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    pm_3929
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s) (gaussianWeightedMoment_nonneg V hV J k _ (by positivity))
  pm_3928
end

def gaussianRemoteMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (s Z A : ℝ) (j : ℕ) : ℝ :=
  if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
    ((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)
  else 0

theorem gaussianRemoteMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J N : ℕ) (s : ℝ) (hs : 0< s) :
    ∃C : ℝ,0<C ∧ ∀Z A : ℝ,0<Z→1≤A→
      Summable (gaussianRemoteMoment V hV J s Z A) ∧
      (∑'j : ℕ,gaussianRemoteMoment V hV J s Z A j)≤C*Z ^s/A^N := by
  obtain ⟨Cm,hCm,hm⟩ := gaussianWeightedMoment_summed V hV J (-(N:ℝ)) s hs
  obtain ⟨Cp,hCp,hp⟩ := gaussianWeightedMoment_summed V hV J (N:ℝ) s hs
  refine ⟨Cm+Cp,by positivity,?_⟩
  intro Z A hZ hA
  have hAp : 0<A := lt_of_lt_of_le zero_lt_one hA
  have hAN : 0<A^N := pow_pos hAp N
  obtain ⟨hsm,htm⟩ := hm Z hZ
  obtain ⟨hsp,htp⟩ := hp Z hZ
  let U : ℕ→ℝ := fun j=>
    (((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z)+
      ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z))/A^N
  have hU : Summable U := (hsm.add hsp).div_const _
  have hnon (j : ℕ) : 0≤gaussianRemoteMoment V hV J s Z A j := by
    unfold gaussianRemoteMoment
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianJointMoment_nonneg V hV J _)
    · rfl
  have hb (j : ℕ) : gaussianRemoteMoment V hV J s Z A j≤U j := by
    let R := (2:ℝ)^j/Z
    have hR : 0<R := div_pos (by positivity) hZ
    have hM : 0≤gaussianJointMoment V hV J R := gaussianJointMoment_nonneg V hV J R
    unfold gaussianRemoteMoment
    split_ifs with hj
    · have he : A^N≤R^(-(N:ℝ))+R^(N:ℝ) := by
        rcases hj with hlo|hhi
        · have hra : R*A≤1 := (le_div_iff₀ hAp).mp (by simpa only [one_div,R] using hlo)
          have hh := pow_le_pow_left₀ (by positivity : 0≤R*A) hra N
          rw [mul_pow,one_pow] at hh
          have hi : A^N≤R^(-(N:ℝ)) := by
            rw [Real.rpow_neg hR.le,Real.rpow_natCast]
            rw [←one_div]
            exact (le_div_iff₀ (pow_pos hR N)).mpr (by simpa only [mul_comm] using hh)
          exact hi.trans (le_add_of_nonneg_right (Real.rpow_nonneg hR.le _))
        · have hi : A^N≤R^(N:ℝ) := by
            rw [Real.rpow_natCast]
            exact pow_le_pow_left₀ hAp.le hhi N
          exact hi.trans (le_add_of_nonneg_left (Real.rpow_nonneg hR.le _))
      change ((2:ℝ)^j)^s*gaussianJointMoment V hV J R≤_
      dsimp only [U]
      apply (le_div_iff₀ hAN).mpr
      calc
        _ ≤ (((2:ℝ)^j)^s*gaussianJointMoment V hV J R)*(R^(-(N:ℝ))+R^(N:ℝ)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg (by positivity) _) hM)
        _ = _ := by unfold gaussianWeightedMoment;dsimp only [R];ring
    · dsimp only [U]
      apply div_nonneg _ hAN.le
      exact add_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
  have hsum := Summable.of_nonneg_of_le hnon hb hU
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,U j := hsum.tsum_le_tsum hb hU
    _ = ((∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z))+
        (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z)))/A^N := by
      dsimp only [U]
      rw [tsum_div_const,hsm.tsum_add hsp]
    _ ≤ (Cm*Z ^s+Cp*Z ^s)/A^N := div_le_div_of_nonneg_right (add_le_add htm htp) hAN.le
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI
