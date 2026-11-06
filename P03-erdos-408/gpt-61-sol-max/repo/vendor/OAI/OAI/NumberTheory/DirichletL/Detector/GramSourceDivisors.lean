module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.GramCommonEnergy
public import OAI.NumberTheory.DirichletL.Detector.GramIdealMass

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
open CenteredMomentMobiusRegroup UniqueFactorizationMonoid

local notation "Id" => Ideal ActualEisensteinCubic.O

def sourceDivisors (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C : SupportedIdeal) : Finset SupportedIdeal :=
  (divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val).preimage
    Subtype.val Subtype.val_injective.injOn
lemma sourceDivisors_mem  W   hW   Y   hY   C D  :
    D∈sourceDivisors W hW Y hY C ↔
      D.val∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val := Finset.mem_preimage

def sourceDivisorUnion (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)  :=
  F.biUnion (sourceDivisors W hW Y hY)

def sourceMobiusWeight (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C D : SupportedIdeal)  :=
  if D∈sourceDivisors W hW Y hY C then (moebius D.val:ℂ) else 0
section
variable (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C D : SupportedIdeal) (hC : C∈F)

lemma sourceMobiusWeight_norm           :
    ‖sourceMobiusWeight W hW Y hY C D‖≤1 := by
  unfold sourceMobiusWeight
  split_ifs
  · exact CubicEisenstein.norm_ideal_moebius_le_one _
  · simp

lemma sourceDivisors_sum        
      (f : Id→ℂ) :
    (∑D∈sourceDivisors W hW Y hY C,f D.val)=
      ∑D∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val,f D := by
  apply Finset.sum_bij (fun D _=>D.val)
  · simp_all [sourceDivisors_mem]
  · intro D hD E hE h;exact Subtype.val_injective h
  · intro D hD
    refine ⟨⟨D,divisorPool_supported _ _ hD⟩,?_,rfl⟩
    exact (sourceDivisors_mem W hW Y hY C _).mpr hD
  · intro D hD;rfl

include hC in
lemma sourceMobiusWeight_rectangle      
            (f : SupportedIdeal→ℂ) :
    (∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*f D)=
      ∑D∈sourceDivisors W hW Y hY C,(moebius D.val:ℂ)*f D := by
  rw [←Finset.sum_subset (show sourceDivisors W hW Y hY C⊆sourceDivisorUnion F W hW Y hY from
    fun D hD=>Finset.mem_biUnion.mpr ⟨C,hC,hD⟩) (by simp_all [sourceMobiusWeight])]
  exact Finset.sum_congr rfl (fun D hD=>by rw [sourceMobiusWeight,ite_eq_left hD])

include hbad hC in
theorem originalCommonBlock_eq_rectangle    
             
     k   W   hW   Y Q   hY  (hQ : 0<Q)
     U   v  :
    originalCommonBlock S hS σ C k W hW Y Q hY U v=
      ∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*
        canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
          ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/gramIdealNorm C))
          (Y/(gramIdealNorm C*gramIdealNorm D)) := by
  rw [sourceMobiusWeight_rectangle F W hW Y hY C hC]
  rw [originalCommonBlock_eq_lattice S hS hbad σ C k W hW Y Q hY hQ U v]
  rw [←sourceDivisors_sum W hW Y hY C]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  rw [frequencyScale_ratio]
  congr 1
  simp only [commonResidualScale,gramIdealNorm,div_div]

end

end SevenEighths.ProbeGramCommon
end

end OAI
