module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.CenteredExceptionalCount

public import OAI.NumberTheory.DirichletL.Moments.SecondBlockAggregate
public import OAI.NumberTheory.DirichletL.Moments.SecondActiveCount
public import OAI.NumberTheory.DirichletL.Moments.DyadicCount

@[expose] public section

namespace OAI


open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondBlockCount
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondWholeKernel
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition
open CenteredMomentSecondBlockAggregate CenteredMomentSecondActiveCount
open CenteredMomentSecondSectorFrequency CenteredMomentSecondRetainedRows
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondSectorColumns CenteredMomentSecondRetainedAggregate
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentDyadicCount
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentActiveSource


section
variable (B L Cr Z ε : ℝ) (hB : 0≤B) (hL : 0≤L) (_hCr : 0<Cr) (hZ : 1≤Z) (C D : Ideal ActualEisensteinCubic.O) (hC : C≠0) (hD : D≠0) (A : ActualEisensteinCubic.O) (hA : A≠0) (K R H : ℝ)

lemma ideal_norm_ge_one (I : Ideal ActualEisensteinCubic.O) (hI : I≠0) : (1:ℝ)≤Ideal.absNorm I := by solve_by_elim [_root_.OAI.SevenEighths.CenteredExceptionalCount.norm_one_le]

lemma sourceLower_le_upper       :
    ∀i,sourceLower C D A K i≤sourceUpper C D A K R H i := by
  intro i
  fin_cases i
  · exact le_rfl
  all_goals exact le_max_left _ _

include hB hL _hCr hZ hC hD hA in
lemma source_ratio_bound      
       
             
      (hK : 0<K) (hR : R≤Cr*Z^L) (hH : H≤Z^B) :
    ∀i,sourceUpper C D A K R H i/sourceLower C D A K i≤
      max 1 (4*Cr)*Z^(B+L) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^(B+L) := Real.one_le_rpow hZ (add_nonneg hB hL)
  have hc : 1≤max 1 (4*Cr) := le_max_left _ _
  have hq : 1≤max 1 (4*Cr)*Z^(B+L) := one_le_mul_of_one_le_of_one_le hc hp
  have hN := normValue_ge_one A hA
  have hNC := ideal_norm_ge_one C hC
  have hND := ideal_norm_ge_one D hD
  have hBpow : Z^B≤Z^(B+L) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hLpow : Z^L≤Z^(B+L) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hH' : H≤max 1 (4*Cr)*Z^(B+L) :=
    hH.trans (hBpow.trans (le_mul_of_one_le_left (zero_le_one.trans hp) hc))
  have hR' : 4*R≤max 1 (4*Cr)*Z^(B+L) := by
    calc
      _≤4*Cr*Z^L := by linarith
      _≤max 1 (4*Cr)*Z^(B+L) :=
        mul_le_mul (le_max_right _ _) hLpow (Real.rpow_nonneg hz.le _) (by positivity)
  have hn (x d : ℝ) (hd : 1≤d) (hx : x≤max 1 (4*Cr)*Z^(B+L)) :
      max 1 (x/d)≤max 1 (4*Cr)*Z^(B+L) := by
    apply max_le hq
    apply (div_le_iff₀ (zero_lt_one.trans_le hd)).mpr
    exact hx.trans (le_mul_of_one_le_right (by positivity) hd)
  intro i
  fin_cases i
  · simpa [sourceUpper,sourceLower,
      div_self (secondEffectiveScale_pos C D hC hD A hA K hK).ne'] using hq
  · simpa [sourceUpper,sourceLower] using hn (4*R) (normValue A) hN hR'
  · simpa [sourceUpper,sourceLower] using hn H (Ideal.absNorm C) hNC hH'
  · simpa [sourceUpper,sourceLower] using hn H (Ideal.absNorm D) hND hH'

include hB hL in
theorem sourceBlocks_subpower      
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃D₀:ℝ,0<D₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D:Ideal ActualEisensteinCubic.O),Supported C → Supported D →
      ∀(U:Finset (CommonIndex C D))(K R H:ℝ),0<K →
      R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (SourceBlocks C D U K R H):ℝ)≤D₀*Z^ε := by
  obtain ⟨D₀,hD₀,hcount⟩ := four_indices_subpower (max 1 (4*Cr)) (B+L) ε
    (le_max_left _ _) (add_nonneg hB hL) hε
  refine ⟨D₀,hD₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hc hZ
  intro C D hC hD U K R H hK hR hH
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)
  exact hc _ _ (sourceLower_pos C D hC.1 hD.1 _ hA K hK)
    (sourceLower_le_upper C D _ K R H)
    (source_ratio_bound B L Cr Z hB hL hCr hZ C D hC.1 hD.1 _ hA K R H hK hR hH)

lemma commonSubset_support   (U : Finset (CommonIndex C D)) :
    U.image Subtype.val⊆IdealMobiusDivisorSum.primeSupport (commonRadical C D) := by
  intro P hP
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
  rw [commonRadical_support]
  exact Q.property

end

end SevenEighths.CenteredMomentSecondBlockCount



end OAI
