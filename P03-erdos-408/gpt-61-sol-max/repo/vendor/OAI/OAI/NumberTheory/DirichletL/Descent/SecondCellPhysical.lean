module

public import OAI.NumberTheory.DirichletL.Descent.PriorityProfile
public import OAI.NumberTheory.DirichletL.Inversion.SecondSourceBlocks

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration


def secondCellColumnExponent (Z X:ℝ) (d:BlockIndex) :=
  Real.logb Z (X/(scales d 0*scales d 2))

section
variable (Z X b : ℝ) (d : BlockIndex) (hZ : 1<Z) (hX : 0<X)

include hZ hX in
theorem second_cell_column_scale         :
    Z^(secondCellColumnExponent Z X d)=X/(scales d 0*scales d 2) := Real.rpow_logb (by linarith) (ne_of_gt hZ)
    (div_pos hX (mul_pos (dyadScale_pos _) (dyadScale_pos _)))

include hZ hX in
theorem second_cell_physical_scale         :
    scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d)=X := by
  rw [second_cell_column_scale Z X d hZ hX]
  field_simp [scales,ne_of_gt (dyadScale_pos (d 0)),ne_of_gt (dyadScale_pos (d 2))]

include hZ hX in
theorem second_cell_clipping_ratio        
    (hb:1≤b) (hsource:scales d 0*scales d 2≤b*X) :
    1≤Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d) ∧
    Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d)≤b := by
  let N:=secondCellColumnExponent Z X d
  have hz:0<Z:=lt_trans zero_lt_one hZ
  have hn:Z^N=X/(scales d 0*scales d 2):=second_cell_column_scale Z X d hZ hX
  constructor
  · exact Real.one_le_rpow hZ.le (sub_nonneg.mpr (le_max_right _ _))
  · by_cases hN:0≤N
    · rw [max_eq_right hN,sub_self,Real.rpow_zero];exact hb
    · have hN':N≤0:=le_of_not_ge hN
      rw [max_eq_left hN',zero_sub,Real.rpow_neg hz.le,hn,inv_div]
      exact (div_le_iff₀ hX).mpr hsource

end

theorem actual_source_block_ratios {ι:Type*} [DecidableEq ι]
    (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))  d 
    (hcell:∀x∈source,index p x=d) (hk:∀x∈source,x.second.frequency≠0) :
    ∀x∈source,∀i,InverseSecondChildWindows.actualOuterRatios p x
      (scales d 0) (scales d 1) (scales d 2) (scales d 3) i∈Set.Icc 1 2 := by
  intro x hx i
  have hxcell:x∈cell p source d:=(mem_cell p source d x).mpr ⟨hx,hcell x hx⟩
  have hr:=cell_ratios p hp source hk d x hxcell i
  have he:InverseSecondChildWindows.actualOuterRatios p x
      (scales d 0) (scales d 1) (scales d 2) (scales d 3) i=outerNorms p x i/scales d i := by
    fin_cases i <;> simp [InverseSecondChildWindows.actualOuterRatios,outerNorms,
      primeSubsetGenerator_norm_eq_productNorm]
  rw [he]
  exact ⟨hr.1,hr.2.le⟩

end SevenEighths.InverseMoment

end

end OAI
