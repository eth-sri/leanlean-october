module

public import OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
public import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedPadding

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification Filter IdealMobiusDivisorSum
open DetectorDictionaryInverseRawInitialGates


def shiftedExponent (_data:RowData)(U r:ℝ)(j:Ideal HeckeFamily.O)  :=
  r-Real.logb U (j.absNorm:ℝ)

theorem marked_shift_eventually  data  eta (heta:0<eta) :
    ∀ᶠU:ℝ in atTop,1<U ∧
      ∀j∈idealDivisors (∏P∈excluded data,P),∀r:ℝ,
        r-eta≤shiftedExponent data U r j ∧ shiftedExponent data U r j≤r ∧
        U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ) := by
  have ht:∀ᶠU:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤U^eta :=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with U hU ht
  refine ⟨hU,?_⟩
  intro j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hU0:0<U:=zero_lt_one.trans hU
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hl0:0≤Real.logb U (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hU).le
  have hl:Real.logb U (j.absNorm:ℝ)≤eta:=
    (Real.logb_le_iff_le_rpow hU hn0).mpr (hnB.trans ht)
  refine ⟨by dsimp [shiftedExponent];linarith,by dsimp [shiftedExponent];linarith,?_⟩
  rw [shiftedExponent,Real.rpow_sub hU0,Real.rpow_logb hU0 hU.ne' hn0]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
