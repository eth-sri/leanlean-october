module

public import OAI.NumberTheory.DirichletL.Moments.FirstScale
public import OAI.NumberTheory.DirichletL.Moments.SectorLocalization
public import OAI.NumberTheory.DirichletL.Moments.FirstExtractedLedger

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstPhysicalLedger
open CenteredMomentFirstScale CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem nominal_log (I J E : Ideal ActualEisensteinCubic.O) (hE : E≠0)
    (Z H X : ℝ) (hH : 0<H) (hX : 0<X) :
    Real.logb Z (firstNominalScale I J E H X)=
      2*Real.logb Z X-Real.logb Z ((commonPart I J).absNorm:ℝ)-
        Real.logb Z ((commonPart J I).absNorm:ℝ)+
        Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)+
        Real.logb Z (E.absNorm:ℝ)-Real.logb Z H := by
  have hc:=norm_pos _ (commonPart_ne_zero I J)
  have hd:=norm_pos _ (commonPart_ne_zero J I)
  have he:=norm_pos E hE
  have hr:=active_norm_pos I J
  unfold firstNominalScale
  rw [Real.logb_div (by positivity)
      (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul he.ne' hr.ne',Real.logb_pow,
    Real.logb_mul (by positivity) hd.ne',Real.logb_mul hH.ne' hc.ne']
  ring

end SevenEighths.CenteredMomentFirstPhysicalLedger

end

end OAI
