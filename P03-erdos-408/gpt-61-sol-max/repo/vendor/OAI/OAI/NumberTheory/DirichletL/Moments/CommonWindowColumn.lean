module

public import OAI.NumberTheory.DirichletL.Moments.ExceptionalWholeWindow
public import OAI.NumberTheory.DirichletL.Moments.CommonPairedSource
public import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentCommonWindowColumn
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentExceptionalWholeWindow CenteredMomentSmooth

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def columns (s:Input ι)(C)(hC:Supported C):=
  residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))

def coefficient (s:Input ι)(C)(hC)(R seed L:Ideal HeckeFamily.O)
    (I:supportedColumns (columns s C hC)):=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*
    (if IsCoprime C (I:Ideal HeckeFamily.O) ∧ L∣(I:Ideal HeckeFamily.O) then
      finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I) else 0)

def windowColumn (s:Input ι)(C)(hC:Supported C)(R seed L:Ideal HeckeFamily.O)
    (η:Character)(t θ X:ℝ)(V:ℝ→ℂ)(z:HeckeFamily.O):=
  rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
    (fun I=>coefficient s C hC R seed L I*heightCoeff η t I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Ideal HeckeFamily.O):ℝ)/X)) θ) z

omit [DecidableEq ι] in
theorem coefficient_polynomial (s:Input ι) C  hC  R seed L 
     η  t  z :
    rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
      (fun I=>coefficient s C hC R seed L I*heightCoeff η t I) z=
      normalizedColumn (withHeight s η t) C hC R seed L z:=by
  unfold normalizedColumn sourceColumn
  dsimp only [withHeight,Input.pools,columns]
  simp only [coefficient,mul_assoc,rowPolynomial_factor,Input.pools,columns]
  rfl

theorem sourceGenerator_span  S  I :
    Ideal.span {sourceGenerator S I}=(I:Ideal HeckeFamily.O):=
  primary_span_supported I (Finset.mem_filter.mp I.property).2

omit [DecidableEq ι] in
theorem whole_window_pair (s v:Input ι)(C D:Ideal HeckeFamily.O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal HeckeFamily.O)(Ds:Finset (Ideal HeckeFamily.O))(μ:Ideal HeckeFamily.O→ℂ) rows 
     η τ  t₁ t₂ θ₁ θ₂ X Y (hX:0<X)(hY:0<Y)
     V₁ V₂  hc₁  hc₂ 
     hs₁  hs₂  J₁ J₂  E (hE:0≤E)
    (hpair:∀u w:ℝ,(∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖normalizedColumn (withHeight s η (t₁+2*Real.pi*(u-θ₁))) C hC R seed L z‖*
      ‖normalizedColumn (withHeight v τ (t₂+2*Real.pi*(w-θ₂))) D hD R seed L z‖)≤
        E*(1+‖u‖)^J₁*(1+‖w‖)^J₂):
    (∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖windowColumn s C hC R seed L η t₁ θ₁ X V₁ z‖*
      ‖windowColumn v D hD R seed L τ t₂ θ₂ Y V₂ z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫w:ℝ,(1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖):=by
  have hh:=whole_plain_window_pair Ds μ rows Finset.univ Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator (columns v D hD))
    (sourceGenerator_supported _) (sourceGenerator_supported _)
    (coefficient s C hC R seed) (coefficient v D hD R seed) η τ t₁ t₂ θ₁ θ₂ X Y hX hY
    V₁ V₂ hc₁ hc₂ hs₁ hs₂ J₁ J₂ E hE ?_
  · simpa only [sourceGenerator_span,windowColumn] using hh
  · intro u w
    simpa only [sourceGenerator_span,coefficient_polynomial] using hpair u w

end SevenEighths.CenteredMomentCommonWindowColumn

end

end OAI
