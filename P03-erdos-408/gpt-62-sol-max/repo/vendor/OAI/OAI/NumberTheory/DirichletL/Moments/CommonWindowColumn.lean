module

public import OAI.NumberTheory.DirichletL.Moments.CommonPairedSource
public import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalWindowPair

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentCommonWindowColumn
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonPairedSource CenteredMomentCommonLinearSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentFirstSectors CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth
open CenteredMomentExceptionalWindowPair CenteredMomentPlainWindowEnergy CenteredMomentRowNorm
open CenteredMomentSmooth CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy HeckeFamily
open FourierBridge
open CenteredMomentPlainWindowEnergy CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem rowPolynomial_factor {α:Type*}(S:Finset α)(a:α→O)(c:α→ℂ)(v:ℂ)(z:O):
    rowPolynomial S a (fun i=>v*c i) z=v*rowPolynomial S a c z:=by
  simp only [rowPolynomial,Finset.mul_sum,mul_assoc]

def columns (s:Input ι)(C:Ideal O)(hC:Supported C):Finset (Ideal O):=
  residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))

def coefficient (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (I:supportedColumns (columns s C hC)):ℂ:=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*
    (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then
      finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I) else 0)

def windowColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
    (fun I=>coefficient s C hC R seed L I*heightCoeff η t I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z

omit [DecidableEq ι] in
theorem coefficient_polynomial (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t:ℝ)(z:O):
    rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
      (fun I=>coefficient s C hC R seed L I*heightCoeff η t I) z=
      normalizedColumn (withHeight s η t) C hC R seed L z:=by
  unfold normalizedColumn sourceColumn
  dsimp only [withHeight,Input.pools,columns]
  simp only [coefficient,mul_assoc,rowPolynomial_factor,Input.pools,columns]
  rfl

theorem sourceGenerator_span (S:Finset (Ideal O))(I:supportedColumns S):
    Ideal.span {sourceGenerator S I}=(I:Ideal O):=
  primary_span_supported I (Finset.mem_filter.mp I.property).2

omit [DecidableEq ι] in
theorem whole_window_pair (s v:Input ι)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal O)(Ds:Finset (Ideal O))(μ:Ideal O→ℂ)(rows:Finset O)
    (η τ:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u w:ℝ,(∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖normalizedColumn (withHeight s η (t₁+2*Real.pi*(u-θ₁))) C hC R seed L z‖*
      ‖normalizedColumn (withHeight v τ (t₂+2*Real.pi*(w-θ₂))) D hD R seed L z‖)≤
        E*(1+‖u‖)^J₁*(1+‖w‖)^J₂):
    (∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖windowColumn s C hC R seed L η t₁ θ₁ X V₁ z‖*
      ‖windowColumn v D hD R seed L τ t₂ θ₂ Y V₂ z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫w:ℝ,(1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖):=by
  let a := sourceGenerator (columns s C hC)
  let b := sourceGenerator (columns v D hD)
  let c (x : Ideal O × O) := fun i => μ x.1*coefficient s C hC R seed x.1 i
  let d (x : Ideal O × O) := coefficient v D hD R seed x.1
  let f (x : Ideal O × O) (u : ℝ) := columnDensity V₁ hc₁ hs₁ u*logPhase (θ₁-u) (Real.log X)*
    rowPolynomial Finset.univ a (fun i => c x i*heightCoeff η (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) x.2
  let g (x : Ideal O × O) (u : ℝ) := columnDensity V₂ hc₂ hs₂ u*logPhase (θ₂-u) (Real.log Y)*
    rowPolynomial Finset.univ b (fun i => d x i*heightCoeff τ (t₂+2*Real.pi*(u-θ₂)) (Ideal.span {b i})) x.2
  have hf (x : Ideal O × O) : Integrable (f x) :=
    plain_column_integrable _ a (sourceGenerator_supported _) (c x) η t₁ θ₁ X hX V₁ hc₁ hs₁ x.2
  have hg (x : Ideal O × O) : Integrable (g x) :=
    plain_column_integrable _ b (sourceGenerator_supported _) (d x) τ t₂ θ₂ Y hY V₂ hc₂ hs₂ x.2
  have hfi (x : Ideal O × O) : (∫ u, f x u) = μ x.1*windowColumn s C hC R seed x.1 η t₁ θ₁ X V₁ x.2 := by
    simpa only [f,a,c,windowColumn,sourceGenerator_span,mul_assoc,rowPolynomial_factor] using
      (plain_column_integral Finset.univ a (sourceGenerator_supported _) (c x) η t₁ θ₁ X hX V₁ hc₁ hs₁ x.2).symm
  have hgi (x : Ideal O × O) : (∫ u, g x u) = windowColumn v D hD R seed x.1 τ t₂ θ₂ Y V₂ x.2 := by
    simpa only [g,b,d,windowColumn,sourceGenerator_span] using
      (plain_column_integral Finset.univ b (sourceGenerator_supported _) (d x) τ t₂ θ₂ Y hY V₂ hc₂ hs₂ x.2).symm
  have hh := paired_integrals (Ds×ˢrows) f g (fun x _ => hf x) (fun x _ => hg x)
    (fun u => (1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)
    (fun w => (1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖)
    (columnDensity_moments V₁ hc₁ hs₁ J₁) (columnDensity_moments V₂ hc₂ hs₂ J₂) E ?_
  · simpa only [hfi,hgi,Finset.sum_product,norm_mul,mul_assoc,← Finset.mul_sum] using hh
  · intro u w
    let U := ‖columnDensity V₁ hc₁ hs₁ u‖
    let V := ‖columnDensity V₂ hc₂ hs₂ w‖
    simp only [f,g,norm_mul,logPhase_norm,a,b,c,d,sourceGenerator_span,mul_assoc,rowPolynomial_factor,
      coefficient_polynomial,Finset.sum_product]
    convert mul_le_mul_of_nonneg_left (hpair u w) (show 0 ≤ U*V from mul_nonneg (norm_nonneg _) (norm_nonneg _)) using 1
    · simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun L _ => ?_)
      refine Finset.sum_congr rfl (fun z _ => ?_)
      dsimp [U,V]
      ring
    · dsimp [U,V]
      ring

end SevenEighths.CenteredMomentCommonWindowColumn

end

end OAI
