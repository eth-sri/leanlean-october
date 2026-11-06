module
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondPaidLedger
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondLossParameters

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExceptionalPaidScales
open CanonicalQuadraticSieve CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstPhysicalLedger
local notation "O"=>ActualEisensteinCubic.O

structure Branch (Z:ℝ) where
  I:Ideal O
  J:Ideal O
  E:Ideal O
  hI:Supported I
  hJ:Supported J
  hE:E≠0
  H:ℝ
  X:ℝ
  Tsec:ℝ
  Csec:ℝ
  ξ:ℝ
  q:ℝ
  w:ℝ
  wo:ℝ
  ell:ℝ
  σ:ℝ
  kind:ℝ
  hH:0<H
  hX:0<X
  hCsec:1≤Csec
  hξ:0≤ξ
  hsec:Tsec≤Csec*firstNominalScale I J E H X
  n:ℤ
  hn:Retained (frequencyRadius Tsec Z ξ) n
  hq:0≤q
  hw:0≤w
  hwo:0≤wo
  hell:0≤ell
  hσ:0≤σ
  hkind:kind≤2
  hwσ:w≤7*σ/3

def saving {Z:ℝ}(s:Branch Z):ℝ:=
  let c:=Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)
  let d:=Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)
  let p:=Real.logb Z ((commonRadical s.I s.J).absNorm:ℝ)
  let R:=Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)
  let e:=Real.logb Z (s.E.absNorm:ℝ)
  let D₀:=d+Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-
    Real.logb Z (dyadicScale s.n)
  firstSaving c D₀ s.w (s.q+R+e) s.wo (c+d-2*p-R)
    (max (D₀-c-2*s.w+s.wo) 0+s.kind*s.σ) s.ell

end SevenEighths.CenteredMomentFirstExceptionalPaidScales

end

end OAI
