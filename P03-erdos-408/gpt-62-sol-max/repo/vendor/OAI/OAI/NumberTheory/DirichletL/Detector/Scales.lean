module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace OAI.SevenEighths

/-- The common scale and error parameters for the detector's cube estimates. -/
structure DetectorScales where
  e : ℝ
  eps : ℝ
  c : ℝ
  b : ℝ
  A : ℝ
  R : ℝ
  dmin : ℝ
  dmax : ℝ
  rmin : ℝ
  τ : ℝ
  ε : ℝ
  κ : ℝ
  cost : ℝ
  mesh : ℝ
  margin : ℝ
  loss : ℝ
  he : 0<e
  he1 : e<1/1000
  heps : 0<eps
  hc : 0<c
  hcb : c≤b
  hA : 0≤A
  hR : 0≤R
  hdmin : 0<dmin
  hdmax : 0≤dmax
  hdRange : dmin≤dmax
  hrmin : 0<rmin
  hτ : 0<τ
  hε : 0<ε
  hκ : 0<κ
  hcost : 0≤cost
  hmesh : 0<mesh
  hbudget : 8*e*R+κ≤ε
  hgap : ε<rmin*mesh
  hmargin : 0<margin
  hheight : 2*τ<dmin*cost
  hloss : τ*(2+4*eps)<loss

/-- The estimates retaining the floor use an additional positive scale. -/
structure FloorDetectorScales extends DetectorScales where
  δ : ℝ
  hδ : 0 < δ

end OAI.SevenEighths
