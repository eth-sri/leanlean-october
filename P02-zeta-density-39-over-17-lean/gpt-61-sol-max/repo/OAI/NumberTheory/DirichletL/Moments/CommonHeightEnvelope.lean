module
public import OAI.NumberTheory.DirichletL.Moments.CommonRadialPointwise

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonHeightEnvelope
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentCommonRadialPointwise



open scoped EisensteinO
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

 def withHeight (s:Input ι) (η:Character) (t:ℝ) : Input ι := {s with η:=η,t:=t}

 def envelope (s:Input ι) (C L:Ideal O) (C0 Z δ E:ℝ) : ℝ :=
  C0*Z^δ*(profileCost s*E)*(s.X₁*s.X₂*∏i,s.P i)/((Ideal.absNorm C:ℝ)*Ideal.absNorm L)






