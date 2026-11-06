module

public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerReference
public import OAI.NumberTheory.DirichletL.Descent.SecondSquarefree
public import OAI.NumberTheory.DirichletL.Descent.ChildCutoff

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
open ActualEisensteinCubic CompletedGauss SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerGeometry
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open ConcreteTraceCRT
variable {ι:Type*}[DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem outerCoefficient_nonzero_coprime
    (Ψ:ActualEisensteinCubic.O→*ℂ)(j:ActualEisensteinCubic.O)(x:Point ι)(ρ:SecondRayIndex)
    (hn:outerCoefficient p hp hcop hg Ψ j x ρ≠0) :
    IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common) := by
  apply sourceIdeal_coprime_of_not_mem p
  intro i hi hc
  have hmc := Ideal.mul_mem_left _ j hc
  have hz : rowCoprimeMask (fun i=>Ideal.span {p i}) x.overlap (j*(∏k∈x.common,p k))=0 := by
    simp only [rowCoprimeMask,ite_eq_left (show ∃i∈x.overlap,j*(∏k∈x.common,p k)∈Ideal.span {p i}
      from ⟨i,hi,hmc⟩)]
  apply hn
  simp only [outerCoefficient, initialColumn, hz, mul_zero, zero_mul]

omit [DecidableEq ι] in
theorem initial_child_label_norm (x:Source (ι:=ι) 0)(u:ActualEisensteinCubic.Oˣ) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)=
      (sourceIdeal p x.divisor).absNorm*(sourceIdeal p x.overlap).absNorm := by
  change ((sourceIdeal p x.divisor*sourceIdeal p x.overlap).absNorm:ℝ)=_
  simp

include hp in

theorem initial_child_row_norm (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:ActualEisensteinCubic.Oˣ) :
    ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2=
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2 := by
  change ‖eisEmbedding (primaryGenerator (sourceIdeal p x.divisor)*((u:ActualEisensteinCubic.O)^5*x.frequency))‖^2=_
  have he : primaryGenerator (sourceIdeal p x.divisor)*((u:ActualEisensteinCubic.O)^5*x.frequency)=
      ((u^5:ActualEisensteinCubic.Oˣ):ActualEisensteinCubic.O)*(primaryGenerator (sourceIdeal p x.divisor)*x.frequency) := by
    change primaryGenerator (sourceIdeal p x.divisor)*((u:ActualEisensteinCubic.O)^5*x.frequency)=
      (u:ActualEisensteinCubic.O)^5*(primaryGenerator (sourceIdeal p x.divisor)*x.frequency)
    ring
  rw [he,GaussGeneratorTransport.norm_eisEmbedding_unit_mul,map_mul,norm_mul,mul_pow]
  rw [eisEmbedding_norm_sq_eq_absNorm_span,sourceIdeal_gen p hp hpr]
  rfl

include hp in
theorem initial_child_row_ball (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:ActualEisensteinCubic.Oˣ)(R:ℝ) :
    (initialChild (toTuple p (sectorSource u x))).2.2∈nonzeroChildFrequencyBall 1 R ↔
    0<((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2 ∧
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2≤R := by
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,initial_child_row_norm p hp hpr]

include hp in

theorem initial_child_enclosures
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:ActualEisensteinCubic.Oˣ)(Z θ v H η:ℝ)(hZ:0<Z)
    (hd:((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η))
    (hh:‖eisEmbedding x.frequency‖^2≤Z^(H+η)) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)≤Z^(θ+v+2*η) ∧
      ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2≤Z^(θ+H+2*η) := by
  rw [initial_child_label_norm p,initial_child_row_norm p hp hpr]
  constructor
  · apply (mul_le_mul hd hv (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    ring
  · apply (mul_le_mul hd hh (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    ring

end SevenEighths.InverseInitialEnergyCallerGeometry

end

end OAI
