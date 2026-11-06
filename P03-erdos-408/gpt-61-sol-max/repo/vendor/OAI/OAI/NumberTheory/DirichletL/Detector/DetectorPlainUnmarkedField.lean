module

public import OAI.NumberTheory.DirichletL.Moments.DetectorPlainMomentParameters
public import OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl
public import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.ProbeDetectorPlainUnmarkedField
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open CenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

def radialSupportUpper  := Classical.choose radialMajorant_support_bound

theorem radialSupportUpper_spec : 0<radialSupportUpper ∧
    Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic radialSupportUpper :=
  Classical.choose_spec radialMajorant_support_bound

lemma unmarked_power_eq (U m e:ℝ)(hU:1≤U):
    U^(max 1 (2*m)+e)=max U ((U^m)^2)*U^e := by
  have hpos:0<U:=zero_lt_one.trans_le hU
  rw [Real.rpow_add hpos]
  congr 1
  have hs:(U^m)^2=U^(2*m):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hpos.le]
    congr 1
    norm_num
    ring
  rw [hs]
  by_cases hm:1≤2*m
  · rw [max_eq_right hm,max_eq_right]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm
  · have hm':2*m≤1:=le_of_not_ge hm
    rw [max_eq_left hm',max_eq_left]
    · exact Real.rpow_one U
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm'

variable {Δ:ℝ}

theorem retained_unmarked_bound (D:Parameters.HighData Δ)
    {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
    {U a tstar T heightAllowance:ℝ}{i:ℕ}
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
     η  Q (hU:1<U)
    (hη:(η.modulus.absNorm:ℝ)≤U^(delta D))
    (degree:ℕ) S  A 
    (hzero:ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 (stageError D) U degree S A)
     j k  σ t :
    retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t radialMajorant ≤
      A*diagonalControl radialMajorant*(detectorProfiles F.reverse j k σ t).control S ^2*
        U^(max 1 (2*F.m)+delta D+stageError D) := by
  let s:=state F η Q radialMajorant radialSupportUpper (delta D) hU.le
    (fixed_parameters D).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hs:=unmarked_state_admission D F η Q radialMajorant radialSupportUpper hU
    radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hwidth:s.width=max 1 (2*F.m)+delta D:=hs.2.2.2.2.2.2.1
  have hband:s.width≤2:=hs.2.2.2.2.2.2.2.2.1
  have hscale:1≤U^F.m ∧ U^F.m≤U:=⟨hs.2.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.2.2.1⟩
  have hz:=hzero s rfl hband (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m)
    (zero_lt_one.trans_le hscale.1) (zero_lt_one.trans_le hscale.1)
    (by simpa only [Real.rpow_one] using hscale.2)
    (by simpa only [Real.rpow_one] using hscale.2)
  rw [actual_source_eq F η Q radialMajorant radialSupportUpper (delta D) hU.le
    (fixed_parameters D).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη j k σ t]
  have hrad:s.radial.profile=radialMajorant:=rfl
  simpa only [hwidth,hrad,norm_zero,add_zero,one_pow,mul_one] using hz

end SevenEighths.ProbeDetectorPlainUnmarkedField

end

end OAI
