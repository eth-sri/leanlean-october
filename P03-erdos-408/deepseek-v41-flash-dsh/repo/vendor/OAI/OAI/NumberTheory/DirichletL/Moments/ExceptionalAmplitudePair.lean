module

public import OAI.NumberTheory.DirichletL.Moments.AllocatedDetectorAmplitude
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAllocationShell

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

structure Tests where
  reverse : Fin 2→Bool
  index : Fin 2→ℕ
  index_le : ∀j,index j≤2
  sigma : Fin 2→ℝ
  sigma_mem : ∀j,sigma j∈Set.Icc (0:ℝ) 1
  height : Fin 2→ℝ

def volume {ι:Type u} [Fintype ι] (s:Data ι):ℝ:=s.X₁*s.X₂*∏i,s.P i

lemma volume_pos {ι:Type u} [Fintype ι] (s:Data ι):0<volume s:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

lemma norm_le_of_squared (x:ℂ) (H V d M:ℝ) (hH:0≤H) (hV:0≤V) (hd:0<d) (hM:0<M)
    (hb:‖x‖^2≤H^2*V/(d^2*M^2)):
    ‖x‖≤H*Real.sqrt V/(d*M):=by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  convert hb using 1
  rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hV]

lemma reduction_cap_identity {ι κ:Type u} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s:Data ι) (v:Data κ) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))) (Z r:ℝ) (hZ:1<Z):
    1/(formalReductionFactor D a s.P*formalReductionFactor D b v.P*
      Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))=
      exceptionalWeight s.toSource v.toSource D a b Z r:=by
  have hz:=zero_lt_one.trans hZ
  unfold exceptionalWeight
  rw [show -Real.logb Z (formalReductionFactor D a s.P)-Real.logb Z (formalReductionFactor D b v.P)-
      max (r-Real.logb Z (formalReductionFactor D a s.P)) 0=
      -(Real.logb Z (formalReductionFactor D a s.P)+Real.logb Z (formalReductionFactor D b v.P)+
        max (r-Real.logb Z (formalReductionFactor D a s.P)) 0) by ring,
    Real.rpow_neg hz.le,Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz hZ.ne' (s.reduction_pos D a),Real.rpow_logb hz hZ.ne' (v.reduction_pos D b)]
  exact one_div _

end SevenEighths.CenteredMomentExceptionalAmplitudePair

end

end OAI
