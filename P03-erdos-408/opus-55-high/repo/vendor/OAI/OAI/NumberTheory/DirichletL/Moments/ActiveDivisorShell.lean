module

public import OAI.NumberTheory.DirichletL.Moments.ActiveAllocation
public import OAI.NumberTheory.DirichletL.Moments.DivisorBoundary

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentActiveDivisorShell
open HeckeFamily CenteredMomentActiveAllocation CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios

structure Source (ι:Type*) [Fintype ι] where
  η : Character
  m : ActualEisensteinCubic.O
  A : ActualEisensteinCubic.O
  t : ℝ
  slots : ι→Finset (Ideal ActualEisensteinCubic.O)
  prime : ∀i,∀I∈slots i,Prime I
  ν : ι→Ideal ActualEisensteinCubic.O→ℂ
  W : ι→ℝ→ℂ
  lo : ι→ℝ
  hi : ι→ℝ
  P : ι→ℝ
  lo_pos : ∀i,0<lo i
  P_pos : ∀i,0<P i
  support : ∀i,Function.support (W i)⊆Set.Icc (lo i) (hi i)
  W₁ : ℝ→ℂ
  W₂ : ℝ→ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Source.active (s:Source ι) (D:Ideal ActualEisensteinCubic.O) : Finset (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :=
  activeAllocations s.η s.m s.A s.t s.slots
    (fun i I=>s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)) D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

def Source.allowance (s:Source ι) (Z:ℝ) : ℝ :=
  (∑i,logWindow (s.lo i) (s.hi i))/Real.log Z

theorem Source.active_boundary (s:Source ι) (D:Ideal ActualEisensteinCubic.O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.active D) (Z:ℝ) (hZ:1<Z) :
    Real.logb Z (Ideal.absNorm D:ℝ)≤Real.logb Z (formalReductionFactor D a s.P)+s.allowance Z :=
  active_formal_boundary s.η s.m s.A s.t s.slots s.prime s.ν s.W s.lo s.hi s.P s.lo_pos s.P_pos
    s.support D hD a s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ Z hZ ha

theorem reciprocal_sqrt_log (Z x y:ℝ) (hZ:1<Z) (hx:0<x) (hy:0<y) :
    1/Real.sqrt (x*y)=Z^(-(Real.logb Z x+Real.logb Z y)/2) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  calc
    _=(x*y)^(-(1/2:ℝ)):=by rw [Real.sqrt_eq_rpow,one_div,Real.rpow_neg (by positivity)]
    _=(Z^(Real.logb Z x+Real.logb Z y))^(-(1/2:ℝ)):=by
      rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hx,Real.rpow_logb hz hZ.ne' hy]
    _=_:=by rw [←Real.rpow_mul hz.le]; ring

theorem Source.active_pair_weight {κ:Type*} [Fintype κ] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (D:Ideal ActualEisensteinCubic.O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (ha:a∈s.active D) (hb:b∈v.active D) (Z:ℝ) (hZ:1<Z) :
    1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P)≤
      Z^((s.allowance Z+v.allowance Z)/2)/(Ideal.absNorm D:ℝ) := by
  have hs:0<formalReductionFactor D a s.P:=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))
  have hv:0<formalReductionFactor D b v.P:=
    mul_pos (selectedNorm_pos D b) (Finset.prod_pos (fun i _=>v.P_pos i))
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  rw [reciprocal_sqrt_log Z _ _ hZ hs hv]
  have hl:=s.active_boundary D hD a ha Z hZ
  have hr:=v.active_boundary D hD b hb Z hZ
  have he:-(Real.logb Z (formalReductionFactor D a s.P)+Real.logb Z (formalReductionFactor D b v.P))/2≤
      (s.allowance Z+v.allowance Z)/2-Real.logb Z (Ideal.absNorm D:ℝ):=by linarith
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le he
  rwa [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn] at hp

end SevenEighths.CenteredMomentActiveDivisorShell

end

end OAI
