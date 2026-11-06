module

public import OAI.NumberTheory.DirichletL.Detector.DetectorMomentData
public import OAI.NumberTheory.DirichletL.Dictionary.InverseRawFiberSource
public import OAI.NumberTheory.DirichletL.Hecke.DetectorBatch
public import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedElement

@[expose] public section

namespace OAI

noncomputable section


open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource CanonicalCoefficientClass InverseInitialExcludedPeriod CanonicalQuadraticSieve InverseInitialRayAttachment CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

def sourceMomentConductorBound (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):ℝ:=
  1+∑j:Sum Bool (RayQuotient.Characters M H),
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)

theorem sourceMomentConductor_le (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    (j:Sum Bool (RayQuotient.Characters M H)):
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
      sourceMomentConductorBound M H hH S hS η:=by
  have hh:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Sum Bool (RayQuotient.Characters M H))))=>
    (Nat.cast_nonneg (α:=ℝ) (baseCharacter (sourceMomentData M H hH S hS η k)).modulus.absNorm))
      (Finset.mem_univ j)
  unfold sourceMomentConductorBound
  linarith

theorem sourceMoment_large_eventually (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    {Slot:Type*}[Fintype Slot](ell:Slot→ℝ)(hell:∀s,0<ell s):
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→
      ∀j:Sum Bool (RayQuotient.Characters M H),∀s:Slot,
        ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
          (Z^d)^(ell s/d):=by
  have ht:∀ᶠZ:ℝ in atTop,∀s:Slot,sourceMomentConductorBound M H hH S hS η<Z^(ell s):=by
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0≤Z),mul_div_cancel₀ _ hd.ne']
  exact (sourceMomentConductor_le M H hH S hS η j).trans (ht s)

end SevenEighths.ProbeHighRowFamily

end

end OAI
