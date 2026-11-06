module

public import OAI.NumberTheory.DirichletL.Inversion.InitialCommonCutoff

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic FirstPassCubeLabels
namespace SevenEighths.InverseInitialCommonTransform
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

theorem original_profile_point
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)(jlo jhi:ℝ)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (A:Finset (primePool F))(yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hjpos:0<yj)(hc:0<yc) :
    tupleProfile I L a Z ell W yj yc (∏i∈A,i.val)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        (primeMark I (fun i=>poolList F (L i))
          (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
          childLogTest wFresh t yc) := by
  have he := common_profile_separation W a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell A yj yc hjpos hc
  have hcut := tupleProfile_insert_fresh I L a hcop Z ell lo hi W wFresh a₀ b₀ jlo jhi hs ha hFresh yj yc hj hc (∏i∈A,i.val)
  rw [←hcut]
  unfold tupleProfile
  rw [he,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  unfold childLogTest
  ring

end SevenEighths.InverseInitialCommonTransform

end

end OAI
