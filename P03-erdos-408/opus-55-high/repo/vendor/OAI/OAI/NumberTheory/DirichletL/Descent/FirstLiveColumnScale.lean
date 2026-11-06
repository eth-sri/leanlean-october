module

public import OAI.NumberTheory.DirichletL.Descent.FirstDyadicLiveRadius
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileScales
public import OAI.NumberTheory.DirichletL.Descent.FirstLiveCaps

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks
open InverseMomentFirstOriginalProfile
open ConcreteTraceCRT (eisEmbedding)

theorem first_profile_live_products (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)(q:Fin 9→ℝ)
    (hq:∀i,1≤q i)(hW:∀x,W x≠0→x≤L)
    (hn:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K q≠0):
    q 0*q 2*q 5≤L ∧ q 1*q 2*q 5≤L:=by
  have h₁:W (q 0*q 2*q 5*q 7)≠0:=by intro h;apply hn;simp [firstNormProfile,h]
  have h₂:W (q 1*q 2*q 5*q 8)≠0:=by intro h;apply hn;simp [firstNormProfile,h]
  constructor
  · exact (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by grind) (by grind)) (by grind)) (hq 7)).trans (by grind)
  · exact (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by grind) (by grind)) (by grind)) (hq 8)).trans (by grind)

private theorem dyadic_column_scale {a c z X b : ℝ}
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hz : 1 ≤ z) (hprod : a * c * z ≤ b * X) :
    1 ≤ X / (dyadScale (dyadIndex a) * dyadScale (dyadIndex c) *
      dyadScale (dyadIndex z)) * b := by
  have hscale : dyadScale (dyadIndex a) * dyadScale (dyadIndex c) *
      dyadScale (dyadIndex z) ≤ a * c * z :=
    mul_le_mul
      (mul_le_mul (dyadIndex_bounds a ha).1 (dyadIndex_bounds c hc).1
        (dyadScale_pos _).le (zero_le_one.trans ha))
      (dyadIndex_bounds z hz).1 (dyadScale_pos _).le
      (by positivity)
  rw [div_mul_eq_mul_div,
    le_div_iff₀ (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)),
    one_mul, mul_comm X b]
  linarith

theorem original_live_column_scale {ι:Type}[DecidableEq ι]
    (p:ι→ActualEisensteinCubic.O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal ActualEisensteinCubic.O))(Y:ℝ)
    (β:Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal ActualEisensteinCubic.O→Finset ι→ℝ)
    (Ψ:ActualEisensteinCubic.O→*ℂ)(m:ActualEisensteinCubic.O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K X b:ℝ)
    (_hX:0<X)(hW:∀y,W y≠0→y≤b*X)
    (k:JointKey)(hk:k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K)):
    1≤physicalScales X k.1 k.2.1 7*b ∧ 1≤physicalScales X k.1 k.2.1 8*b:=by
  obtain ⟨⟨x,j⟩,hm,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hm
  obtain ⟨hx,hj⟩:=Finset.mem_product.mp hm
  have hs:=original_source_norms_ge_one p hp pool Q labels Y x hx
  have hq:∀i,1≤firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
      (divisorElement p x.1) x.2.2 j i:=by
    intro i
    fin_cases i
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 4
    · exact primeProductNorm_ge_one p hp _
    · exact hs 5
    · exact primeProductNorm_ge_one p hp _
    · exact primeProductNorm_ge_one p hp _
  have hprof:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)≠0:=by
    intro hzero
    exact hnon (by unfold sourceSummand;simp_all)
  have hb:=first_profile_live_products W Φ K (b*X) _ hq hW hprof
  constructor
  · change 1 ≤ X / (dyadScale (dyadIndex (leftNorm p x)) *
        dyadScale (dyadIndex (commonNorm p x)) *
        dyadScale (dyadIndex (primeProductNorm p j.2.1))) * b
    exact dyadic_column_scale (hs 0) (hs 2) (primeProductNorm_ge_one p hp _) hb.1
  · change 1 ≤ X / (dyadScale (dyadIndex (rightNorm p x)) *
        dyadScale (dyadIndex (commonNorm p x)) *
        dyadScale (dyadIndex (primeProductNorm p j.2.1))) * b
    exact dyadic_column_scale (hs 1) (hs 2) (primeProductNorm_ge_one p hp _) hb.2

end SevenEighths.InverseMoment

end

end OAI
