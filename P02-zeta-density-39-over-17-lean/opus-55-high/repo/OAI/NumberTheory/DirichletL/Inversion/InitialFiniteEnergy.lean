module
public import OAI.NumberTheory.DirichletL.Inversion.InitialRetainedSum
public import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicTailBound
public import OAI.NumberTheory.DirichletL.Inversion.InitialProfileBounds
import WeylPort.Analytic.RealLaplace

public section

namespace OAI


open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialFiniteEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource
open InverseInitialQuotientGeometry
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

theorem finite_physical_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb₁:∀x,‖W₁ x‖≤B₀)(hb₂:∀x,‖W₂ x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z ^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→ all.card≤K→
    ∀(lists:σ→ Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→ primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→ O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z ^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→ FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
      (∀x∈S,x.common⊆Finset.univ)→(∀x∈S,x.overlap⊆Finset.univ)→
    ∀(D m r:ℝ),0≤ m→ m≤ cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z ^η→
      (∏i∈all\assigned,Hslot i)≤Z ^(assignedCenter (all\assigned) z+η)→
      D =r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤ c₁→ c₁≤bcap→1≤ c₂→ c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘ erasePoint) Ψ
        (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z ^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨J,Btree,hBtree,hretained⟩:=InverseInitialRetainedSum.retained_sum_bound
    W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨ss,Ct,hCt,htail⟩:=InverseInitialDyadicTailBound.actual_high_mass_tail (2*cap+2) 1 τ hτ
  let tailC:=Ct*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  pm_100 htailC tailC
  have hevent:∀ᶠZ:ℝ in atTop,max 1 b₀≤Z ∧ 64*(max 1 b₀)^2≤Z ^η:=
    (eventually_ge_atTop (max 1 b₀)).and
      ((tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (64*(max 1 b₀)^2)))
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp hevent
  pm_253 J Btree hBtree q hq
  pm_3744 Cr Zr hCr hZr hretained
  refine ⟨Cr+tailC,max Zr Zaux,by linarith,lt_max_of_lt_left hZr,?_⟩
  pm_3210
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf hcommon hoverlap
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent
    c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  pm_5224 hZr' Zr Z hZ
  have hZp:1<Z:=hZr.trans_le hZr'
  pm_8137 hbZ h64 haux Z hZ
  have hDcap:D ≤ cap:=by
    pm_3198
    rw [hDeq];linarith
  have hsize:max 1 b₀*Z ^D ≤Z ^(2*cap+2):=by
    calc
      _≤Z*Z ^D:=mul_le_mul_of_nonneg_right hbZ (Real.rpow_nonneg (by linarith) _)
      _=Z ^(D +1):=by rw [Real.rpow_add (by linarith : 0<Z),Real.rpow_one];ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  pm_7021 hs₁' W₁ c₁ θ₁ hc₁ hs₁
  pm_7021 hs₂' W₂ c₂ θ₂ hc₂ hs₂
  pm_3599 T hT hfreqcap exists_source_frequency_cap p S
  have hsplit:=actual_physical_retained_tail p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ S hdiv hf w Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ
    Z D m (max 1 b₀) T (4*η+τ) hZp hs₁' hs₂' hfreqcap
  rw [hsplit]
  apply (norm_add_le _ _).trans
  have hret:=hretained Z hZr' Dpool hD all assigned hassigned hK lists Hslot coeff
    hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf
    D m r T hm hT hprodj hprod hDeq hmargin₁ hmargin₂ hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  pm_1410
  have ht:=htail p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa) Ψ hΨ
    (assignedElement assigned qelem) (all\assigned) lists coeff
    (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hac
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m η (max 1 b₀) 1 B₀ B₀
    hZp hη.le (by positivity) h64 (by linarith) hsize (by linarith) (by linarith)
    (by norm_num) hB₀ hB₀ (clipped_bound W₁ B₀ hb₁ c₁ θ₁) (clipped_bound W₂ B₀ hb₂ c₂ θ₂)
    hs₁' hs₂' Finset.univ Sc w
    (fun x hx=>hcommon x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hoverlap x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hw x (Finset.mem_filter.mp hx).1)
    (fun _=>1) (physicalCaps (max 1 b₀) Z D T) (by intros;norm_num)
    (fun x hx=>(Finset.mem_filter.mp hx).2)
  have hheight:1≤((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg θ₁]))
      (one_le_pow₀ (by linarith [norm_nonneg θ₂]))
  have hpow:Z ^(-1:ℝ)≤Z ^(m+15*η+π+eps+loss):=
    Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  apply (add_le_add hret ht).trans
  change Cr*Z ^(m+15*η+π+eps+loss)*_+(Ct*1*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z ^(-1:ℝ))≤_
  have hh:tailC*Z ^(-1:ℝ)≤tailC*Z ^(m+15*η+π+eps+loss)*
      ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    calc
      _≤tailC*Z ^(m+15*η+π+eps+loss):=mul_le_mul_of_nonneg_left hpow htailC
      _≤_:=le_mul_of_one_le_right (by positivity) hheight
  convert add_le_add_left hh (Cr*Z ^(m+15*η+π+eps+loss)*
    ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))) using 1 <;> dsimp [tailC] <;> ring

end SevenEighths.InverseInitialFiniteEnergy


end OAI
