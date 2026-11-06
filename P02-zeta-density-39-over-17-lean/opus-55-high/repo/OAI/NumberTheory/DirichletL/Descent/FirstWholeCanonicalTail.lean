module
public import OAI.NumberTheory.DirichletL.Descent.FirstWholeMarkedColumns
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem first_whole_cube_canonical_tail (ε : ℝ) (hε : 0<ε) (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct Cm : ℝ),0<Ct ∧ 0<Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→ O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι),b.Admissible →
      ∀ (common divisor : Finset ι),Disjoint common b.support →
      ∀ (f : Ideal O),f≠0 →
      ∀ (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ : O) (extra₁ extra₂ : Finset ι) (E : ℝ) (slots : Finset σ) (lists : σ→ Finset ι) (a : σ→ι→ℂ),
      0≤E → primeProductNorm p extra₁≤E → primeProductNorm p extra₂≤E →
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤G₁ → 0≤G₂ → 0<Z →
      (∀ U,‖test₁ U‖≤G₁) → (∀ U,‖test₂ U‖≤G₂) →
      (∀ U,test₁ U≠0 → primeProductNorm p U≤Z ^(r+eta)) →
      (∀ U,test₂ U≠0 → primeProductNorm p U≤Z ^(r+eta)) →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z ^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z ^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤Z ^(V+eta) → primeProductNorm p divisor≤Z ^(delta+eta) →
      Z ^(B-eta)≤primeProductNorm p common →
      Z ^(j-eta)≤‖eisEmbedding (jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit)‖^2 →
      let residualPool := pool\(b.support∪common)
      let C₁ := canonicalCubeResidual p hg b common true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
      let C₂ := canonicalCubeResidual p hg b common false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U)
      let U₁ := Z ^(r+eta)/(‖eisEmbedding (aLabel p b.support b.rightBit)‖^2*primeProductNorm p common)
      let U₂ := Z ^(r+eta)/(‖eisEmbedding (aLabel p b.support b.leftBit)‖^2*primeProductNorm p common)
      let G₁' := Cm*(E*Z ^(r+eta))^ε*G₁
      let G₂' := Cm*(E*Z ^(r+eta))^ε*G₂
      let active := cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      let slow := Z ^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f)
        (Z ^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hcop hg residualPool b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit C₁ C₂ W
        (fun _=>1) (fun _=>1) 1 1 (Z ^M)
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁'*G₂'*Z ^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z ^tau)^order)) := by
  pm_3008 s Ct hCt htail full_first_physical_tail order
  pm_69 Cm hCm hmark whole_cube_marked_test_uniform ε hε
  pm_164 s Ct Cm hCt hCm
  intro ι σ _ _ p hp _ hinj hcop hg hchar pool b hb common divisor hcommon f hf0 Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ extra₁ extra₂ E slots lists a hE he₁ he₂ hslots ha test₁ test₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ
    htest₁ htest₂ hs₁ hs₂ hb₁ hb₂ hf hd hc hj residualPool C₁ C₂ U₁ U₂ G₁' G₂' active slow T
  pm_6367 residualPool common
  apply htail p hp hinj hcop hg hchar residualPool b.support common divisor b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos (hdis.mono_right Finset.subset_union_left) f hf0 C₁ C₂ W
    G₁' G₂' Z M r ell V delta B j eta tau (by dsimp [G₁']; positivity) (by dsimp [G₂']; positivity) hZ
  pm_7567 true Ψ₁ hΨ₁ m₁ extra₁ test₁ G₁ hG₁ he₁ htest₁ hs₁
  pm_7567 false Ψ₂ hΨ₂ m₂ extra₂ test₂ G₂ hG₂ he₂ htest₂ hs₂
  pm_87 hb₁ hb₂ hf hd
  · exact hc
  · exact hj
  · intro N hN hn
    pm_5080 true Ψ₁ m₁ hs₁
    simp only [ite_true] at he
    exact he ▸ hn'
  · intro N hN hn
    pm_5080 false Ψ₂ m₂ hs₂
    simp only [ite_false,Bool.false_eq_true] at he
    exact he ▸ hn'

end SevenEighths.InverseMoment

end OAI
