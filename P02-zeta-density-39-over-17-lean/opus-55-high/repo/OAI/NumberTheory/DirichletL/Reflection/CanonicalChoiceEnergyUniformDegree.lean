module
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalChoiceEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalDyadsUniformDegree
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem canonical_original_choice_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0< cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤ cstar/100000) :
    ∃ (degree : ℕ), ∀ {Nlevel : Eis}, ∀
    {γ : Type*} [Fintype γ] (a c₀ : γ→ Eis) (mode : γ→ Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (_hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (_hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (_hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (_hB : B≠0),
    ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0) (_hR : R≠0),
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z N V M z₀ margin O₀ hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z ^V → (Ideal.absNorm R:ℝ)≤Z ^L →
      0≤O₀ → O₀≤M → Z ^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤ margin →
      V≤d → hhat≤d+η → d≤ cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z ^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (lists : σ→ Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z ^z₀ →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ K : rows,∀ p : supportedSlotChoices lists (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily lists hmax hgood p.val)).generator Nlevel (a g) (c₀ g) (mode g),
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ), (∀ i P,‖w i P‖≤1) →
      (∑ K : rows,‖∑ p : supportedSlotChoices lists (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
        (∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
          (reflectedExponent jF) (slotIndices A (PrimeIndex K.val) σ)
          (CompletedHeight.normTwistedSource W θ) (Z ^(N-3*hhat))‖^2)≤
        C*(1+‖θ‖)^degree*Z ^(N+V-cstar/8-O₀/2) := by
  obtain ⟨degree,hu⟩ := canonical_dyadic_geometry_uniform_uniform_degree lo hi hlo W hWs hW L cstar η hL hcstar hη hη1 hηc
  pm_3286
  pm_6588 Z₀ hZ₀
  obtain ⟨Cb,hCb,hbins⟩ := actual_dyad_count_budget L (cstar/32) hL (by positivity)
  refine ⟨Cb*C,Z₀,mul_pos hCb hC,hZ₀,?_⟩
  intro g σ _ _ J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents hsub hbad
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH hprod hGN hGchar hrowcop hLN hLchar
  pm_3298
  pm_3306
  pm_338
  have hpair : ∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hm hg p)).ideal) := by
    intro p
    apply PrimeFamily.sum_pairwise G _ ((poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A)
    pm_286
  pm_272
  have hPchar : ∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hm hg p)).ideal b)≠2 := by
    intro p b
    cases b with
    | inl f => exact hGchar f
    | inr i => exact hLchar i _ (htuples p.val p.property i)
  have hPnorm : ∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Z ^z₀ := by
    intro p hp
    refine ⟨slotTupleProduct_admissible lists hdis hprime ?_ p (htuples p hp),?_⟩
    · intro i P hPi
      let : P.IsMaximal := hmax i P hPi
      exact (primaryPrime_eq_primaryGenerator P).symm ▸ primaryPrime_ne_zero P (hgood i P hPi)
    · exact (slotTupleProduct_norm_bound lists H (fun i P hPi => (hprime i P hPi).ne_zero) hH p (htuples p hp)).2.trans hprod
  let Hrow := Z ^M/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J (B*F*R)):ℝ))
  let Hslot := Z ^z₀
  obtain ⟨Dc,hDc⟩ := he g J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d
    hZ hN hM hMc hVc hzc hhc hFn hRn hO hOM hOn hinv hmargin hVd hhd hd
    parents rows hparents hsub hbad tuples hm hg (fixedSlotTupleSet_product_injective lists FF hdis hprime)
    hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  pm_324
  have hsource (K : rows) :
      (∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc (s g) (hc₀ g)
        (fun b : A => completedLocalExponent J F b.val.val) W θ (Z ^(N-3*hhat)) (fun _ => 1)
        (fixedTupleCoefficient lists w) K p)=
      ∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z ^(N-3*hhat)) := by
    simpa only [dyadicPhysicalTerm,D,one_mul] using member_source_eq_original_choices lists FF hmax hgood G K.val
      (hrows K.val K.property) (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K)
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z ^(N-3*hhat)) 1 w
  pm_609
  have hid : (∑ K : rows,‖∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val) W θ (Z ^(N-3*hhat))
      (fun _ => 1) (fixedTupleCoefficient lists w) K p‖^2)=
      ∑ K : rows,‖∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z ^(N-3*hhat))‖^2 := by
    pm_282 hsource
  apply (hid.symm.trans_le hb).trans
  pm_148 hz hZ₀ hZ hzpos
  pm_5839
  have hm' : (1:ℝ)≤Ideal.absNorm (rowMaskPart J (B*F*R)) :=
    QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart J) (B*F*R))
  pm_3693 hRpos Hrow
  have hScap : Hslot≤Z ^L := Real.rpow_le_rpow_of_exponent_le hz.le hzc
  have hRcap : Hrow≤Z ^L := by
    exact (div_le_self (Real.rpow_nonneg hzpos.le _) (one_le_mul_of_one_le_of_one_le hp hm')).trans
      (Real.rpow_le_rpow_of_exponent_le hz.le hMc)
  pm_6714
  calc
    _ ≤ (Cb*Z ^(cstar/32))*(C*(1+‖θ‖)^degree*Z ^(N+V-3*cstar/16-O₀/2)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (Cb*C)*(1+‖θ‖)^degree*Z ^(cstar/32+(N+V-3*cstar/16-O₀/2)) := by
      rw [Real.rpow_add hzpos];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)
end SevenEighths.InverseReflectedPhase

end OAI
