module
public import OAI.NumberTheory.DirichletL.Descent.SecondRapidTail
public import OAI.NumberTheory.DirichletL.Descent.SecondCanonicalTail
public import OAI.NumberTheory.DirichletL.Descent.PrincipalSelectorMass

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityRapidTail
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion InverseMoment InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O

theorem marked_rapid_tail (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ), (∀u,‖Ψ u‖≤1) →
      ∀ (m c d : O),d≠0 → ∀ (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      ∀ (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (negative : Bool) (height X M Y Z : ℝ)
      (R : Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀G∈F.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (markedRadial p slots lists a ∅ (principalWindow om lo hi hlo hs negative height) X) W Y
        (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))‖≤
      Ct*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_rapid_correlated_tail Lcap tau (saving+Lcap) hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound (1/2) (by norm_num)
  refine ⟨s,Ct*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F Ψ hΨ m c d hd slots lists a hslots ha
    om W lo hi hlo hs negative height X M Y Z R hX hhi hZ hY hL hy hyi hl hR
  let L:=X*Real.exp M
  have hLpos : 0<L := mul_pos hX (Real.exp_pos _)
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hv := principalWindow_upper om lo hi hlo hs M hhi negative height
  have hm := hmark p hp hcop slots lists a hslots ha ∅
    (principalWindow om lo hi hlo hs negative height) X M hX hv
  simp only [Finset.card_empty,pow_zero,one_mul,principalWindow_seminorm_zero] at hm
  have ht := htail p hp hg hinj hc F Ψ hΨ m c d hd _ W Z
    (Cm*L^(1/2:ℝ)*SchwartzMap.seminorm ℝ 0 0 om) Y L R hZ (by positivity) hY hL hy hyi hl hm
    (markedRadial_support p slots lists a ∅ _ X M hX hv) hR
  have hp : (L^(1/2:ℝ))^2=L := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLpos.le]
    norm_num
  have habsorb : L*Z^(-(saving+Lcap))≤Z^(-saving) := by
    calc
      _≤Z^Lcap*Z^(-(saving+Lcap)) := mul_le_mul_of_nonneg_right hl (by positivity)
      _=Z^(-saving) := by rw [←Real.rpow_add hz];congr 1;ring
  apply ht.trans
  calc
    _=(Ct*Cm^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        (L*Z^(-(saving+Lcap))) := by rw [mul_pow,mul_pow,hp];ring
    _≤_ := by
      exact mul_le_mul_of_nonneg_left habsorb (by positivity)

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseWholePriorityRapidTail

end

end OAI
