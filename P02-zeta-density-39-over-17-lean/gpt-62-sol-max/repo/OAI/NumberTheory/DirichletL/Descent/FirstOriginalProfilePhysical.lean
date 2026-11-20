module
public import OAI.NumberTheory.DirichletL.Descent.FirstGlobalPush
public import OAI.NumberTheory.DirichletL.Descent.FirstHeightBudget
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileUniform

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
theorem actual_first_original_subset_physical_budget (ε : ℝ) (hε : 0<ε)
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile Kpush : ℝ,0 ≤ Cprofile ∧ 0<Kpush ∧ ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (_hc : ∀ i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (outer:Finset κ) (b : κ→SecondPassArithmetic.CubeCoordinates ι) (common : κ→Finset ι)
    (Ψ₁ Ψ₂ : Eis→*ℂ) (mleft mright : Eis) (dd:κ→Eis) (H₁ H₂ selector : κ→Finset ι→ℂ)
    (labels : κ→Finset (Ideal Eis)) (a : κ→Ideal Eis×Eis→ℂ) (Γ Y : ℝ)
    (_hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (_hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (_hΓ : 0≤Γ) (_hY : 0<Y)
    (_hlabels : ∀k∈outer,∀ f∈labels k,Squarefree f) (_hn : ∀k∈outer,∀ f∈labels k,f≠0)
    (_ha : ∀k∈outer,∀ x∈firstRetainedSource p (labels k) (b k) Y,‖a k x‖≤Γ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : (Σ _ : κ,Ideal Eis×Eis) → ℝ) (K L : ℝ) (_hK : 0<K) (s : Fin 9→ℝ)
    (_hs : ∀ i,0<s i)
    (selected : Finset (Σ _ : κ,Ideal Eis×Eis))
    (_hselected : selected⊆firstGlobalRetainedSource p outer labels b Y),
    let source := selected
    let C₁ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) true Ψ₁ mleft (dd x.1) (H₁ x.1) x.2
    let C₂ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) false Ψ₂ mright (dd x.1) (H₂ x.1) x.2
    let w := fun x : (Σ _ : κ,Ideal Eis×Eis) => retainedCubeWeight p hp hcop hg (b x.1) (common x.1) Ψ₁ Ψ₂ mleft mright (dd x.1) (a x.1) x.2
    ∀ (_hpos : ∀ x∈source,0<A₁ x ∧ 0<A₂ x ∧ 0<C x ∧ 0<R x ∧ dd x.1≠0 ∧ x.2.2≠0)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (dd x.1) x.2.2 j) s i)+ρ i) = 1)
    (Benergy : ℝ) (_hBenergy : 0 ≤ Benergy)
    (Z M r ell V delta aa₁ aa₂ bb rr tq hh eta:ℝ) (_hZ:0<Z)
    (_hscale:s=fun i=>Z^(![aa₁,aa₂,bb,delta,rr,tq,hh,r-aa₁-bb-tq,r-aa₂-bb-tq] i))
    (_hLe:L=eta*Real.log Z)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      (Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) true Ψ₁ mleft (dd k) (H₁ k) (selector k) ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y) ≤
        Benergy*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      (Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) false Ψ₂ mright (dd k) (H₂ k) (selector k) ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y) ≤
        Benergy*(tripleHeight J z.1*coordinateHeight J z.2)),
    (Z^(-r-2*ell-V)*Z^M)*‖firstFamilyPhysicalRows p hg source F (fun x=>selector x.1) C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K (fun x=>dd x.1) (fun x=>x.2.2) s‖ ≤
      ((Γ*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hprofile⟩ := actual_first_moving_family_two_energies_uniform
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Kpush,hKpush,hpush⟩ := first_global_retained_push_uniform ε hε
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro ι κ _ _ p hp _ hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL hω₁ hω₂ hcut Benergy hBenergy
    Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hZ hscale hLe hleft hright
  let P₁:=Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let P₂:=Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hp₁:0<P₁:=by dsimp [P₁];positivity
  have hp₂:0<P₂:=by dsimp [P₂];positivity
  let G := Γ*Kpush*Y^ε
  let B₁ := Benergy/P₁
  let B₂ := Benergy/P₂
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hB₁ : 0 ≤ G*B₁ := by dsimp [B₁]; positivity
  have hB₂ : 0 ≤ G*B₂ := by dsimp [B₂]; positivity
  have hmono (coef : (Σ _ : κ,Ideal Eis×Eis)→Finset ι→ℂ) (sign : Bool) ω X t :
      firstFamilyEnergy p hg source F (fun x=>selector x.1) coef w sign ω X t (fun x=>x.2.2) ≤
      firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels b Y) F (fun x=>selector x.1)
        coef w sign ω X t (fun x=>x.2.2) := by
    unfold firstFamilyEnergy
    exact Finset.sum_le_sum_of_subset_of_nonneg hselected (fun x hx hn=>
      mul_nonneg (norm_nonneg _) (firstBlockEnergy_nonneg p hg _ _ _ _ _ _ _ _))
  have hb := hprofile p hp hg source F (fun x=>selector x.1) C₁ C₂ w ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK (fun x=>dd x.1) (fun x=>x.2.2) s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    hω₁ hω₂ hcut (G*B₁) (G*B₂) hB₁ hB₂
    (by
      intro z
      have he := hpush p hp hinj hcop hg hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd
        labels a Γ Y hΨ₁ hΨ₂ hΓ hY hlabels hn ha true H₁ selector ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (hs 7)
      simp only [ite_true,] at he
      apply ((hmono C₁ true ω₁ (s 7) _).trans he).trans
      change G * _ ≤ (G*B₁) * _
      rw [mul_assoc G B₁]
      apply mul_le_mul_of_nonneg_left _ hG
      dsimp only [B₁]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hp₁).mpr
      convert hleft z using 1 <;> dsimp only [P₁] <;> simp only [mul_comm, mul_left_comm, mul_assoc])
    (by
      intro z
      have he := hpush p hp hinj hcop hg hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd
        labels a Γ Y hΨ₁ hΨ₂ hΓ hY hlabels hn ha false H₂ selector ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (hs 8)
      simp only [ite_false,Bool.false_eq_true] at he
      apply ((hmono C₂ false ω₂ (s 8) _).trans he).trans
      change G * _ ≤ (G*B₂) * _
      rw [mul_assoc G B₂]
      apply mul_le_mul_of_nonneg_left _ hG
      dsimp only [B₂]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hp₂).mpr
      convert hright z using 1 <;> dsimp only [P₂] <;> simp only [mul_comm, mul_left_comm, mul_assoc])
  have hsqrt (U : ℝ) : Real.sqrt (G*(Benergy/U)) = Real.sqrt (G*Benergy) * Real.sqrt U⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, Real.sqrt_mul (mul_nonneg hG hBenergy)]
  have hroot : Real.sqrt (G*B₁)*Real.sqrt (G*B₂) =
      (Γ*Kpush*Y^ε*Benergy)*(Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹) := by
    rw [show G*B₁ = G*(Benergy/P₁) from rfl, show G*B₂ = G*(Benergy/P₂) from rfl, hsqrt, hsqrt]
    calc
      _ = (Real.sqrt (G*Benergy))^2*(Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹) := by ring
      _ = _ := by rw [Real.sq_sqrt (mul_nonneg hG hBenergy)]
  rw [hroot] at hb
  have hcancel:(Z^(-r-2*ell-V)*Z^M/firstRootScale s)*Real.exp ((9/2:ℝ)*L)*
      (Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹)=1:=by
    rw [hscale,hLe]
    exact first_unequal_prefactor Z hZ M r ell V delta aa₁ aa₂ bb rr tq hh eta
  have hnorm:0≤Z^(-r-2*ell-V)*Z^M:=by positivity
  apply (mul_le_mul_of_nonneg_left hb hnorm).trans_eq
  calc
    _=((Z^(-r-2*ell-V)*Z^M/firstRootScale s)*Real.exp ((9/2:ℝ)*L)*
      (Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹))*
      ((Γ*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)):=by ring
    _= _:=by rw [hcancel,one_mul]
end
end SevenEighths.InverseMoment

end OAI
