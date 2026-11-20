module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Descent.FirstUnequalPhysicalEnergy
public import OAI.NumberTheory.DirichletL.Descent.FirstGlobalPush
public import OAI.NumberTheory.DirichletL.Descent.FirstHeightBudget

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
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
    [OAI.PrincipalFamily.Maximal p]
    (hg : OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : OAI.PrincipalFamily.Coprime p)
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
  obtain ⟨Cprofile,hCprofile,hmeasure⟩ := first_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Kpush,hKpush,hpush⟩ := first_retained_actual_second_energy ε hε
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro ι κ _ _ p hp _ hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL hω₁ hω₂ hcut Benergy hBenergy
    Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hZ hscale hLe hleft hright
  let P₁:=Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let P₂:=Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hp₁:0<P₁:=by dsimp [P₁];positivity
  have hp₂:0<P₂:=by dsimp [P₂];positivity
  let scale := Γ*Kpush*Y^ε
  have hscale0 : 0 ≤ scale := by dsimp [scale];positivity
  have hweight : 0 ≤ scale*Benergy := mul_nonneg hscale0 hBenergy
  have push (negative : Bool) (H' : κ → Finset ι → ℂ) (ω : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) :=
    Finset.sum_le_sum (s := outer) (fun k hk =>
      hpush p hp hinj hcop hg hc hpr F (b k) (common k) Ψ₁ Ψ₂ hΨ₁ hΨ₂ mleft mright
        (dd k) (labels k) (a k) Γ Y hΓ hY (hlabels k hk) (hn k hk) (ha k hk)
        negative (H' k) (selector k) ω X t hX)
  have hRad : 0 < K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8) := by
    have := hs 3; have := hs 4; have := hs 5; have := hs 6; have := hs 7; have := hs 8
    positivity
  obtain ⟨b₃,hb₃⟩ := hmeasure _ hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  have he := actual_first_family_two_energies p hg hp source F (fun x=>selector x.1) C₁ C₂ w
    (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) ω₁ ω₂ Φ (fun i y => U₀ i (y+ρ i))
    A₁ A₂ C R K L (fun x=>dd x.1) (fun x=>x.2.2) s hpos hs _
    (first_balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L) hsep hω₁ hω₂ hcut
    J (scale*(Benergy/P₁)) (scale*(Benergy/P₂)) (by positivity) (by positivity) hWeighted
    (by
      intro z
      have he := push true H₁ ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (hs 7)
      simp only [ite_true, ←Finset.mul_sum] at he
      apply (firstFamilyEnergy_mono p hg hselected F _ C₁ w true ω₁ (s 7) _ _).trans
      simp only [firstFamilyEnergy,firstGlobalRetainedSource,Finset.sum_sigma]
      apply he.trans
      rw [mul_assoc scale]
      apply mul_le_mul_of_nonneg_left _ hscale0
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hp₁).mpr
      convert hleft z using 1 <;> dsimp only [P₁] <;> ring)
    (by
      intro z
      have he := push false H₂ ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (hs 8)
      simp only [Bool.false_eq_true, ite_false, ←Finset.mul_sum] at he
      apply (firstFamilyEnergy_mono p hg hselected F _ C₂ w false ω₂ (s 8) _ _).trans
      simp only [firstFamilyEnergy,firstGlobalRetainedSource,Finset.sum_sigma]
      apply he.trans
      rw [mul_assoc scale]
      apply mul_le_mul_of_nonneg_left _ hscale0
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hp₂).mpr
      convert hright z using 1 <;> dsimp only [P₂] <;> ring)
  have hm := (le_div_iff₀ (pow_pos (by linarith : 0 < 1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) Aker)).mpr
    ((mul_comm _ _).le.trans hMoment)
  have hb := he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hm (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (by have := firstRootScale_pos s hs; positivity))
  have hroot : Real.sqrt (scale*(Benergy/P₁))*Real.sqrt (scale*(Benergy/P₂)) =
      (scale*Benergy)*(Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹) := by
    simp only [div_eq_mul_inv, ←mul_assoc, Real.sqrt_mul hweight]
    calc
      _ = (Real.sqrt (scale*Benergy))^2*(Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹) := by ring
      _ = _ := by rw [Real.sq_sqrt hweight];ring
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
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)):=by dsimp [scale]; ring
    _= _:=by rw [hcancel,one_mul]
end
end SevenEighths.InverseMoment

end OAI
