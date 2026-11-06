module

public import OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneous
public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceAllocatedErrorMass

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceHomogeneousError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalReflectionErrorMass CenteredMomentNaturalFixedRaySource
open CenteredMomentOriginalRadialComparison
open CenteredMomentAbsoluteEnergy QuadraticInitialBound

theorem natural_remaining_homogeneous_bound {α : Type*} (F T : Finset α) (hT : T⊆F)
    (W : ℝ→ℂ) (bshort Bshort : ℝ) (b M : α→ℝ)
    (hBshort : 0≤Bshort) (hM : ∀j∈F,0≤M j)
    (hW : ∀x,‖W x‖≤Bshort) (hsW : Function.support W⊆Set.Iic bshort)
    (χ : Character) (pool : α→Finset (Ideal HeckeFamily.O)) (β : α→Ideal HeckeFamily.O→ℂ)
    (P : α→ℝ) (X omega : ℝ) (hX : 0<X) (hP : ∀j∈T,0<P j)
    (hβ : ∀j∈T,∀I∈pool j,‖β j I‖≤M j)
    (hs : ∀j∈T,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) :
    ‖polynomial χ false W X 0 omega*∏j∈T,naturalSlot χ (pool j) (β j) (P j)‖^2≤
      errorConstant F bshort 1 b M*Bshort^2*X*∏j∈T,P j := by
  have hshort:=pow_le_pow_left₀ (norm_nonneg _)
    (plain_polynomial_bound χ W bshort Bshort X omega hBshort hX hW hsW) 2
  rw [mul_pow,Real.sq_sqrt hX.le] at hshort
  have hj (j:α) (hj:j∈T):
      ‖naturalSlot χ (pool j) (β j) (P j)‖^2≤(128*max 1 (b j)*M j)^2*P j := by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (naturalSlot_ideal_bound χ (pool j) (β j) (b j) (M j) (P j)
        (by grind) (by grind) (by grind) (by grind)) 2
    simpa only [mul_pow,Real.sq_sqrt (hP j hj).le] using hh
  have hc₀ : (128*max 1 bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort 1 b M := by
    have hp : (∏j∈T,(128*max 1 (b j)*M j)^2)≤∏j∈F,max 1 ((128*max 1 (b j)*M j)^2) :=
      (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) (by simp)).trans
        (Finset.prod_le_prod_of_subset_of_one_le₀ hT (by simp)
          (by simp))
    unfold errorConstant
    simp only [mul_one]
    exact mul_le_mul (by simp) hp
      (by positivity) (by positivity)
  have hc : (128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort 1 b M*Bshort^2 := by
    calc
      _=((128*max 1 bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*Bshort^2:=by ring
      _≤_:=mul_le_mul_of_nonneg_right hc₀ (sq_nonneg Bshort)
  calc
    _ = ‖polynomial χ false W X 0 omega‖^2*∏j∈T,‖naturalSlot χ (pool j) (β j) (P j)‖^2 := by
      simp only [norm_mul,mul_pow,norm_prod,Finset.prod_pow]
    _ ≤ ((128*max 1 bshort*Bshort)^2*X)*∏j∈T,(128*max 1 (b j)*M j)^2*P j :=
      mul_le_mul hshort (Finset.prod_le_prod₀ (by simp) hj)
        (by positivity) (by positivity)
    _ = ((128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*(X*∏j∈T,P j) := by
      rw [Finset.prod_mul_distrib];ring
    _ ≤ (errorConstant F bshort 1 b M*Bshort^2)*(X*∏j∈T,P j) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hX.le (Finset.prod_nonneg (by grind)))
    _ = _ := by ring

theorem natural_reference_error_homogeneous {α:Type*}(F:Finset α)(bshort:ℝ)(b M:α→ℝ)
    (hM:∀i∈F,0≤M i):
    ∃C:ℝ,0<C ∧ ∀(T:Finset α),T⊆F → ∀W:𝓢(ℝ,ℂ),
      Function.support (W:ℝ→ℂ)⊆Set.Iic bshort →
      ∀(χ:HeckeFamily.O→Character)(pool:α→Finset (Ideal HeckeFamily.O))(β:α→Ideal HeckeFamily.O→ℂ)(P:α→ℝ)
        (t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:HeckeFamily.O→Prop),
      0<X → 0<K → (∀i∈T,0<P i) →
      (∀i∈T,∀I∈pool i,Prime I) →
      (∀i∈T,∀I∈pool i,‖β i I‖≤M i) →
      (∀i∈T,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) →
      (∀z:HeckeFamily.O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t *
        ∏i∈T,naturalSlot (χ z) (pool i) (heightCoefficient (β i) t) (P i)) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl Φ*max 1 K*X*∏i∈T,P i:=by
  refine ⟨errorConstant F bshort 1 b M,errorConstant_pos _ _ _ _ _,?_⟩
  intro T hT W hsW χ pool β P t X K Φ keep hX hK hP hp hβ hs hΦ
  let A:=(schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W
  have hA:0≤A:=apply_nonneg _ _
  have hWA:∀x,‖W x‖≤A:=SchwartzMap.norm_le_seminorm ℝ W
  let R:=fun z:HeckeFamily.O=>polynomial (χ z) false W X 0 t *
    ∏i∈T,naturalSlot (χ z) (pool i) (heightCoefficient (β i) t) (P i)
  let V:=errorConstant F bshort 1 b M*A^2*X*∏i∈T,P i
  have hV:0≤V:=by
    dsimp only [V]
    exact mul_nonneg (mul_nonneg (mul_nonneg (errorConstant_pos F bshort 1 b M).le
      (sq_nonneg A)) hX.le) (Finset.prod_nonneg (by grind))
  have hr(z:HeckeFamily.O):‖R z‖^2≤V:=by
    have hh:=natural_remaining_homogeneous_bound F T hT W bshort A b M hA hM hWA hsW
      (χ z) pool (fun i=>heightCoefficient (β i) t) P X t hX hP
      (fun i hi I hI=>by rw [heightCoefficient_norm _ _ _ (hp i hi I hI).ne_zero];simp_all)
      (fun i hi I hI hn=>hs i hi I hI (left_ne_zero_of_mul hn))
    exact hh
  have hsum:Summable (fun z:HeckeFamily.O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2):=
    Summable.of_nonneg_of_le (fun z=>by positivity)
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right V)
  apply (radialEnergy_le_absolute_mass R keep Φ K hΦ hsum).trans
  calc
    _≤∑'z:HeckeFamily.O,‖Φ (‖eisEmbedding z‖^2/K)‖*V:=hsum.tsum_le_tsum
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right V)
    _=(∑'z:HeckeFamily.O,‖Φ (‖eisEmbedding z‖^2/K)‖)*V:=tsum_mul_right
    _≤(diagonalControl Φ*max 1 K)*V:=mul_le_mul_of_nonneg_right
      (radial_weight_lattice_bound_all Φ K hK) hV
    _=_:=by linarith

end SevenEighths.CenteredMomentEnergyReferenceHomogeneousError

end

end OAI
