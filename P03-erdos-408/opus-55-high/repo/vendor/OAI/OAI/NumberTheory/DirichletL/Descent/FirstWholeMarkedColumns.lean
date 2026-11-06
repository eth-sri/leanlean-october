module

public import OAI.NumberTheory.DirichletL.Descent.FirstMarkedZero

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped Classical
open FirstPassCubeLabels SecondPassArithmetic

theorem primeProductNorm_union_le_mul {ι : Type*} [DecidableEq ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal] (A U : Finset ι) :
    primeProductNorm p (A∪U)≤primeProductNorm p A*primeProductNorm p U := by
  have he : A∪U=A∪(U\A) := by ext i;simp only [Finset.mem_union,Finset.mem_sdiff];tauto
  rw [he,primeProductNorm_union p A (U\A) Finset.disjoint_sdiff]
  exact mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp Finset.sdiff_subset)
    (primeProductNorm_pos p hp A).le

theorem whole_cube_marked_test_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ,0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→ActualEisensteinCubic.O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (extra : Finset ι) (test : Finset ι→ℂ) (E G L : ℝ),0≤E → 0≤G → 0≤L →
      primeProductNorm p extra≤E → (∀ U,‖test U‖≤G) →
      (∀ U,test U≠0→primeProductNorm p U≤L) →
      ∀ U,‖primeMark slots lists a (extra∪U)*test U‖≤Cm*(E*L)^ε*G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha extra test E G L hE hG hL he hb hs U
  by_cases hz : test U=0
  · simp only [hz,mul_zero,norm_zero];positivity
  have hnorm : primeProductNorm p (extra∪U)≤E*L :=
    (primeProductNorm_union_le_mul p hp extra U).trans
      (mul_le_mul he (by grind) (primeProductNorm_pos p hp U).le hE)
  have hnorm0 := (primeProductNorm_pos p hp (extra∪U)).le
  rw [norm_mul]
  calc
    _ ≤ (Cm*(primeProductNorm p (extra∪U))^ε)*G :=
      mul_le_mul (hmark p hp hcop slots lists a hslots ha _) (hb U) (norm_nonneg _) (by positivity)
    _ ≤ _ := by gcongr

end
end SevenEighths.InverseMoment

end OAI
