/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/AdicLifting.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system and shortened.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.StencilConvolution

public section


open scoped TensorProduct

set_option autoImplicit true
namespace OAI.EuclideanRamsey
set_option hygiene false
local notation "𝔞" => (Pi.single a 1)
notation "𝔦" => (Λ i)

variable [CommRing R] [Algebra ℚ R]

lemma nil_exp_quadratic {a : R} (ha : IsNilpotent a) :
    ∃ c, IsNilpotent.exp a = 1 + a + a^2 * c := by
  obtain ⟨n, hn⟩ := ha
  rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_add_right n 2) hn), add_comm n, Finset.sum_range_add]
  exact ⟨∑ i ∈ Finset.range n, ((2 + i).factorial : ℚ)⁻¹ • a ^ i, by
    simp [Finset.sum_range_succ, Finset.mul_sum, pow_add]⟩

lemma nil_exp_eq_one_iff {a : R} (ha : IsNilpotent a) : IsNilpotent.exp a = 1 ↔ a = 0 := by
  obtain ⟨c, hc⟩ := nil_exp_quadratic ha
  refine ⟨fun h => (Commute.all a c).isNilpotent_mul_right ha |>.isUnit_one_add.mul_right_cancel ?_, fun h => by grind⟩
  linear_combination h - hc

notation "𝔫" => nilpotent_of_mem_nil_ideal hI

section
variable {I : Ideal R} (hI : I ^ n = ⊥)
include hI

omit [Algebra ℚ R] in
lemma nilpotent_of_mem_nil_ideal (hx : x ∈ I) :
    IsNilpotent x := ⟨n, by simpa [hI] using Ideal.pow_mem_pow hx n⟩

lemma nil_ideal_exp_surjective (hw : w - 1 ∈ I) :
    ∃ x ∈ I, IsNilpotent.exp x = w := by
  have (m : ℕ) : ∃ x ∈ I, IsNilpotent.exp x - w ∈ I ^ (m + 1) := by
    induction m with
    | zero => exact ⟨0, I.zero_mem, by simpa using I.neg_mem hw⟩
    | succ m ih =>
      obtain ⟨x, hx, he⟩ := ih
      have hei := Ideal.pow_le_self m.succ_ne_zero he
      obtain ⟨c, hc⟩ := nil_exp_quadratic (𝔫 (I.neg_mem hei))
      obtain ⟨d, hd⟩ := nil_exp_quadratic (𝔫 hx)
      refine ⟨x + -(IsNilpotent.exp x - w), I.add_mem hx (I.neg_mem hei), ?_⟩
      rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) (𝔫 hx)
        (𝔫 (I.neg_mem hei)), hc]
      have h1 := Ideal.mul_mem_mul he (I.mul_mem_right (1 + x * d) hx)
      have h2 := Ideal.mul_mem_right (IsNilpotent.exp x * c) _ (Ideal.pow_mem_pow he 2)
      rw [← pow_succ, ← pow_mul] at *
      convert sub_mem (Ideal.pow_le_pow_right (by omega) h2) h1 using 1
      rw [hd]
      ring
  obtain ⟨x, hx, he⟩ := this n
  simp [pow_succ, hI, sub_eq_zero] at he
  exact ⟨x, hx, he⟩

lemma nil_exp_injective (ha : a ∈ I) (hb : b ∈ I)
    (he : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  rw [← sub_eq_zero, ← nil_exp_eq_one_iff (𝔫 (I.sub_mem ha hb)), sub_eq_add_neg,
    IsNilpotent.exp_add_of_commute (Commute.all _ _) (𝔫 ha)
    (𝔫 hb).neg, he, (𝔫 hb).exp_mul_exp_neg_self]
end

lemma adic_intersection_lifting [IsNoetherianRing R] [Fintype ι]
    I (J : ι → Ideal R) q :
    ∃ n, ∀ x, (∀ i, x ∈ J i ⊔ I ^ n) → ∃ y, (∀ i, y ∈ J i) ∧ x - y ∈ I ^ q := by
  classical
  let f : R →ₗ[R] (∀ i, R ⧸ J i) := LinearMap.pi fun i => Algebra.linearMap R (R ⧸ J i)
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨k + q, fun x hx => ?_⟩
  choose y hy z hz he using fun i => Submodule.mem_sup.mp (hx i)
  have : f x = ∑ i, z i • Pi.single i (1 : R ⧸ J i) := by
    simp_rw [← Pi.single_smul, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Finset.univ_sum_single]
    ext i
    simp [f, ← he i, Ideal.Quotient.eq_zero_iff_mem.mpr (hy i)]
  have hfx : f x ∈ I ^ (k + q) • (⊤ : Submodule R (∀ i, R ⧸ J i)) ⊓ LinearMap.range f :=
    ⟨this ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hz i) Submodule.mem_top, x, rfl⟩
  rw [hk _ le_self_add, Nat.add_sub_cancel_left] at hfx
  obtain ⟨w, hw, hw'⟩ : f x ∈ (I ^ q • ⊤ : Submodule R R).map f := by
    rw [Submodule.map_smul'']; simpa using (smul_mono_right _ inf_le_right : _ ≤ I ^ q • LinearMap.range f) hfx
  exact ⟨x - w, fun i => Ideal.Quotient.eq_zero_iff_mem.mp (by
    simpa [f] using congrFun (show f (x - w) = 0 by grind) i), by simpa using hw⟩
theorem finite_lattice_identity (Λ : Fin s → AddSubgroup (Lattice k)) C
    (hCs : C.IsSymm) (hC : ∀ i, quotientTensor 𝔦 (matrixTensor C) = 0) :
    ∃ ν, (∀ i, cosetPushforward 𝔦 ν = 0) ∧ mass ν = 0 ∧
      (∀ a, firstMoment ν a = 0) ∧ (∀ a b, secondMoment ν a b = C a b) := by
  let I := @augmentationIdeal k
  let K i := RingHom.ker (AddMonoidAlgebra.mapDomainRingHom ℚ (QuotientAddGroup.mk' 𝔦))
  obtain ⟨n, hn⟩ := adic_intersection_lifting I K 3
  let N := n + 3
  let q := Ideal.Quotient.mk (I ^ N)
  have hI : (I.map q) ^ N = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]
  choose g hg he using fun γ => nil_ideal_exp_surjective hI
    (by simpa using Ideal.mem_map_of_mem q (monomial_sub_one_mem γ))
  let f : Lattice k →+ _ := AddMonoidHom.mk' g fun a b => nil_exp_injective hI (hg _) (add_mem (hg a) (hg b)) (by
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) (𝔫 (hg a))
      (𝔫 (hg b)), he, he, he, ← map_mul, AddMonoidAlgebra.single_mul_single, mul_one])
  choose l hlI hl using fun a =>
    (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp (hg 𝔞)
  have hfirst a b : firstMoment (l a) b = if a = b then 1 else 0 := by
    obtain ⟨c, hc⟩ := nil_exp_quadratic (𝔫 (hg 𝔞))
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [he, ← hl, ← map_pow, ← map_mul, ← map_one q, ← map_add, ← map_add, Ideal.Quotient.eq] at hc
    have := (augmentation_sq_le_jetOne (show AddMonoidAlgebra.single 𝔞 1 - 1 - l a ∈ I ^ 2 by
      convert add_mem (Ideal.pow_le_pow_right (by grind) hc)
        (Ideal.mul_mem_right c _ (Ideal.pow_mem_pow (hlI a) 2)); ring)).2 b
    simp [moments_linear, sub_eq_zero, AddMonoidAlgebra.one_def] at this ⊢
    rw [← this]
    simp [Pi.single_apply, eq_comm]
  have hx i : quadraticStencil C l ∈ K i ⊔ I ^ n := by
    let ψ := Ideal.Quotient.factorₐ ℚ (le_sup_right : I ^ N ≤ K i ⊔ I ^ N)
    let g' := ψ.toLinearMap ∘ₗ Fintype.linearCombination ℚ fun j => f (Pi.single j 1)
    have hg' : latticeSpan 𝔦 ≤ LinearMap.ker g' := Submodule.span_le.mpr <| by
      rintro _ ⟨γ, hγ, rfl⟩
      have hn := 𝔫 (hg γ)
      have : f γ = ∑ j, (γ j : ℚ) • f (Pi.single j 1) := by
        conv_lhs => rw [← Finset.univ_sum_single γ]
        simp only [map_sum, Int.cast_smul_eq_zsmul]
        congr! with j
        rw [← map_zsmul, ← Pi.single_smul, smul_eq_mul, mul_one]
      simp only [SetLike.mem_coe, LinearMap.mem_ker, g', LinearMap.comp_apply, Fintype.linearCombination_apply,
        rationalize, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ← this]
      refine (nil_exp_eq_one_iff (hn.map ψ)).mp ?_
      rw [← hn.map_exp ψ, he]
      simp only [ ← map_one (Ideal.Quotient.mk _)]
      exact Ideal.Quotient.eq.mpr (Ideal.mem_sup_left (by simp only [K, RingHom.mem_ker, map_sub, sub_eq_zero]; simp [(QuotientAddGroup.eq_zero_iff γ).mpr hγ, AddMonoidAlgebra.one_def]))
    have := congrArg ((Algebra.TensorProduct.lmul' ℚ).toLinearMap ∘ₗ
      TensorProduct.map ((latticeSpan 𝔦).liftQ g' hg') ((latticeSpan 𝔦).liftQ g' hg')) (hC i)
    simp [matrixTensor, quotientTensor] at this
    have h2 a : Ideal.Quotient.mk (K i ⊔ I^N) (l a) = g' 𝔞 := by
      simp [g', ψ, f, q, ← hl, Ideal.Quotient.factor_mk]
    refine (sup_le_sup_left (Ideal.pow_le_pow_right (by grind)) (K i) : K i ⊔ I ^ N ≤ _) (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
    rw [← Ideal.Quotient.mkₐ_eq_mk ℚ]
    simp only [quadraticStencil, map_smul, map_sum, map_mul, Ideal.Quotient.mkₐ_eq_mk, h2, this, smul_zero]
  obtain ⟨y, hy, hxy⟩ := hn _ hx
  have he := moments_eq_of_sub_mem_cube hxy
  have hM := quadraticStencil_moments C hCs l (fun a => (mem_augmentationIdeal _).mp (hlI a)) hfirst
  refine ⟨y, fun i => ?_, he.1.symm.trans hM.1, fun a => (he.2.1 a).symm.trans (hM.2.1 a),
    fun a b => (he.2.2 a b).symm.trans (hM.2.2 a b)⟩
  exact congrArg AddMonoidAlgebra.coeff (hy i)
