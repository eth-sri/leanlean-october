/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/AdicLifting.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Discretization

@[expose] public section

namespace OAI.EuclideanRamsey


noncomputable section

open scoped TensorProduct


section NilpotentLog
variable {R : Type*} [CommRing R] [Algebra ℚ R]
open Finset PowerSeries
lemma nil_exp_quadratic {a : R} (ha : IsNilpotent a) :
    ∃ c : R, IsNilpotent.exp a = 1 + a * (1 + a * c) := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨∑ i ∈ range n, ((i + 2).factorial : ℚ)⁻¹ • a ^ i, ?_⟩
  rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_add_right n 2) hn)]
  rw [show n + 2 = 2 + n by omega, sum_range_add]
  simp [sum_range_succ, pow_add, mul_sum, add_comm 2, mul_add]
  ring_nf

lemma nil_exp_eq_one_iff {a : R} (ha : IsNilpotent a) :
    IsNilpotent.exp a = 1 ↔ a = 0 := by
  obtain ⟨c, he⟩ := nil_exp_quadratic ha
  have hb := (Commute.all a c).isNilpotent_mul_right ha
  rw [he, add_eq_left, hb.isUnit_one_add.mul_left_eq_zero]

omit [Algebra ℚ R] in
lemma nilpotent_of_mem_nil_ideal {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)
    {x : R} (hx : x ∈ I) : IsNilpotent x := by
  refine ⟨n, ?_⟩
  have := Ideal.pow_mem_pow hx n
  simp_all

lemma nil_exp_series {a : R} (ha : IsNilpotent a) :
    constantCoeff ((exp R).subst (C a)) = IsNilpotent.exp a := by
  have hC : HasSubst (C a : PowerSeries R) := by simpa [HasSubst,PowerSeries.C] using ha
  obtain ⟨n,hn⟩ := ha
  rw [IsNilpotent.exp_eq_sum hn, constantCoeff_eq, constantCoeff_subst hC]
  simp only [coeff_exp, map_pow, PowerSeries.C, MvPowerSeries.constantCoeff_C]
  rw [finsum_eq_sum_of_support_subset (s := range n)]
  · simp [Algebra.smul_def]
  · intro i hi
    by_contra h
    have hz : a^i = 0 := pow_eq_zero_of_le (by simpa using h) hn
    simp [hz] at hi

lemma nil_ideal_exp_surjective {I : Ideal R} {n : ℕ} (hI : I^n=⊥) {z : R} (hz : z∈I) :
    ∃ x∈I, IsNilpotent.exp x = 1+z := by
  have hzn : IsNilpotent z := nilpotent_of_mem_nil_ideal hI hz
  have hC : HasSubst (C z : PowerSeries R) := by simpa [HasSubst,PowerSeries.C] using hzn
  let l := (log R).subst (C z)
  let x := constantCoeff l
  have hx : IsNilpotent x := by
    simpa only [HasSubst, coe_substAlgHom, ← constantCoeff_eq] using (HasSubst.log (A:=R)).comp hC
  refine ⟨x,?_,?_⟩
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    change constantCoeff (((log R).subst (C z)).map (Ideal.Quotient.mk I)) = 0
    rw [map_subst hC, map_log]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hz,PowerSeries.C]
  · rw [← nil_exp_series hx]
    change constantCoeff ((exp R).subst (C (constantCoeff l))) = _
    have hl : C (constantCoeff l) = l := by
      ext m
      cases m with
      | zero => simp
      | succ m => simp [l,coeff_subst' hC,← map_pow]
    rw [hl, ← subst_comp_subst_apply HasSubst.log hC, subst_exp_log]
    simp [subst_add hC, subst_X hC, ← coe_substAlgHom hC]

lemma nil_exp_injective {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥) {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    (he : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  have hna := nilpotent_of_mem_nil_ideal hI ha
  have hnb := nilpotent_of_mem_nil_ideal hI hb
  have hnd := nilpotent_of_mem_nil_ideal hI (I.sub_mem ha hb)
  apply sub_eq_zero.mp
  apply (nil_exp_eq_one_iff hnd).mp
  rw [sub_eq_add_neg, IsNilpotent.exp_add_of_commute (Commute.all _ _) hna hnb.neg,
    he, hnb.exp_mul_exp_neg_self]

end NilpotentLog

section LatticeLog
variable {k : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

def rationalExtension (f : (Fin k → ℤ) →+ R) : (Fin k → ℚ) →ₗ[ℚ] R :=
  Fintype.linearCombination ℚ (fun j => f (Pi.single j 1))

lemma rationalExtension_lattice (f : (Fin k → ℤ) →+ R) (γ : Fin k → ℤ) :
    rationalExtension f (fun j => (γ j : ℚ)) = f γ := by
  simp only [rationalExtension, Fintype.linearCombination_apply]
  simp_rw [Int.cast_smul_eq_zsmul, ← map_zsmul]
  rw [← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply]

end LatticeLog

section Construction
variable {k : ℕ}

def cosetIdeal (Λ : AddSubgroup (Lattice k)) : Ideal (LatticeRing k) :=
  RingHom.ker (cosetPushforward Λ)

lemma quotient_nil_augmentation (N : ℕ) :
    (Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N))
      (augmentationIdeal : Ideal (LatticeRing k))) ^ N = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem finite_lattice_identity {k s : ℕ}
    (Λ : Fin s → AddSubgroup (Lattice k)) (C : Matrix (Fin k) (Fin k) ℚ)
    (hCs : C.IsSymm) (hC : ∀ i, quotientTensor (Λ i) (matrixTensor C) = 0) :
    ∃ ν : LatticeRing k, (∀ i, cosetPushforward (Λ i) ν = 0) ∧ mass ν = 0 ∧
      (∀ a, firstMoment ν a = 0) ∧ (∀ a b, secondMoment ν a b = C a b) := by
  let I : Ideal (LatticeRing k) := augmentationIdeal
  classical
  let J (i) := cosetIdeal (Λ i)
  let F : LatticeRing k →ₗ[LatticeRing k] (∀ i : Fin s, LatticeRing k ⧸ J i) :=
    LinearMap.pi (fun i => Algebra.linearMap _ (LatticeRing k ⧸ J i))
  obtain ⟨r, hr⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range F)
  let n := r+3
  have hn x (hx : ∀ i, x ∈ J i ⊔ I ^ n) :
      ∃ y, (∀ i, y ∈ J i) ∧ x-y ∈ I ^ 3 := by
    have hm : F x ∈ I ^ n • (⊤ : Submodule (LatticeRing k) (∀ i : Fin s, LatticeRing k ⧸ J i)) := by
      have hz : ∀ i, ∃ z ∈ I ^ n, (Ideal.Quotient.mk (J i)) z = (Ideal.Quotient.mk (J i)) x := by
        intro i
        obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp (hx i)
        refine ⟨z, hz, ?_⟩
        rw [← he, map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hy, zero_add]
      choose z hz he using hz
      have he' : F x = ∑ i, z i • Pi.single i (1 : LatticeRing k ⧸ J i) := by
        simp_rw [← Pi.single_smul]
        change F x = ∑ i, Pi.single i (z i • (Submodule.Quotient.mk (1 : LatticeRing k) : LatticeRing k ⧸ J i))
        simp_rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Ideal.Quotient.mk_eq_mk, he]
        exact (Finset.univ_sum_single _).symm
      rw [he']
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (hz i) Submodule.mem_top)
    have hfx : F x ∈ I ^ (r+3) • ⊤ ⊓ LinearMap.range F := ⟨hm, ⟨x, rfl⟩⟩
    rw [hr (r+3) (by omega), Nat.add_sub_cancel_left] at hfx
    have hf'  := (smul_mono_right _ inf_le_right : I ^ 3 • (I ^ r • ⊤ ⊓ LinearMap.range F) ≤ _) hfx
    have heq : I ^ 3 • LinearMap.range F = Submodule.map F (I ^ 3 • ⊤) := by
      rw [Submodule.map_smul'']; simp
    rw [heq] at hf'
    obtain ⟨z, hz, he⟩ := hf'
    refine ⟨x-z, ?_, ?_⟩
    · have hy : F (x-z) = 0 := by rw [map_sub, he, sub_self]
      intro i
      exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hy i)
    · simpa [Ideal.smul_eq_mul] using hz
  let N := n + 3
  let χ :=
    (Ideal.Quotient.mk ((augmentationIdeal : Ideal (LatticeRing k)) ^ N)).toMonoidHom.comp (AddMonoidAlgebra.of ℚ (Lattice k))
  have hχ : ∀ γ : Lattice k, χ (Multiplicative.ofAdd γ) - 1 ∈
      Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal := by
    intro γ
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk (augmentationIdeal ^ N))
      (show AddMonoidAlgebra.single γ 1 - 1 ∈ (augmentationIdeal : Ideal (LatticeRing k)) by
        change mass _ = 0; simp [mass])
    simpa [χ, AddMonoidAlgebra.of_apply, map_sub] using h
  choose g hg he using fun γ => nil_ideal_exp_surjective (quotient_nil_augmentation N) (hχ γ)
  have he (γ) : IsNilpotent.exp (g γ) = χ (Multiplicative.ofAdd γ) := by simpa using he γ
  let f : Lattice k →+ (LatticeRing k ⧸ augmentationIdeal ^ N) := {
    toFun := g
    map_zero' := by
      apply nil_exp_injective (quotient_nil_augmentation N) (hg _) (Ideal.zero_mem _)
      simp [he]
    map_add' a b := by
      apply nil_exp_injective (quotient_nil_augmentation N) (hg _)
        (Ideal.add_mem _ (hg _) (hg _))
      rw [he, IsNilpotent.exp_add_of_commute (Commute.all _ _)
        (nilpotent_of_mem_nil_ideal (quotient_nil_augmentation N) (hg _))
        (nilpotent_of_mem_nil_ideal (quotient_nil_augmentation N) (hg _)), he, he]
      exact χ.map_mul _ _ }
  have hf (γ) := hg γ
  have hfexp (γ) : IsNilpotent.exp (f γ) =
      (Ideal.Quotient.mk (augmentationIdeal ^ N)) (AddMonoidAlgebra.single γ 1) := by
    simpa [f, χ, AddMonoidAlgebra.of_apply] using he γ
  let q := Ideal.Quotient.mk (I ^ N)
  let M := Ideal.map q I
  have hex : ∀ a : Fin k, ∃ x ∈ I, q x = f (Pi.single a 1) := by
    intro a
    exact (Ideal.mem_map_iff_of_surjective q (Ideal.Quotient.mk_surjective)).mp (hf _)
  choose l hlI hl using hex
  have hfirst : ∀ a b, firstMoment (l a) b = if a = b then 1 else 0 := by
    have hpre : Ideal.comap q (Ideal.map q (I ^ 2)) = I ^ 2 := by
      rw [Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact sup_eq_left.mpr (Ideal.pow_le_pow_right (show 2 ≤ N by omega))
    intro a b
    let z : LatticeRing k := AddMonoidAlgebra.single (Pi.single a 1) 1 - 1
    have hdiff : l a - z ∈ I ^ 2 := by
      rw [← hpre]
      change q (l a - z) ∈ Ideal.map q (I ^ 2)
      rw [Ideal.map_pow]
      have hn : IsNilpotent (f (Pi.single a 1)) := nilpotent_of_mem_nil_ideal (quotient_nil_augmentation N) (hf (Pi.single a 1))
      have hre : q (l a - z) = -(IsNilpotent.exp (f (Pi.single a 1)) - 1 - f (Pi.single a 1)) := by
        rw [hfexp, map_sub, hl]
        dsimp [z, q]
        rw [map_sub, map_one]
        ring
      obtain ⟨c,hc⟩ := nil_exp_quadratic hn
      rw [hre,hc]
      convert (M^2).neg_mem ((M^2).mul_mem_right c (Ideal.pow_mem_pow (hf (Pi.single a 1)) 2)) using 1 <;> simp [f] <;> ring
    simpa [z,AddMonoidAlgebra.one_def,Pi.single_apply,eq_comm (a := a) (b := b),sub_eq_zero] using
      (augmentation_sq_moments hdiff).2 b
  have hxN (i) : quadraticStencil C l ∈ cosetIdeal (Λ i) ⊔ I ^ N := by
    let J := cosetIdeal (Λ i) ⊔ (augmentationIdeal : Ideal (LatticeRing k)) ^ N
    let ψ := Ideal.Quotient.factorₐ ℚ (show augmentationIdeal ^ N ≤ J from le_sup_right)
    let g := ψ.toLinearMap.comp (rationalExtension f)
    have hgγ : ∀ γ ∈ Λ i, g (rationalize γ) = 0 := by
      intro γ hγ
      have hn : IsNilpotent (f γ) :=
        nilpotent_of_mem_nil_ideal (quotient_nil_augmentation N) (hf γ)
      change ψ (rationalExtension f (rationalize γ)) = 0
      rw [show rationalize γ = (fun j => (γ j : ℚ)) from rfl, rationalExtension_lattice]
      apply (nil_exp_eq_one_iff (hn.map ψ)).mp
      rw [← hn.map_exp ψ, hfexp]
      change (Ideal.Quotient.mk J) (AddMonoidAlgebra.single γ 1) = 1
      apply (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr
      apply Ideal.mem_sup_left
      change cosetPushforward (Λ i) (AddMonoidAlgebra.single γ 1 - 1) = 0
      rw [map_sub,map_one]
      simp [cosetPushforward,(QuotientAddGroup.eq_zero_iff γ).mpr hγ]
      exact sub_self _
    have hg : latticeSpan (Λ i) ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      rintro _ ⟨γ, hγ, rfl⟩
      exact hgγ γ hγ
    let u := (latticeSpan (Λ i)).liftQ g hg
    have hquad := congrArg ((Algebra.TensorProduct.lmul' ℚ).toLinearMap.comp
      (TensorProduct.map u u)) (hC i)
    simp [u, quotientTensor, matrixTensor, LinearMap.comp_apply] at hquad
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ ℚ J) (quadraticStencil C l) = 0
    have hlj : ∀ a, (Ideal.Quotient.mkₐ ℚ J) (l a) = g (Pi.single a 1) := by
      intro a
      change ψ (q (l a)) = ψ (rationalExtension f (Pi.single a 1))
      rw [hl]
      simp [rationalExtension]
    simp only [quadraticStencil, map_smul, map_sum, map_mul, hlj, hquad, smul_zero]
  have hx : ∀ i, quadraticStencil C l ∈ cosetIdeal (Λ i) ⊔ I ^ n := by
    intro i
    apply (sup_le_sup_left (α := Ideal (LatticeRing k))
      (Ideal.pow_le_pow_right (show n ≤ N by omega)) (cosetIdeal (Λ i)))
    exact hxN i
  obtain ⟨y, hy, hxy⟩ := hn (quadraticStencil C l) hx
  have he := augmentation_cube_moments hxy
  simp [sub_eq_zero] at he
  have hM := quadraticStencil_moments C hCs l hlI hfirst
  refine ⟨y, hy, ?_, ?_, ?_⟩
  · exact he.1.symm.trans hM.1
  · grind
  · simp_all

end Construction

end

end OAI.EuclideanRamsey
