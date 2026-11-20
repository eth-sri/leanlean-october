/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.ClassGroup.DiscriminantPrimeIdealCover
public import CCDN.ClassGroup.TwoTorsion
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section
namespace CCDN
noncomputable section
open NumberField Ideal UniqueFactorizationMonoid
open scoped nonZeroDivisors
variable (K F : Type*) [Field K] [Field F] [NumberField K] [NumberField F] [Algebra F K]

/-- If the extension of a squarefree ideal is a square, its primes all lie below ramification. -/
private lemma squarefree_support {T : Ideal (𝓞 F)} (hT : Squarefree T) (hT0 : T ≠ 0)
    (J : Ideal (𝓞 K)) (he : T.map (algebraMap (𝓞 F) (𝓞 K)) = J^2) :
    (normalizedFactors T).toFinset ⊆ (discriminantPrimeIdealCover K).image (Ideal.under (𝓞 F)) := by
  classical
  intro P hP
  have hm := Multiset.mem_toFinset.mp hP
  have hpr := prime_of_normalized_factor P hm
  have _ := Ideal.isPrime_of_prime hpr
  obtain ⟨U,hu⟩ := dvd_of_mem_normalizedFactors hm
  let φ := algebraMap (𝓞 F) (𝓞 K)
  obtain ⟨Q,hQ,hQP⟩ := Classical.ofNonempty (α := P.primesOver (𝓞 K))
  have _ := hQ
  have _ := hQP
  have hQ0 := Ideal.ne_bot_of_liesOver_of_ne_bot hpr.ne_zero Q
  refine Finset.mem_image.mpr ⟨Q, mem_discriminantPrimeIdealCover_of_ramified K F Q hQ0 ?_, hQP.over.symm⟩
  have hU : U ≠ 0 := by intro h; simp_all
  have hnot : Q ∉ normalizedFactors (U.map φ) := by
    intro hh
    have hle := Ideal.map_le_iff_le_comap.mp ((Ideal.mem_normalizedFactors_iff (Ideal.map_ne_bot_of_ne_bot hU)).mp hh).2
    have hd : P ∣ U := Ideal.dvd_iff_le.mpr (hQP.over ▸ hle)
    exact hpr.not_isUnit (hT P (hu ▸ mul_dvd_mul_left P hd))
  intro hidx
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count P Q (Ideal.map_ne_bot_of_ne_bot hpr.ne_zero)] at hidx
  rw [hu,Ideal.map_mul] at he
  have hh := congrArg (fun I : Ideal (𝓞 K) => (normalizedFactors I).count Q) he
  change (normalizedFactors (P.map φ * U.map φ)).count Q = (normalizedFactors (J^2)).count Q at hh
  rw [normalizedFactors_mul (x := P.map φ) (y := U.map φ) (Ideal.map_ne_bot_of_ne_bot hpr.ne_zero) (Ideal.map_ne_bot_of_ne_bot hU),Multiset.count_add,
    normalizedFactors_pow,Multiset.count_nsmul, Multiset.count_eq_zero_of_notMem hnot, hidx] at hh
  omega

/-- Write a nonzero principal ideal downstairs as `A² T`. When its extension
is a square, the squarefree part `T` is determined by a subset of a fixed prime cover. -/
private theorem square_parts {x : 𝓞 F} (hx : x ≠ 0) {J : (Ideal (𝓞 K))⁰}
    (hJ : (Ideal.span {x}).map (algebraMap (𝓞 F) (𝓞 K)) = (J : Ideal (𝓞 K))^2) :
    ∃ (A T : (Ideal (𝓞 F))⁰) (I : (Ideal (𝓞 K))⁰), (A:Ideal (𝓞 F))^2 * T = Ideal.span {x} ∧
      J = ClassGroup.extendedIdeal (𝓞 F) (𝓞 K) A * I ∧ (T:Ideal (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 K)) = (I:Ideal (𝓞 K))^2 ∧
      Squarefree (T:Ideal (𝓞 F)) ∧ (normalizedFactors (T:Ideal (𝓞 F))).toFinset ⊆
        (discriminantPrimeIdealCover K).image (Ideal.under (𝓞 F)) := by
  classical
  obtain ⟨A,T,he,ht⟩ := exists_sq_mul_squarefree (Ideal.span {x})
  have h0 : A^2 * T ≠ 0 := by simpa [he] using hx
  have ha : A ≠ 0 := by intro h; simp [h] at h0
  have ht0 := right_ne_zero_of_mul h0
  let φ := algebraMap (𝓞 F) (𝓞 K)
  have he' := congrArg (Ideal.map φ) he
  rw [Ideal.map_mul,Ideal.map_pow,hJ] at he'
  obtain ⟨I,hi⟩ := (pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp (show (A.map φ)^2 ∣ (J:Ideal (𝓞 K))^2 from ⟨_,he'.symm⟩)
  have hi0 : I ≠ 0 := by intro h; exact nonZeroDivisors.coe_ne_zero J (by simpa [h] using hi)
  rw [hi,mul_pow] at he'
  have ht' := mul_left_cancel₀ (pow_ne_zero _ (Ideal.map_ne_bot_of_ne_bot ha)) he'
  exact ⟨⟨A,mem_nonZeroDivisors_of_ne_zero ha⟩,⟨T,mem_nonZeroDivisors_of_ne_zero ht0⟩,⟨I,mem_nonZeroDivisors_of_ne_zero hi0⟩,
    he,Subtype.ext hi,ht',ht,squarefree_support K F ht ht0 I ht'⟩

private lemma count_by_square_fibers {ι τ G : Type*} [Finite τ] [CommGroup G] [Finite G]
    (t : ι → τ) (a : ι → G) (hsq : ∀ i j, t i = t j → (a i)^2 = (a j)^2)
    (hinj : ∀ i j, t i = t j → a i = a j → i = j) :
    Nat.card ι ≤ Nat.card (powMonoidHom 2 : G →* G).ker * Nat.card τ := by
  classical
  let r (l : Set.range t) := l.property.choose
  let b (i : ι) := r ⟨t i,i,rfl⟩
  have hb i : t (b i) = t i := (show t i ∈ Set.range t from ⟨i,rfl⟩).choose_spec
  let k (i : ι) : (powMonoidHom 2 : G →* G).ker := ⟨a i / a (b i), by change (a i / a (b i))^2 = 1; rw [div_pow,hsq i (b i) (hb i).symm,div_self']⟩
  rw [← Nat.card_prod]
  apply Nat.card_le_card_of_injective (fun i => (k i,t i))
  intro i j h
  have ht := congrArg Prod.snd h
  have he : b i = b j := congrArg r (Subtype.ext ht)
  apply hinj i j ht
  have hv := congrArg (fun p : (powMonoidHom 2 : G →* G).ker × τ => p.1.val) h
  simpa only [k, he,div_left_inj] using hv

/-- Count ideal classes whose square generators descend to the base. The
squarefree part `T` records only ramified primes. At fixed `T`, `[A]^2` and
the residual ideal upstairs are fixed, leaving at most `h₂(F)` possibilities. -/
theorem descended_square_class_count (K F : Type*) [Field K] [Field F] [NumberField K] [NumberField F] [Algebra F K]
    {ι : Type*} (J : ι → (Ideal (𝓞 K))⁰) (hinj : Function.Injective (ClassGroup.mk0 ∘ J))
    (x : ι → 𝓞 F) (hx : ∀ i, x i ≠ 0)
    (hJ : ∀ i, (Ideal.span {x i}).map (algebraMap (𝓞 F) (𝓞 K)) = (J i : Ideal (𝓞 K))^2) :
    Nat.card ι ≤ classGroupTwoTorsionCard F * 2^(Module.finrank ℚ K*(NumberField.discr K).natAbs.primeFactors.card) := by
  classical
  let S := (discriminantPrimeIdealCover K).image (Ideal.under (𝓞 F))
  choose A T I hparts hfac hsquare hT hsub using fun i => square_parts K F (hx i) (hJ i)
  let t (i : ι) : S.powerset := ⟨(normalizedFactors (T i : Ideal (𝓞 F))).toFinset,Finset.mem_powerset.mpr (hsub i)⟩
  have hdet (i j) (h : t i = t j) : T i = T j := by
    have hp (k) : (t k).val.val.prod = T k := by
      dsimp only [t]
      rw [Multiset.toFinset_val,(squarefree_iff_nodup_normalizedFactors (nonZeroDivisors.coe_ne_zero _)).mp (hT k) |>.dedup]
      exact associated_iff_eq.mp (prod_normalizedFactors (nonZeroDivisors.coe_ne_zero _))
    apply Subtype.ext
    rw [← hp i,← hp j,h]
  have hcls (i) : (ClassGroup.mk0 (A i))^2 * ClassGroup.mk0 (T i) = 1 := by
    rw [← map_pow,← map_mul,ClassGroup.mk0_eq_one_iff]
    exact ⟨x i,hparts i⟩
  have hh := count_by_square_fibers t (fun i => ClassGroup.mk0 (A i)) (fun i j h => by
    apply mul_right_cancel (b := ClassGroup.mk0 (T j)); rw [← hdet i j h,hcls i,hdet i j h,hcls j]) (fun i j h ha => by
    have he : (I i : Ideal (𝓞 K))^2 = (I j : Ideal (𝓞 K))^2 := by rw [← hsquare i,← hsquare j,hdet i j h]
    have hI : I i = I j := by
      apply Subtype.ext
      apply le_antisymm <;> apply Ideal.le_of_dvd <;> apply (pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp <;> rw [he]
    apply hinj
    simp [Function.comp_apply,hfac,map_mul,← ClassGroup.extendedHom_mk0,ha,hI])
  rw [Nat.card_eq_fintype_card (α := S.powerset),Fintype.card_coe,Finset.card_powerset] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Finset.card_image_le.trans (discriminantPrimeIdealCover_card_le K))))

end
end CCDN
