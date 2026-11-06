module

public import OAI.NumberTheory.DirichletL.Foundation

@[expose] public section

namespace OAI

namespace SevenEighths.InverseInitialFibers

open ActualEisensteinCubic
open CompletedGauss (primaryGenerator primaryGenerator_mul)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical
noncomputable section

@[ext] structure InitialTuple (J : ℕ) where
  common : Ideal O
  divisor : Ideal O
  residual : Ideal O
  frequency : O
  assigned : Fin J → SmoothMobiusCorrection.PrimeIdeal

structure Valid {J : ℕ} (x : InitialTuple J) (t f : Ideal O) (k : O) : Prop where
  common_eq : t * x.divisor = x.common
  label_eq : x.divisor * x.residual = f
  divisor_good : primaryGenerator x.divisor ≠ 0
  row_eq : primaryGenerator x.divisor * x.frequency = k
  assigned_dvd : ∀ i, (x.assigned i).val ∣ t * f

lemma divisor_dvd {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) : x.divisor ∣ f := ⟨x.residual, hx.label_eq.symm⟩

lemma divisor_ne_zero {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) (hf : f ≠ 0) : x.divisor ≠ 0 := by
  intro hz
  have he := hx.label_eq
  rw [hz, zero_mul] at he
  exact hf he.symm

theorem valid_key_injective {J : ℕ} (t f : Ideal O) (k : O) (hf : f ≠ 0)
    {x y : InitialTuple J} (hx : Valid x t f k) (hy : Valid y t f k)
    (hd : x.divisor = y.divisor) (ha : x.assigned = y.assigned) : x = y := by
  have hd0 := divisor_ne_zero hx hf
  have hc : x.common = y.common := by rw [← hx.common_eq, ← hy.common_eq, hd]
  have hs : x.residual = y.residual := by
    apply mul_left_cancel₀ hd0
    exact hx.label_eq.trans (by simpa only [hd] using hy.label_eq.symm)
  have hg : primaryGenerator x.divisor ≠ 0 := hx.divisor_good
  have hr : x.frequency = y.frequency := by
    apply mul_left_cancel₀ hg
    exact hx.row_eq.trans (by simpa only [hd] using hy.row_eq.symm)
  exact InitialTuple.ext hc hd hs hr ha

lemma divisors_mul_image (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealDivisors (I*J) =
      ((idealDivisors I) ×ˢ (idealDivisors J)).image (fun p => p.1*p.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hI hJ), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨A, B, hA, hB, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hD
    exact ⟨(A,B), Finset.mem_product.mpr
      ⟨(mem_idealDivisors hI).mpr hA, (mem_idealDivisors hJ).mpr hB⟩, hab.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hI).mp (Finset.mem_product.mp hp).1)
      ((mem_idealDivisors hJ).mp (Finset.mem_product.mp hp).2)

lemma divisor_card_mul_le (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (idealDivisors (I*J)).card ≤ (idealDivisors I).card * (idealDivisors J).card := by
  rw [divisors_mul_image I J hI hJ, ← Finset.card_product]
  exact Finset.card_image_le

theorem valid_tuple_card_le {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card * (idealDivisors (t*f)).card^J := by
  let D := idealDivisors f
  let E := idealDivisors (t*f)
  let encode (x : T) : D × (Fin J → E) :=
    (⟨x.val.divisor, (mem_idealDivisors hf).mpr (divisor_dvd (hT x.val x.property))⟩,
      fun i => ⟨(x.val.assigned i).val,
        (mem_idealDivisors (mul_ne_zero ht hf)).mpr ((hT x.val x.property).assigned_dvd i)⟩)
  have hi : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply valid_key_injective t f k hf (hT x.val x.property) (hT y.val y.property)
    · exact congrArg Subtype.val (congrArg Prod.fst hxy)
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : E => z.val) (congrFun (congrArg Prod.snd hxy) i)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, D, E] using Fintype.card_le_of_injective encode hi

theorem valid_tuple_card_le_separated {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card^(J+1) * (idealDivisors t).card^J := by
  apply (valid_tuple_card_le T t f k ht hf hT).trans
  calc
    _ ≤ (idealDivisors f).card *
        ((idealDivisors t).card * (idealDivisors f).card)^J :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (divisor_card_mul_le t f ht hf) J)
    _ = _ := by rw [mul_pow, pow_succ]; ring

lemma divisor_card_pos (I : Ideal O) (hI : I ≠ 0) : 1 ≤ (idealDivisors I).card := by
  apply Finset.one_le_card.mpr
  exact ⟨1, (mem_idealDivisors hI).mpr (one_dvd I)⟩

end
end SevenEighths.InverseInitialFibers

end OAI
