module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.PrimitiveDivisorGrowth

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                      
                                                                 

noncomputable section
namespace TaoTrudgianYang2025

theorem harmonic_le_rpow_loss (ε : ℝ) (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ N) :
    (harmonic N:ℝ) ≤ (1+1/ε)*(N:ℝ)^ε := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hone : 1 ≤ (N:ℝ)^ε := Real.one_le_rpow hN1 hε.le
  calc
    _ ≤ 1+Real.log N := harmonic_le_one_add_log N
    _ ≤ (N:ℝ)^ε+(N:ℝ)^ε/ε :=
      add_le_add hone (Real.log_le_rpow_div (Nat.cast_nonneg N) hε)
    _ = _ := by ring

theorem sum_positive_displacement_weight_le_harmonic
    {η A : ℝ} {N : ℕ} (hη : 0 ≤ η) (hA : 0 ≤ A) :
    (∑ n ∈ Finset.Icc 1 N, (n:ℝ)^η*(1+A/n)) ≤
      (N:ℝ)^η*((N:ℝ)+A*(harmonic N:ℝ)) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (N:ℝ)^η*(1+A/n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg n)
          (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hη) (by positivity)
    _ = (N:ℝ)^η*((N:ℝ)+A*(∑ n ∈ Finset.Icc 1 N, (n:ℝ)⁻¹)) := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [div_eq_mul_inv,Finset.sum_add_distrib,Finset.sum_const,
        Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one,← Finset.mul_sum]
    _ = _ := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

theorem sum_positive_displacement_weight_le
    {ε A : ℝ} {N : ℕ} (hε : 0 < ε) (hA : 0 ≤ A) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(ε/2)*(1+A/n)) ≤
      (1+2/ε)*(N:ℝ)^ε*((N:ℝ)+A) := by
  have hη : 0 < ε/2 := by linarith
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith
  have hpow : 1 ≤ (N:ℝ)^(ε/2) := Real.one_le_rpow hN1 hη.le
  have hconst : 1 ≤ 1+2/ε := by linarith [div_pos (by norm_num : (0:ℝ) < 2) hε]
  have hh : (harmonic N:ℝ) ≤ (1+2/ε)*(N:ℝ)^(ε/2) := by
    convert harmonic_le_rpow_loss (ε/2) hη hN using 1
    field_simp
  have hmain : (N:ℝ) ≤ (1+2/ε)*(N:ℝ)^(ε/2)*(N:ℝ) := by
    have hone : 1 ≤ (1+2/ε)*(N:ℝ)^(ε/2) :=
      one_le_mul_of_one_le_of_one_le hconst hpow
    nlinarith only [mul_le_mul_of_nonneg_right hone hNp.le]
  have hsq : (N:ℝ)^(ε/2)*(N:ℝ)^(ε/2) = (N:ℝ)^ε := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  calc
    _ ≤ (N:ℝ)^(ε/2)*((N:ℝ)+A*(harmonic N:ℝ)) :=
      sum_positive_displacement_weight_le_harmonic hη.le hA
    _ ≤ (N:ℝ)^(ε/2)*((1+2/ε)*(N:ℝ)^(ε/2)*(N:ℝ)+
        A*((1+2/ε)*(N:ℝ)^(ε/2))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hmain (mul_le_mul_of_nonneg_left hh hA)) (by positivity)
    _ = (1+2/ε)*((N:ℝ)^(ε/2)*(N:ℝ)^(ε/2))*((N:ℝ)+A) := by ring
    _ = _ := by rw [hsq]

/-- Separate the zero and positive shifts in a finite symmetric relation.
The negative part has the same cardinality as the positive part. -/
theorem card_symmetric_displacement_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (R : Finset (ι×ι)) (y : ι → ℝ) (B N : ℕ) (w : ℕ → ℝ)
    (hRS : R ⊆ S ×ˢ S) (hsym : ∀ p∈R, p.swap∈R)
    (hshift : ∀ p∈R, ∃ k : ℤ, y p.2-y p.1=(k:ℝ) ∧ |(k:ℝ)|≤N)
    (hmulLevel : ∀ a : ℝ, (S.filter (fun i => y i=a)).card≤B)
    (hpos : ∀ n∈Finset.Icc 1 N,
      ((R.filter (fun p => y p.2-y p.1=(n:ℝ))).card:ℝ)≤w n) :
    (R.card:ℝ) ≤ (B:ℝ)*S.card+2*(∑ n∈Finset.Icc 1 N,w n) := by
  classical
  let Z := R.filter (fun p => y p.1=y p.2)
  let Rp := R.filter (fun p => y p.1<y p.2)
  have hRmem p (hp : p∈R) : p.1∈S ∧ p.2∈S := Finset.mem_product.mp (hRS hp)
  have hpmem p (hp : p∈Rp) : p∈R ∧ y p.1<y p.2 := Finset.mem_filter.mp hp
  have hRsplit : R ⊆ Z ∪ (Rp ∪ Rp.image Prod.swap) := by
    intro p hp
    rcases lt_trichotomy (y p.1) (y p.2) with hh | hh | hh
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hh⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hh⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨p.swap,Finset.mem_filter.mpr ⟨hsym p hp,hh⟩,Prod.swap_swap p⟩
  have hsplit : R.card ≤ Z.card+2*Rp.card := by
    have hh := (Finset.card_le_card hRsplit).trans (Finset.card_union_le _ _)
    have hh' := Finset.card_union_le Rp (Rp.image Prod.swap)
    have he : (Rp.image Prod.swap).card=Rp.card := Finset.card_image_of_injective _ Prod.swap_injective
    omega
  have hZfiber i : (Z.filter (fun p => p.1=i)).card ≤ B := by
    have hsub : Z.filter (fun p => p.1=i) ⊆ {i} ×ˢ (S.filter (fun j => y j=y i)) := by
      intro p hp
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp,hh⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr he,
        Finset.mem_filter.mpr ⟨(hRmem p hp).2,by rw [←he]; exact hh.symm⟩⟩
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ = (S.filter (fun j => y j=y i)).card := by simp only [Finset.card_product,Finset.card_singleton,one_mul]
      _ ≤ _ := hmulLevel _
  have hZ : (Z.card:ℝ) ≤ (B:ℝ)*S.card := by
    have he : (Z.card:ℝ)=∑ i∈S,((Z.filter (fun p => p.1=i)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise
        (fun (p : ι × ι) hp => (hRmem p (Finset.mem_filter.mp hp).1).1)
    rw [he]
    calc
      _ ≤ ∑ _i∈S,(B:ℝ) := Finset.sum_le_sum (fun i _ => by exact_mod_cast hZfiber i)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hex (p : ι × ι) : ∃ d : ℕ, p∈Rp →
      0 < d ∧ y p.2-y p.1=(d:ℝ) ∧ d ≤ N := by
    by_cases hp : p∈Rp
    · obtain ⟨d,he,hd⟩ := hshift p (hpmem p hp).1
      have hdr : 0 < (d:ℝ) := by linarith only [he,(hpmem p hp).2]
      have hdi : 0 < d := by exact_mod_cast hdr
      have hdcast : (d.toNat:ℝ)=(d:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hdi.le
      refine ⟨d.toNat,fun _ => ⟨by omega,by rw [hdcast]; exact he,?_⟩⟩
      have hh : (d.toNat:ℝ) ≤ N := by rw [hdcast]; exact (le_abs_self _).trans hd
      exact_mod_cast hh
    · exact ⟨0,fun hh => False.elim (hp hh)⟩
  choose shift hshiftNat using hex
  let J := Finset.Icc 1 N
  have hindex p (hp : p∈Rp) : shift p∈J :=
    Finset.mem_Icc.mpr ⟨(hshiftNat p hp).1,(hshiftNat p hp).2.2⟩
  have hRp : (Rp.card:ℝ) ≤ ∑ n∈J,w n := by
    have hc : (Rp.card:ℝ)=∑ n∈J,((Rp.filter (fun p => shift p=n)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hindex
    rw [hc]
    refine Finset.sum_le_sum fun n hn => ?_
    refine (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (hpos n hn)
    intro p hp
    obtain ⟨hpp, rfl⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(hpmem p hpp).1,(hshiftNat p hpp).2.1⟩
  have hh : (R.card:ℝ)≤(Z.card:ℝ)+2*(Rp.card:ℝ) := by exact_mod_cast hsplit
  linarith only [hh,hZ,hRp]

/-- The symmetric displacement estimate when the positive fibers have harmonic weight. -/
theorem card_symmetric_displacement_harmonic {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (R : Finset (ι×ι)) (y : ι → ℝ) (B N : ℕ) (K D : ℝ)
    (hRS : R ⊆ S ×ˢ S) (hsym : ∀ p∈R, p.swap∈R)
    (hshift : ∀ p∈R, ∃ k : ℤ, y p.2-y p.1=(k:ℝ) ∧ |(k:ℝ)|≤N)
    (hmul : ∀ a : ℝ, (S.filter (fun i => y i=a)).card≤B)
    (hpos : ∀ n∈Finset.Icc 1 N,
      ((R.filter (fun p => y p.2-y p.1=(n:ℝ))).card:ℝ)≤K*(3+D/n)) :
    (R.card:ℝ) ≤ (B:ℝ)*S.card+2*K*(3*(N:ℝ)+D*(harmonic N:ℝ)) := by
  refine (card_symmetric_displacement_le S R y B N _ hRS hsym hshift hmul hpos).trans_eq ?_
  rw [←Finset.mul_sum, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel,
    div_eq_mul_inv, ←Finset.mul_sum, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  ring

end TaoTrudgianYang2025
