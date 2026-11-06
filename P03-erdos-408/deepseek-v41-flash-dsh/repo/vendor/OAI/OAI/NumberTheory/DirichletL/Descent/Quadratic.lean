module

public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.Descent.IdealMasks
public import OAI.NumberTheory.DirichletL.Descent.SieveComposition

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment

open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_squarefree_quadratic_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows cols : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ J ∈ cols, Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X) →
    ∀ a : Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2) ≤
        C * (K * X) ^ ε * (K + X) * ∑ J ∈ cols, ‖a J‖ ^ 2 := by
  obtain ⟨C, hC, hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨4 * C, by positivity, ?_⟩
  intro K X hK hX rows cols hrows hcols a
  have hf := squarefree_all_column_energy (fun J : cols => J.val) Subtype.val_injective X K
    (fun J => hcols J.val J.property) (fun J => a J.val)
  have hi (k : idealRange K) :
      (∑ J : cols, quadraticRow k.val (primaryGenerator J.val) * a J.val) =
        ∑ J ∈ cols, quadraticRow k.val (primaryGenerator J) * a J :=
    Finset.sum_coe_sort cols (fun J => quadraticRow k.val (primaryGenerator J) * a J)
  simp_rw [hi] at hf
  rw [Finset.sum_coe_sort (idealRange K)
    (fun k => ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2),
    Finset.sum_coe_sort cols (fun J => ‖a J‖ ^ 2)] at hf
  have hr : rows ⊆ idealRange K := fun k hk => mem_idealRange.mpr (hrows k hk)
  have he : (∑ k ∈ rows, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2) ≤
      ∑ k ∈ idealRange K, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hr (by intro k _ _; exact sq_nonneg _)
  apply (he.trans hf).trans
  calc
    _ ≤ 4 * (C * (X * K) ^ ε * (X + K)) * ∑ J ∈ cols, ‖a J‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (hsharp X K hX hK) (by norm_num)
    _ = _ := by rw [mul_comm X K, add_comm X K]; ring

theorem quadratic_squarefree_product_column_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ a : Ideal Eis × Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Cq, hCq, hquad⟩ := finite_squarefree_quadratic_energy (ε / 2) hhalf
  obtain ⟨Cd, hCd, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) hhalf
  refine ⟨Cq * Cd, mul_pos hCq hCd, ?_⟩
  intro K X hK hX rows pairs hrows hpairs a
  let target := pairs.image (fun p => p.1 * p.2)
  have ht (J : Ideal Eis) (hJ : J ∈ target) :
      Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ
    exact hpairs p hp
  have hfiber (J : Ideal Eis) (hJ : J ∈ target) :
      ((pairs.filter (fun p => p.1 * p.2 = J)).card : ℝ) ≤ Cd * X ^ (ε / 2) := by
    apply (Nat.cast_le.mpr (product_fiber_card pairs J (ht J hJ).1.ne_zero)).trans
    exact (hdiv J (ht J hJ).1.ne_zero).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (ht J hJ).2 hhalf.le) hCd.le)
  have he := column_fiber_sieve rows pairs target (fun p => p.1 * p.2)
    (fun k J => quadraticRow k (primaryGenerator J)) a
    (Cq * (K * X) ^ (ε / 2) * (K + X)) (Cd * X ^ (ε / 2)) (by positivity)
    (fun p hp => Finset.mem_image_of_mem _ hp) hfiber
    (hquad K X hK hX rows target hrows ht)
  apply he.trans
  have hKX : 0 < K * X := mul_pos (by linarith) (by linarith)
  have hpow : (K * X) ^ (ε / 2) * X ^ (ε / 2) ≤ (K * X) ^ ε := by
    calc
      _ ≤ (K * X) ^ (ε / 2) * (K * X) ^ (ε / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hKX.le _)
        exact Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith) hK) hhalf.le
      _ = _ := by rw [← Real.rpow_add hKX]; congr 1 ; ring
  calc
    _ = (Cq * Cd) * ((K * X) ^ (ε / 2) * X ^ (ε / 2)) * (K + X) *
        ∑ p ∈ pairs, ‖a p‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem quadratic_fixed_factor_energy
    (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
    (hrows : ∀ k ∈ rows, Admissible k) (B : Ideal Eis)
    (a : Ideal Eis × Ideal Eis → ℂ) :
    (∑ k ∈ rows, ‖∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
    ∑ k ∈ rows, ‖∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  have he : (∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p) =
      quadraticRow k (primaryGenerator B) * ∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p := by
    simp only [primaryGenerator_mul,
      canonical_quadraticRow_argument_mul k (hrows k hk), Finset.mul_sum, mul_assoc]
  rw [he]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one k _)

theorem quadratic_squarefree_product_energy_fixed_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B : Ideal Eis) (a : Ideal Eis × Ideal Eis → ℂ),
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := quadratic_squarefree_product_column_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B a
  exact (quadratic_fixed_factor_energy rows pairs (fun k hk => (hrows k hk).1) B a).trans
    (hb K X hK hX rows pairs hrows hpairs a)

end
end SevenEighths.InverseMoment

end OAI
