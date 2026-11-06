module

public import NearlyMinimax.HighPriorModel


@[expose] public section

/-! Stars-and-bars bound for the manuscript's distinct mixed partials. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

def boundedMultiIndexMultiset d ℓ (γ : Fin d → Fin (ℓ + 1))  :=
  (∑ r, Multiset.replicate (γ r).val r.castSucc) +
    Multiset.replicate (ℓ - ∑ r, (γ r).val) (Fin.last d)

theorem boundedMultiIndexMultiset_card d ℓ γ
    (hγ : (∑ r, (γ r).val) ≤ ℓ) :
    (boundedMultiIndexMultiset d ℓ γ).card = ℓ := by
  simp only [boundedMultiIndexMultiset, Multiset.card_add, Multiset.card_sum,
    Multiset.card_replicate]
  omega

theorem boundedMultiIndexMultiset_count d ℓ γ r :
    (boundedMultiIndexMultiset d ℓ γ).count r.castSucc = (γ r).val := by
  simp only [boundedMultiIndexMultiset, Multiset.count_add, Multiset.count_sum',
    Multiset.count_replicate]
  have hlast : Fin.last d ≠ r.castSucc := by
    grind
  simp_all

theorem bounded_multiIndex_count_le d ℓ :
    (Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ r, (γ r).val) ≤ ℓ)).card ≤
      (d + ℓ).choose d := by
  let A := Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ r, (γ r).val) ≤ ℓ)
  let encode : A → Sym (Fin (d + 1)) ℓ := fun γ =>
    ⟨boundedMultiIndexMultiset d ℓ γ, boundedMultiIndexMultiset_card d ℓ γ
      (Finset.mem_filter.mp γ.property).2⟩
  have hinj : Function.Injective encode := by
    intro γ δ he
    apply Subtype.ext
    funext r
    apply Fin.ext
    have hm := congrArg (fun s : Sym (Fin (d + 1)) ℓ => s.val.count r.castSucc) he
    change (boundedMultiIndexMultiset d ℓ γ).count r.castSucc =
      (boundedMultiIndexMultiset d ℓ δ).count r.castSucc at hm
    simpa only [boundedMultiIndexMultiset_count] using hm
  have hc := Fintype.card_le_of_injective encode hinj
  rw [Fintype.card_coe, Sym.card_sym_eq_choose, Fintype.card_fin] at hc
  have hsum : d + 1 + ℓ - 1 = d + ℓ := by omega
  rw [hsum, ← Nat.choose_symm (by omega : ℓ ≤ d + ℓ)] at hc
  measurability

theorem holderNorm_of_global_mixed_bounds_binomial {d } U
    F ℓ α B L (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hsup : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) ≤ ℓ →
      ∀ x, |multiPartial F (fun i => (γ i).val) x| ≤ B)
    (hmod : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) = ℓ → ∀ x y,
      |multiPartial F (fun i => (γ i).val) x - multiPartial F (fun i => (γ i).val) y| ≤
        L * euclideanNorm (x - y) ^ α) :
    holderNorm U F ℓ α ≤ ENNReal.ofReal (((d + ℓ).choose d) * B + L) := by
  have hs (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) ≤ ℓ) :
      derivativeSup U (multiPartial F (fun i => (γ i).val)) ≤ ENNReal.ofReal B := by
    apply iSup_le
    simp_all
  have hh (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) = ℓ) :
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α ≤ ENNReal.ofReal L := by
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : (x : Covariate d) = y
    · simp [hxy]
    · simp only [ite_eq_right_iff.mpr (fun h => False.elim (hxy h))]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (Real.rpow_pos_of_pos
        (euclideanNorm_pos_of_ne_zero (x.val - y.val) (sub_ne_zero.mpr hxy)) α)).mpr
      exact hmod γ hγ x y
  let A := Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ i, (γ i).val) ≤ ℓ)
  have hsum : (∑ γ : Fin d → Fin (ℓ + 1),
      if (∑ i, (γ i).val) ≤ ℓ then
        derivativeSup U (multiPartial F (fun i => (γ i).val)) else 0) ≤
      ENNReal.ofReal (((d + ℓ).choose d : ℝ) * B) := by
    calc
      _ = ∑ γ ∈ A, derivativeSup U (multiPartial F (fun i => (γ i).val)) := by
        
        rw [Finset.sum_filter]
      _ ≤ ∑ _γ ∈ A, ENNReal.ofReal B := by
        apply Finset.sum_le_sum
        intro γ hγ
        exact hs γ (Finset.mem_filter.mp hγ).2
      _ = ENNReal.ofReal ((A.card : ℝ) * B) := by
        simp_all
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (by exact_mod_cast bounded_multiIndex_count_le d ℓ) hB)
  have hsem : (⨆ γ : Fin d → Fin (ℓ + 1), if (∑ i, (γ i).val) = ℓ then
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α else 0) ≤ ENNReal.ofReal L := by
    apply iSup_le
    bound
  
  rw [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hB) hL]
  exact add_le_add hsum hsem

end NearlyMinimax
