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

variable {d ℓ : ℕ}

def boundedMultiIndexMultiset (γ : Fin d → Fin (ℓ + 1)) : Multiset (Fin (d + 1)) :=
  (∑ r, Multiset.replicate (γ r).val r.castSucc) +
    Multiset.replicate (ℓ - ∑ r, (γ r).val) (Fin.last d)

theorem boundedMultiIndexMultiset_card {γ : Fin d → Fin (ℓ + 1)}
    (hγ : (∑ r, (γ r).val) ≤ ℓ) :
    (boundedMultiIndexMultiset γ).card = ℓ := by
  simp [boundedMultiIndexMultiset]
  omega

theorem boundedMultiIndexMultiset_count (d ℓ : ℕ) (γ : Fin d → Fin (ℓ + 1)) (r : Fin d) :
    (boundedMultiIndexMultiset γ).count r.castSucc = (γ r).val := by
  simp only [boundedMultiIndexMultiset, Multiset.count_add, Multiset.count_sum',
    Multiset.count_replicate]
  have hlast : Fin.last d ≠ r.castSucc := by
    grind
  simp only [hlast, ite_false, add_zero, Fin.castSucc_inj]
  simp

theorem bounded_multiIndex_count_le (d ℓ : ℕ) :
    (Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ r, (γ r).val) ≤ ℓ)).card ≤
      (d + ℓ).choose d := by
  let A := Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ r, (γ r).val) ≤ ℓ)
  let encode : A → Sym (Fin (d + 1)) ℓ := fun γ =>
    ⟨boundedMultiIndexMultiset (ℓ := ℓ) γ, boundedMultiIndexMultiset_card (d := d) (ℓ := ℓ)
      (Finset.mem_filter.mp γ.property).2⟩
  have hinj : Function.Injective encode := by
    intro γ δ he
    apply Subtype.ext
    funext r
    apply Fin.ext
    have hm := congrArg (fun s => s.val.count r.castSucc) he
    change (boundedMultiIndexMultiset (ℓ := ℓ) γ).count r.castSucc =
      (boundedMultiIndexMultiset (ℓ := ℓ) δ).count r.castSucc at hm
    simpa only [boundedMultiIndexMultiset_count] using hm
  have hc := Fintype.card_le_of_injective encode hinj
  rw [Fintype.card_coe, Sym.card_sym_eq_choose, Fintype.card_fin] at hc
  have hsum : d + 1 + ℓ - 1 = d + ℓ := by omega
  rw [hsum, ← Nat.choose_symm (by omega)] at hc
  simpa using hc

end NearlyMinimax
