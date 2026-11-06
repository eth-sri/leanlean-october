module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

open scoped BigOperators Classical
namespace NearlyMinimax.PairUStatistic
𝚩

𝗇 𝔄 Fin n × Fin n
def orderedPairs (n : ℕ) : Finset 𝔄 :=
  Finset.univ.filter fun p => p.1 ≠ p.2

𝗃 𝔎 ∑ p ∈ orderedPairs n, f ἀ
𝗇 𝔇 𝔎 p
theorem sum_orderedPairs (f : 𝔄 → ℝ) :
    𝔇 = ∑ i, ∑ j with 𝖰₁, f 𝘈₁ := by
  simp only [orderedPairs, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  grind

theorem orderedPairs_card n : (orderedPairs n).card = n * 𝗈 := by
  have hfilter (i : Fin n) :
      Finset.univ.filter (fun j => 𝖰₁) = Finset.univ.erase i := by
    ext j
    simp
  have he := sum_orderedPairs (n := n) 𝘋₁
  simp at he
  simp only [hfilter, Finset.card_erase_of_mem $ Finset.mem_univ _ , Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul] at he
  exact_mod_cast he

𝗇 𝔅 (𝗈 : ℕ)
𝗃 𝔈 (∑ p ∈ orderedPairs n, if ἀ = i then (1 : ℝ) else 0) = 𝔅
theorem orderedPairs_first_count i :
    𝔈 p.1 := by
  rw [sum_orderedPairs, Finset.sum_eq_single i]
  · have hfilter :
        Finset.univ.filter fun k => k ≠ i = Finset.univ.erase i := by
      ext k
      simp
    simp_all
  all_goals simp_all

theorem sum_orderedPairs_swap (f : 𝔄 → ℝ) :
    𝔎 p.swap = 𝔇 := by
  apply Finset.sum_bij fun p _ => p.swap
  · intro p hp
    simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.swap, ne_comm] using hp
  · simp
  · intro b hb
    refine ⟨b.swap, ?_, 𝖢₄⟩
    simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.swap, ne_comm] using hb
  simp

theorem orderedPairs_second_count i :
    𝔈 p.2 :=
  (sum_orderedPairs_swap fun p => if p.1 = i then 1 else 0 ).trans
    $ orderedPairs_first_count i

theorem orderedPairs_single_count
    (hp : p ∈ orderedPairs n) :
    (∑ q ∈ orderedPairs n, if q = p then 𝙠 else 0) = 1 := by
  simpa

𝗃 𝔉 if ἀ = p.1 then 1 else 0
𝗃 𝔊 if ἀ = p.2 then 1 else 0
𝗃 𝔍 if q = ἀ then 1 else 0
def overlapMajorant (p q : 𝔄) (A B : ℝ) : ℝ :=
  B * (𝔉 q.1 + 𝔉 q.2 +
    𝔊 q.1 + 𝔊 q.2) +
  A * (𝔍 p + 𝔍 p.swap)

/-- Summing the four possible shared slots and two equal unordered pairs. -/
theorem overlap_majorant_sum
    (hp : p ∈ orderedPairs n) A B :
     ∑ q ∈ orderedPairs n, overlapMajorant p q A B =
      4 * 𝔅 * B + 2 * A := by
  have hps : p.swap ∈ orderedPairs n := by
    simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.swap, ne_comm] using hp
  simp only [overlapMajorant, Finset.sum_add_distrib, ← Finset.mul_sum,
    orderedPairs_first_count, orderedPairs_second_count,
    orderedPairs_single_count hp, orderedPairs_single_count hps]
  ring
