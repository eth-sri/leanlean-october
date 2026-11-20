module

public import PottsDiscontinuity.TorusRC.CrossingContracts
public import PottsDiscontinuity.TorusRC.MeasureFacts
public import PottsDiscontinuity.TorusRC.BlockLogRate
public import Mathlib.Combinatorics.Pigeonhole

/-! # Extracting an endpoint pair from the rectangle-crossing estimate -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

section

variable (hNp : 0 < N) (hMp : 0 < M) (n : ℕ)

/-- A rectangle crossing with the two horizontal endpoint coordinates fixed.
Impossible parity choices simply give an empty event. -/
def rectanglePairConnection
    (i j : Fin (3 * n + 1)) : Set (RCConfig N M) :=
  {A | ∃ u v : RotatedVertex,
    u.val = ((i.val : ℤ), 0) ∧ v.val = ((j.val : ℤ), (n : ℤ)) ∧
      ∃ w : (liftedStripGraph hNp hMp A 0 (3 * (n : ℤ))).Walk u v,
        ∀ z ∈ w.support, 0 ≤ z.val.2 ∧ z.val.2 ≤ (n : ℤ)}

theorem rectangleCrossing_covered_by_pairs (hn : 0 < n) (A : RCConfig N M)
    (hA : torusRCVerticalRectangleCrossing hNp hMp n A) :
    ∃ ij : Fin (3 * n + 1) × Fin (3 * n + 1),
      A ∈ rectanglePairConnection hNp hMp n ij.1 ij.2 := by
  obtain ⟨u,v,hu,hv,w,hw⟩ := hA
  have huv : u ≠ v := by
    intro h
    subst v
    omega
  have hend {a b : RotatedVertex}
      (p : (liftedStripGraph hNp hMp A 0 (3 * (n : ℤ))).Walk a b) (hab : a ≠ b) :
      0 ≤ a.val.1 ∧ a.val.1 ≤ 3 * (n : ℤ) := by
    cases p with
    | nil => trivial
    | cons hadj _ => exact hadj.2.2.1
  have hux := hend w huv
  have hvx := hend w.reverse huv.symm
  let i : Fin (3 * n + 1) := ⟨u.val.1.toNat, by omega⟩
  let j : Fin (3 * n + 1) := ⟨v.val.1.toNat, by omega⟩
  refine ⟨(i,j),u,v,?_,?_,w,hw⟩
  · apply Prod.ext <;> dsimp [i] <;> omega
  · apply Prod.ext <;> dsimp [j] <;> omega

end

/-- Pigeonholing the endpoints of an actual crossing. -/
theorem rectanglePair_probability_ge (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ))
    (n : ℕ) (hn : 0 < n) (c : ℝ)
    (hc : c ≤ torusRCProbability hN hM q
      {A | torusRCVerticalRectangleCrossing hNp hMp n A}) :
    ∃ ij : Fin (3 * n + 1) × Fin (3 * n + 1),
      blockPenalty c n ≤ torusRCProbability hN hM q (rectanglePairConnection hNp hMp n ij.1 ij.2) := by
  classical
  let F (ij : Fin (3 * n + 1) × Fin (3 * n + 1)) := rectanglePairConnection hNp hMp n ij.1 ij.2
  have hsub : {A | torusRCVerticalRectangleCrossing hNp hMp n A} ⊆ ⋃ ij, F ij :=
    fun A hA => Set.mem_iUnion.2 (rectangleCrossing_covered_by_pairs hNp hMp n hn A hA)
  have hsum : c ≤ ∑ ij, torusRCProbability hN hM q (F ij) :=
    hc.trans ((torusRCProbability_mono hN hM q hsub).trans
      (MeasureTheory.measureReal_iUnion_fintype_le F))
  obtain ⟨ij, _, hij⟩ := Finset.exists_le_of_sum_le
    (f := fun _ => blockPenalty c n) Finset.univ_nonempty (g := fun ij => torusRCProbability hN hM q (F ij)) (by
      convert hsum using 1
      simp only [blockPenalty, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp)
  exact ⟨ij, hij⟩

end PottsDiscontinuity.TorusRC
