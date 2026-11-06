module

public import PottsDiscontinuity.LinearAlgebra.PerronFrobenius
public import PottsDiscontinuity.SixVertex.InfinityHalfSpectrum
public import PottsDiscontinuity.SixVertex.InfinityIrreducible

/-! # Perron eigenvalue of the restriction and the full limiting block -/

@[expose] public section

open Finset Matrix
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

/-- Embed the existing even-position state into a sufficiently long row. -/
def embeddedEvenState (hN : 2 * n ≤ N) : State N n :=
  ⟨(evenState n).1.map (Fin.castLEEmb hN), by rw [card_map, (evenState n).2]⟩

theorem mem_embeddedEvenState (hN : 2 * n ≤ N) (i : Fin N) :
    i ∈ (embeddedEvenState hN).1 ↔ i.val % 2 = 0 ∧ i.val < 2 * n := by
  refine ⟨fun hi => ?_, fun ⟨he, hi⟩ => mem_map.mpr ⟨⟨i.val, hi⟩, (mem_evenState _).mpr he, Fin.ext rfl⟩⟩
  obtain ⟨j, hj, he⟩ := mem_map.mp hi
  have hv := congrArg Fin.val he
  simp only [Fin.castLEEmb_apply, Fin.val_castLE] at hv
  exact ⟨hv ▸ (mem_evenState j).mp hj, hv ▸ j.isLt⟩

def independentPacked (hN : 2 * n ≤ N) : IndependentState N n :=
  ⟨embeddedEvenState hN, fun i hi hni => by
    obtain ⟨he, hi⟩ := (mem_embeddedEvenState hN i).mp hi
    have hne := ((mem_embeddedEvenState hN (nxt i)).mp hni).1
    rw [nxt_val_of_lt i (by omega)] at hne; omega⟩

/-- PF positivity, a positive eigenvector, and algebraic simplicity on the genuine support. -/
theorem infinityRestriction_perronFrobenius (hn : 0 < n) (hN : 2 * n ≤ N) :
    0 < pfRoot (infinityRestriction N n) ∧
    (∃ v : IndependentState N n → ℝ, (∀ x, 0 < v x) ∧
      infinityRestriction N n *ᵥ v = pfRoot (infinityRestriction N n) • v) ∧
    (infinityRestriction N n).charpoly.rootMultiplicity
      (pfRoot (infinityRestriction N n)) = 1 := by
  have : Nonempty (IndependentState N n) := ⟨independentPacked hN⟩
  obtain ⟨hp, _, _, hv, _, _, hm, _, _⟩ := perronFrobenius_irreducible
    (infinityRestriction_isHermitian (N := N) (n := n)) (infinityRestriction_isIrreducible hn)
  exact ⟨hp, hv, hm⟩

/-- Restriction of a coordinate vector to the independent states. -/
def restrictIndependent (v : State N n → ℝ) : IndependentState N n → ℝ := fun x => v x.1

/-- Extension by zero outside the independent states. -/
def extendIndependent (v : IndependentState N n → ℝ) : State N n → ℝ :=
  fun x => if h : NoConsecutiveUp x.1 then v ⟨x, h⟩ else 0

@[simp] theorem restrictIndependent_extend (v : IndependentState N n → ℝ) :
    restrictIndependent (extendIndependent v) = v := by
  funext x
  simp only [restrictIndependent, extendIndependent, dite_eq_left x.2]

/-- The zero columns outside the support make restriction commute with the operator. -/
theorem restrictIndependent_mulVec (hn : 0 < n) (v : State N n → ℝ) :
    restrictIndependent (infinityBlock N n *ᵥ v) =
      infinityRestriction N n *ᵥ restrictIndependent v := by
  funext x
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun y : State N n => NoConsecutiveUp y.1)
    (fun y => infinityBlock N n x.1 y * v y)
  rw [Finset.sum_eq_zero fun (y : {y : State N n // ¬ NoConsecutiveUp y.1}) _ => by
    rw [infinityBlock_symm, infinityBlock_eq_zero_of_not_noConsecutiveUp hn _ _ y.2, zero_mul],
    add_zero] at hs
  exact hs.symm

theorem infinityBlock_eigenvector_supported (hn : 0 < n) {μ : ℝ} (hμ : μ ≠ 0)
    {v : State N n → ℝ} (hv : infinityBlock N n *ᵥ v = μ • v)
    (x : State N n) (hx : ¬ NoConsecutiveUp x.1) : v x = 0 := by
  have hh := congrFun hv x
  rw [infinityBlock_mulVec_supported hn v x hx] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left hμ

/-- Extension lifts eigenvectors from the support to the full matrix. -/
theorem extendIndependent_eigenvector (hn : 0 < n) {μ : ℝ}
    {v : IndependentState N n → ℝ} (hv : infinityRestriction N n *ᵥ v = μ • v) :
    infinityBlock N n *ᵥ extendIndependent v = μ • extendIndependent v := by
  funext x
  by_cases hx : NoConsecutiveUp x.1
  · have hh := congrFun (restrictIndependent_mulVec hn (extendIndependent v)) ⟨x, hx⟩
    rw [restrictIndependent_extend, hv] at hh
    simpa only [restrictIndependent, extendIndependent, dite_eq_left hx, Pi.smul_apply] using hh
  · rw [infinityBlock_mulVec_supported hn _ x hx]
    simp only [Pi.smul_apply, extendIndependent, dite_eq_right hx, smul_eq_mul, mul_zero]

private theorem mem_spectrum_of_eigenvector {S : Type*} [Fintype S] [DecidableEq S]
    {A : Matrix S S ℝ} {μ : ℝ} {v : S → ℝ} (hv0 : v ≠ 0) (hv : A *ᵥ v = μ • v) :
    μ ∈ spectrum ℝ A := by
  simpa only [Matrix.spectrum_toLin'] using
    (Module.End.hasEigenvalue_of_hasEigenvector
      (⟨by rwa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply], hv0⟩ :
        Module.End.HasEigenvector (Matrix.toLin' A) μ v)).mem_spectrum

/-- The support restriction and the full block have the same largest eigenvalue. -/
theorem pfRoot_infinityBlock_eq_restriction (hn : 0 < n) (hN : 2 * n ≤ N) :
    pfRoot (infinityBlock N n) = pfRoot (infinityRestriction N n) := by
  have : Nonempty (IndependentState N n) := ⟨independentPacked hN⟩
  have : Nonempty (State N n) := ⟨(independentPacked hN).1⟩
  obtain ⟨hp, ⟨v, hv, he⟩, _⟩ := infinityRestriction_perronFrobenius hn hN
  have hv0 : extendIndependent v ≠ 0 := fun hz => by
    have hzero := congrFun (congrArg restrictIndependent hz) (independentPacked hN)
    rw [restrictIndependent_extend] at hzero
    exact (hv _).ne' hzero
  have hle : pfRoot (infinityRestriction N n) ≤ pfRoot (infinityBlock N n) :=
    (isGreatest_pfRoot infinityBlock_isHermitian).2
      (mem_spectrum_of_eigenvector hv0 (extendIndependent_eigenvector hn he))
  have hfullpos : 0 < pfRoot (infinityBlock N n) := hp.trans_le hle
  have hA := infinityBlock_isHermitian (N := N) (n := n)
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_pfRoot hA
  let w := eigvec hA i
  have hw : infinityBlock N n *ᵥ w = pfRoot (infinityBlock N n) • w := by
    rw [show w = eigvec hA i from rfl, mulVec_eigvec hA, hi]
  have hw0 : restrictIndependent w ≠ 0 := fun hz => by
    have hzero : w = 0 := funext fun x => by
      by_cases hx : NoConsecutiveUp x.1
      · exact congrFun hz ⟨x, hx⟩
      · exact infinityBlock_eigenvector_supported hn hfullpos.ne' hw x hx
    have hh := eigvec_dot hA i i
    change w ⬝ᵥ w = _ at hh
    simp [hzero] at hh
  exact le_antisymm ((isGreatest_pfRoot infinityRestriction_isHermitian).2
    (mem_spectrum_of_eigenvector hw0 (by rw [← restrictIndependent_mulVec hn, hw]; rfl))) hle

/-- The full block has a positive largest eigenvalue in the source's range. -/
theorem pfRoot_infinityBlock_pos (hn : 0 < n) (hN : 2 * n ≤ N) :
    0 < pfRoot (infinityBlock N n) := by
  rw [pfRoot_infinityBlock_eq_restriction hn hN]
  exact (infinityRestriction_perronFrobenius hn hN).1

/-- Every eigenvector at the full block's largest eigenvalue lies on one fixed line. -/
theorem infinityBlock_pfRoot_eigenvector_line (hn : 0 < n) (hN : 2 * n ≤ N) :
    ∃ u : State N n → ℝ, u ≠ 0 ∧
      infinityBlock N n *ᵥ u = pfRoot (infinityBlock N n) • u ∧
      ∀ w : State N n → ℝ,
        infinityBlock N n *ᵥ w = pfRoot (infinityBlock N n) • w →
        ∃ c : ℝ, w = c • u := by
  have : Nonempty (IndependentState N n) := ⟨independentPacked hN⟩
  obtain ⟨_, ⟨v, hv, he⟩, _⟩ := infinityRestriction_perronFrobenius hn hN
  have hroot := pfRoot_infinityBlock_eq_restriction hn hN
  have hpos := pfRoot_infinityBlock_pos hn hN
  refine ⟨extendIndependent v, fun hz => ?_, by rw [hroot]; exact extendIndependent_eigenvector hn he, fun w hw => ?_⟩
  · have hh := congrFun (congrArg restrictIndependent hz) (independentPacked hN)
    rw [restrictIndependent_extend] at hh
    exact (hv _).ne' hh
  · obtain ⟨c, hc⟩ := eigenspace_pfRoot_eq infinityRestriction_nonneg
      (infinityRestriction_exists_pow_pos hn) infinityRestriction_isHermitian hv he
      (by rw [← restrictIndependent_mulVec hn, hw, hroot]; rfl)
    refine ⟨c, funext fun x => ?_⟩
    by_cases hx : NoConsecutiveUp x.1
    · simpa only [restrictIndependent, Pi.smul_apply, extendIndependent, dite_eq_left hx] using
        congrFun hc ⟨x, hx⟩
    · rw [infinityBlock_eigenvector_supported hn hpos.ne' hw x hx]
      simp only [Pi.smul_apply, extendIndependent, dite_eq_right hx, smul_eq_mul, mul_zero]

/-- The largest eigenvalue of the full limiting block is algebraically simple. -/
theorem rootMultiplicity_infinityBlock_pfRoot (hn : 0 < n) (hN : 2 * n ≤ N) :
    (infinityBlock N n).charpoly.rootMultiplicity (pfRoot (infinityBlock N n)) = 1 := by
  have : Nonempty (State N n) := ⟨(independentPacked hN).1⟩
  have hA := infinityBlock_isHermitian (N := N) (n := n)
  obtain ⟨u, _, _, hu⟩ := infinityBlock_pfRoot_eigenvector_line hn hN
  have huniq (i j) (hi : hA.eigenvalues i = pfRoot (infinityBlock N n))
      (hj : hA.eigenvalues j = pfRoot (infinityBlock N n)) : i = j := by
    by_contra hij
    obtain ⟨c, hc⟩ := hu _ (by rw [mulVec_eigvec hA, hi])
    obtain ⟨d, hd⟩ := hu _ (by rw [mulVec_eigvec hA, hj])
    have hii : eigvec hA i ⬝ᵥ eigvec hA i = 1 := by simpa using eigvec_dot hA i i
    have hjj : eigvec hA j ⬝ᵥ eigvec hA j = 1 := by simpa using eigvec_dot hA j j
    have hij' : eigvec hA i ⬝ᵥ eigvec hA j = 0 := by simpa [hij] using eigvec_dot hA i j
    rw [hc, hd, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hij'
    exact (mul_ne_zero (fun hz => by simp [hc, hz] at hii)
      (mul_ne_zero (fun hz => by simp [hd, hz] at hjj)
        (fun hz => by simp [hc, smul_dotProduct, dotProduct_smul, hz] at hii))) hij'
  rw [rootMultiplicity_charpoly_eq_card hA, card_eq_one]
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_pfRoot hA
  refine ⟨i, Finset.ext fun j => ?_⟩
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun hj => huniq j i hj hi, fun hj => hj ▸ hi⟩

end PottsDiscontinuity.SixVertex
