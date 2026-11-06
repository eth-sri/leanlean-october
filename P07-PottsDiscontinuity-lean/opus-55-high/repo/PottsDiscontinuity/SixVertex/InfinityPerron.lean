module

public import PottsDiscontinuity.LinearAlgebra.PerronFrobenius
public import PottsDiscontinuity.SixVertex.InfinityHalfSpectrum
public import PottsDiscontinuity.SixVertex.InfinityIrreducible

/-! # Perron eigenvalue of the restriction and the full limiting block -/

public section

open Finset Matrix
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

section
variable (hN : 2 * n ≤ N)
/-- Embed the existing even-position state into a sufficiently long row. -/
def embeddedEvenState  : State N n :=
  ⟨(evenState n).1.map (Fin.castLEEmb hN), by grind⟩

theorem mem_embeddedEvenState (i : Fin N) :
    i ∈ (embeddedEvenState hN).1 ↔ i.val % 2 = 0 ∧ i.val < 2 * n := by
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := mem_map.mp hi
    have hp := (mem_evenState j).mp hj
    aesop
  · rintro ⟨he, hi⟩
    refine mem_map.mpr ⟨⟨i.val, hi⟩, (mem_evenState _).mpr he, ?_⟩
    rfl

def independentPacked  : IndependentState N n :=
  ⟨embeddedEvenState hN, by
    intro i hi hni
    obtain ⟨he, hi⟩ := (mem_embeddedEvenState hN i).mp hi
    have hnext := nxt_val_of_lt i (by omega)
    have hne := ((mem_embeddedEvenState hN (nxt i)).mp hni).1
    omega⟩
end

/-- PF positivity, a positive eigenvector, and algebraic simplicity on the genuine support. -/
theorem infinityRestriction_perronFrobenius (hn : 0 < n) (hN : 2 * n ≤ N) :
    0 < pfRoot (infinityRestriction N n) ∧
    (∃ v : IndependentState N n → ℝ, (∀ x, 0 < v x) ∧
      infinityRestriction N n *ᵥ v = pfRoot (infinityRestriction N n) • v) ∧
    (infinityRestriction N n).charpoly.rootMultiplicity
      (pfRoot (infinityRestriction N n)) = 1 := by
  have : Nonempty (IndependentState N n) := ⟨independentPacked hN⟩
  obtain ⟨hp, _, _, hv, _, _, hm, _, _⟩ := perronFrobenius_irreducible
    (infinityRestriction_isHermitian (N := N)) (infinityRestriction_isIrreducible hn)
  exact ⟨hp, hv, hm⟩

/-- Restriction of a coordinate vector to the independent states. -/
def restrictIndependent (v : State N n → ℝ) : IndependentState N n → ℝ := fun x => v x.1

section
variable (v : IndependentState N n → ℝ)
/-- Extension by zero outside the independent states. -/
def extendIndependent  : State N n → ℝ :=
  fun x => if h : NoConsecutiveUp x.1 then v ⟨x, h⟩ else 0

@[simp] theorem restrictIndependent_extend  :
    restrictIndependent (extendIndependent v) = v := by
  funext x
  simp only [restrictIndependent, extendIndependent, dite_eq_left x.2]
end

section
variable (hn : 0 < n)
include hn
/-- The zero columns outside the support make restriction commute with the operator. -/
theorem restrictIndependent_mulVec (v : State N n → ℝ) :
    restrictIndependent (infinityBlock N n *ᵥ v) =
      infinityRestriction N n *ᵥ restrictIndependent v := by
  funext x
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun y : State N n => NoConsecutiveUp y.1)
    (fun y => infinityBlock N n x.1 y * v y)
  have hz : (∑ y : {y : State N n // ¬ NoConsecutiveUp y.1},
      infinityBlock N n x.1 y.1 * v y.1) = 0 := by
    apply sum_eq_zero
    intro y _
    rw [infinityBlock_symm, infinityBlock_eq_zero_of_not_noConsecutiveUp hn _ _ y.2, zero_mul]
  simp_all
  exact hs.symm

theorem infinityBlock_eigenvector_supported {μ : ℝ} (hμ : μ ≠ 0)
    {v : State N n → ℝ} (hv : infinityBlock N n *ᵥ v = μ • v)
    (x : State N n) (hx : ¬ NoConsecutiveUp x.1) : v x = 0 := by
  have hh := congrFun hv x
  rw [infinityBlock_mulVec_supported hn v x hx] at hh
  aesop

/-- Extension lifts eigenvectors from the support to the full matrix. -/
theorem extendIndependent_eigenvector {μ : ℝ}
    {v : IndependentState N n → ℝ} (hv : infinityRestriction N n *ᵥ v = μ • v) :
    infinityBlock N n *ᵥ extendIndependent v = μ • extendIndependent v := by
  funext x
  by_cases hx : NoConsecutiveUp x.1
  · have hh := congrFun (restrictIndependent_mulVec hn (extendIndependent v)) ⟨x, hx⟩
    simp_all [restrictIndependent_extend, restrictIndependent, extendIndependent]
  · rw [infinityBlock_mulVec_supported hn _ x hx]
    simp_all [extendIndependent]
end

theorem mem_spectrum_of_eigenvector {S : Type*} [Fintype S] [DecidableEq S]
    {A : Matrix S S ℝ} {μ : ℝ} {v : S → ℝ} (hv0 : v ≠ 0) (hv : A *ᵥ v = μ • v) :
    μ ∈ spectrum ℝ A := by
  have he : Module.End.HasEigenvector (Matrix.toLin' A) μ v :=
    ⟨by simp_all, hv0⟩
  have hm := (Module.End.hasEigenvalue_of_hasEigenvector he).mem_spectrum
  simp_all

section
variable (hn : 0 < n) (hN : 2 * n ≤ N)
include hn hN
/-- The support restriction and the full block have the same largest eigenvalue. -/
theorem pfRoot_infinityBlock_eq_restriction  :
    pfRoot (infinityBlock N n) = pfRoot (infinityRestriction N n) := by
  have : Nonempty (IndependentState N n) := ⟨independentPacked hN⟩
  have : Nonempty (State N n) := by aesop
  obtain ⟨hp, ⟨v, hv, he⟩, _⟩ := infinityRestriction_perronFrobenius hn hN
  have hv0 : extendIndependent v ≠ 0 := by
    intro hz
    have hzero := congrFun (congrArg restrictIndependent hz) (independentPacked hN)
    rw [restrictIndependent_extend] at hzero
    exact (hv _).ne' hzero
  have hle :=
    (isGreatest_pfRoot infinityBlock_isHermitian).2
      (mem_spectrum_of_eigenvector hv0 (extendIndependent_eigenvector hn he))
  have hfullpos := hp.trans_le hle
  have hA := infinityBlock_isHermitian (N := N) (n := n)
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_pfRoot hA
  let w := eigvec hA i
  have hw : infinityBlock N n *ᵥ w = pfRoot (infinityBlock N n) • w := by
    rw [show w = eigvec hA i from rfl, mulVec_eigvec, hi]
  have hw0 : restrictIndependent w ≠ 0 := by
    intro hz
    have hzero : w = 0 := by
      funext x
      by_cases hx : NoConsecutiveUp x.1
      · exact congrFun hz ⟨x, hx⟩
      · exact infinityBlock_eigenvector_supported hn hfullpos.ne' hw x hx
    have hh := eigvec_dot hA i i
    change w ⬝ᵥ w = _ at hh
    simp_all
  have hw' : infinityRestriction N n *ᵥ restrictIndependent w =
      pfRoot (infinityBlock N n) • restrictIndependent w := by
    rw [← restrictIndependent_mulVec hn, hw]
    rfl
  exact le_antisymm ((isGreatest_pfRoot infinityRestriction_isHermitian).2
    (mem_spectrum_of_eigenvector hw0 hw')) hle

/-- The full block has a positive largest eigenvalue in the source's range. -/
theorem pfRoot_infinityBlock_pos  :
    0 < pfRoot (infinityBlock N n) := by
  simp_all [pfRoot_infinityBlock_eq_restriction, infinityRestriction_perronFrobenius]

/-- Every eigenvector at the full block's largest eigenvalue lies on one fixed line. -/
theorem infinityBlock_pfRoot_eigenvector_line  :
    ∃ u : State N n → ℝ, u ≠ 0 ∧
      infinityBlock N n *ᵥ u = pfRoot (infinityBlock N n) • u ∧
      ∀ w : State N n → ℝ,
        infinityBlock N n *ᵥ w = pfRoot (infinityBlock N n) • w →
        ∃ c : ℝ, w = c • u := by
  have : Nonempty (IndependentState N n) := ⟨independentPacked hN⟩
  obtain ⟨_, ⟨v, hv, he⟩, _⟩ := infinityRestriction_perronFrobenius hn hN
  have hroot := pfRoot_infinityBlock_eq_restriction hn hN
  have hpos := pfRoot_infinityBlock_pos hn hN
  refine ⟨extendIndependent v, ?_, ?_, ?_⟩
  · intro hz
    have hh := congrFun (congrArg restrictIndependent hz) (independentPacked hN)
    rw [restrictIndependent_extend] at hh
    exact (hv _).ne' hh
  · rw [hroot]
    exact extendIndependent_eigenvector hn he
  · intro w hw
    have hw' : infinityRestriction N n *ᵥ restrictIndependent w =
        pfRoot (infinityRestriction N n) • restrictIndependent w := by
      rw [← restrictIndependent_mulVec hn, hw, hroot]
      rfl
    obtain ⟨c, hc⟩ := eigenspace_pfRoot_eq infinityRestriction_nonneg
      (infinityRestriction_exists_pow_pos hn) infinityRestriction_isHermitian hv he hw'
    refine ⟨c, ?_⟩
    funext x
    by_cases hx : NoConsecutiveUp x.1
    · have hh := congrFun hc ⟨x, hx⟩
      simp_all [restrictIndependent, extendIndependent]
    · rw [infinityBlock_eigenvector_supported hn hpos.ne' hw x hx]
      simp_all [extendIndependent]

/-- The largest eigenvalue of the full limiting block is algebraically simple. -/
theorem rootMultiplicity_infinityBlock_pfRoot  :
    (infinityBlock N n).charpoly.rootMultiplicity (pfRoot (infinityBlock N n)) = 1 := by
  have : Nonempty (State N n) := ⟨(independentPacked hN).1⟩
  have hA := infinityBlock_isHermitian (N := N) (n := n)
  obtain ⟨u, _, _, hu⟩ := infinityBlock_pfRoot_eigenvector_line hn hN
  have huniq : ∀ i j, hA.eigenvalues i = pfRoot (infinityBlock N n) →
      hA.eigenvalues j = pfRoot (infinityBlock N n) → i = j := by
    intro i j hi hj
    by_contra hij
    have hvi : infinityBlock N n *ᵥ eigvec hA i = pfRoot (infinityBlock N n) • eigvec hA i := by
      rw [mulVec_eigvec, hi]
    have hvj : infinityBlock N n *ᵥ eigvec hA j = pfRoot (infinityBlock N n) • eigvec hA j := by
      rw [mulVec_eigvec, hj]
    obtain ⟨c, hc⟩ := hu _ hvi
    obtain ⟨d, hd⟩ := hu _ hvj
    have hii := eigvec_dot hA i i
    have hjj := eigvec_dot hA j j
    have hij' := eigvec_dot hA i j
    have hc0 : c ≠ 0 := by
      intro hz
      simp_all
    simp_all
  rw [rootMultiplicity_charpoly_eq_card hA, card_eq_one]
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_pfRoot hA
  refine ⟨i, ?_⟩
  ext j
  simp
  exact ⟨fun hj => huniq j i hj hi, fun hj => hj ▸ hi⟩
end

end PottsDiscontinuity.SixVertex
