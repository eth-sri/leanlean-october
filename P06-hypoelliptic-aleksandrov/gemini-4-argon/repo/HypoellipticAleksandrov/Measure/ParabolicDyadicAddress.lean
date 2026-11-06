module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicMeasure
public import Mathlib.Basic.Countable.Basic

/-!
# Heterogeneous parabolic dyadic addresses

This module joins the finite parabolic dyadic address families across all
generations.  It records truncation, the resulting prefix order, and the cell
geometry determined solely by that order.  In particular, no density or
ink-spots data enter this API.
-/

@[expose] public section

open Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/- An addressed parabolic dyadic cell together with its generation. -/
abbrev ParabolicDyadicAddress (d : Nat) : Type :=
  Sigma (ParabolicDyadicIndex d)

/- Restrict a parabolic dyadic address to an earlier generation. -/
def parabolicDyadicTruncate {d m n } (hmn : m <= n)
    (index : ParabolicDyadicIndex d n) : ParabolicDyadicIndex d m :=
  fun j => index (j.castLE hmn)

/- Address `a` is a prefix of `b` when it is the truncation of `b` to the
generation of `a`. -/
def parabolicDyadicAddressPrefix {d }
    (a b : ParabolicDyadicAddress d) : Prop :=
  exists h : a.1 <= b.1, parabolicDyadicTruncate h b.2 = a.2

/- Truncating an address to its own generation does nothing. -/
theorem parabolicDyadicTruncate_self {d n }
    (index : ParabolicDyadicIndex d n) :
    parabolicDyadicTruncate (le_refl n) index = index := by
  funext j
  simp only [parabolicDyadicTruncate]
  apply congrArg index
  exact Fin.ext (by rfl)

private theorem parabolicDyadicHalfOpenCell_subset_truncate {d m n }
    (hmn : m <= n) (index : ParabolicDyadicIndex d n) :
    parabolicDyadicHalfOpenCell index ⊆
      parabolicDyadicHalfOpenCell (parabolicDyadicTruncate hmn index) := by
  induction n, hmn using Nat.le_induction with
  | base =>
      exact Subset.rfl
  | succ n hmn ih =>
      calc
        parabolicDyadicHalfOpenCell index ⊆
            parabolicDyadicHalfOpenCell (parabolicDyadicParent index) := by
          simpa only [parabolicDyadicChildIndex_parent_last] using
            (parabolicDyadicHalfOpenCell_child_subset
              (parabolicDyadicParent index) (index (Fin.last n)))
        _ ⊆ parabolicDyadicHalfOpenCell
            (parabolicDyadicTruncate hmn (parabolicDyadicParent index)) :=
          ih (parabolicDyadicParent index)
        _ = parabolicDyadicHalfOpenCell
            (parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index) := by
          calc
            parabolicDyadicHalfOpenCell
                (parabolicDyadicTruncate hmn (parabolicDyadicParent index)) =
                parabolicDyadicHalfOpenCell
                (parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index) := by
                    have _h_inl_11 (hmn : m <= n) (index : ParabolicDyadicIndex d (n + 1)) : parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index = parabolicDyadicTruncate hmn (parabolicDyadicParent index) := by
                      funext j
                      simp only [parabolicDyadicTruncate, parabolicDyadicParent]
                      apply congrArg index
                      exact Fin.ext (by rfl)
                    rw [_h_inl_11]

/- A cell is contained in every addressed ancestor cell. -/
theorem parabolicDyadicHalfOpenCell_subset_of_addressPrefix {d }
    {a b : ParabolicDyadicAddress d} (hab : parabolicDyadicAddressPrefix a b) :
    parabolicDyadicHalfOpenCell b.2 ⊆ parabolicDyadicHalfOpenCell a.2 := by
  rcases hab with ⟨hmn, htruncate⟩
  rw [← htruncate]
  exact parabolicDyadicHalfOpenCell_subset_truncate hmn b.2

/- The open cell is contained in the corresponding half-open cell. -/
theorem parabolicDyadicOpenCell_subset_halfOpenCell {d n }
    (index : ParabolicDyadicIndex d n) :
    parabolicDyadicOpenCell index ⊆ parabolicDyadicHalfOpenCell index := by
  rintro ⟨time, velocity⟩ hz
  rw [mem_parabolicDyadicOpenCell_iff] at hz
  rw [mem_parabolicDyadicHalfOpenCell_iff, mem_parabolicDyadicTimeCell_iff,
    mem_parabolicDyadicVelocityCell_iff]
  refine ⟨⟨hz.1, hz.2.1.le⟩, fun coordinate => ?_⟩
  exact ⟨(hz.2.2 coordinate).1, (hz.2.2 coordinate).2.le⟩

/- Two half-open addressed cells which meet have comparable addresses. -/
theorem disjoint_parabolicDyadicOpenCell_of_incomparable {d }
    {a b : ParabolicDyadicAddress d}
    (hab : ¬ parabolicDyadicAddressPrefix a b)
    (hba : ¬ parabolicDyadicAddressPrefix b a) :
    Disjoint (parabolicDyadicOpenCell a.2) (parabolicDyadicOpenCell b.2) := by
  have _h_inl_15 : Disjoint (parabolicDyadicHalfOpenCell a.2) (parabolicDyadicHalfOpenCell b.2) := by
    classical
    by_contra hdisjoint
    have _h_inl_15 : parabolicDyadicAddressPrefix a b ∨ parabolicDyadicAddressPrefix b a := by
        classical
        rcases a with ⟨m, a⟩
        rcases b with ⟨n, b⟩
        by_cases hmn : m <= n
        · by_cases htruncate : parabolicDyadicTruncate hmn b = a
          · exact Or.inl ⟨hmn, htruncate⟩
          · exfalso
            apply hdisjoint
            exact (parabolicDyadicHalfOpenCell_disjoint_of_ne htruncate).symm.mono
              Subset.rfl (parabolicDyadicHalfOpenCell_subset_truncate hmn b)
        · have hnm : n <= m := Nat.le_of_not_ge hmn
          by_cases htruncate : parabolicDyadicTruncate hnm a = b
          · exact Or.inr ⟨hnm, htruncate⟩
          · exfalso
            apply hdisjoint
            exact (parabolicDyadicHalfOpenCell_disjoint_of_ne htruncate).mono
              (parabolicDyadicHalfOpenCell_subset_truncate hnm a) Subset.rfl


    rcases _h_inl_15 with
      hab' | hba'
    · exact hab hab'
    · exact hba hba'
  exact _h_inl_15.mono
    (parabolicDyadicOpenCell_subset_halfOpenCell a.2)
    (parabolicDyadicOpenCell_subset_halfOpenCell b.2)

/- Heterogeneous parabolic dyadic addresses form a countable type. -/
instance parabolicDyadicAddressCountable (d : Nat) : Countable (ParabolicDyadicAddress d) := by
  infer_instance

end

end HypoellipticAleksandrov.Parabolic
