import Mathlib.Tactic

import RequestProject.TruncatedCellDimension
import RequestProject.SpineCollapse

/-! Read actual codimension-one face incidences in the collapse's coordinate indices. -/
namespace FiniteChains.Davis
open RACG Mirror
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

  {L : ASC V}
theorem mem_cofaces_of_coordinateFace  {c d : Cube V}
    (hface : CoordinateFace c d) (hc : (freeSet c).card = 2)
    (hd : (freeSet d).card = 3) (hL : freeSet d ∈ L.faces) : d ∈ cofaces L c := by
  classical
  have hsub : freeSet c ⊆ freeSet d := by
    intro v hv
    have hvf := mem_freeSet.mp hv
    rcases hface v with h | h
    · exact mem_freeSet.mpr h
    · exact mem_freeSet.mpr (h.symm.trans hvf)
  have hcard : (freeSet d \ freeSet c).card = 1 := by
    grind
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hjd  := (Finset.mem_sdiff.mp
    (hj ▸ Finset.mem_singleton_self j)).1
  have hjc  := (Finset.mem_sdiff.mp
    (hj ▸ Finset.mem_singleton_self j)).2
  have hset : freeSet d = insert j (freeSet c) := by
    ext v
    constructor
    · intro hv
      by_cases hvc : v ∈ freeSet c
      · exact Finset.mem_insert_of_mem hvc
      · have hm  := Finset.mem_sdiff.mpr ⟨hv, hvc⟩
        rw [hj] at hm
        exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hm))
    · grind
  apply mem_cofaces.mpr
  refine ⟨j, (fun h => hjc (mem_freeSet.mpr h)), hset ▸ hL, ?_⟩
  funext v
  by_cases hvj : v = j
  · subst v
    simpa using mem_freeSet.mp hjd
  · rw [Function.update_of_ne hvj]
    by_cases hvd : v ∈ freeSet d
    · grind [freeSet]
    · exact ((hface v).resolve_left (fun h => hvd (mem_freeSet.mpr h))).symm

theorem truncatedCell_inc_of_le  (c : TruncatedCell A) (d : QOld A)
    (hcd : c ≤ Sum.inl d) (hc : truncatedCellDimension c = 2)
    (hd : d.1.spx.card = 3) (hL : d.1.spx ∈ L.faces) :
    qCubeToCoordinate d.1 ∈ spineInc L (truncatedFaceIndex c) := by
  classical
  cases c with
  | inl c =>
    have hf := (qCubeToCoordinate_face_iff c.1 d.1).mp hcd
    have hdim : (freeSet (qCubeToCoordinate c.1)).card = 2 := by
      simpa [truncatedCellDimension] using hc
    simp_all [spineInc, truncatedFaceIndex, mem_cofaces_of_coordinateFace]
  | inr σ =>
    have hsub  := hcd.1
    have hσ : σ.1.card = 3 := by
      
      change σ.1.card - 1 = 2 at hc
      omega
    have he  :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have ht : IsTri L σ.1 := ⟨he ▸ hL, hσ⟩
    have ht'  := he ▸ ht
    have hz := qCubeToCoordinate_sgn_zero d.1 hcd.2
    simp [spineInc, truncatedFaceIndex, ht', hz, he]

theorem truncatedCell_le_of_inc  (c : TruncatedCell A) (d : QOld A)
    (hi : qCubeToCoordinate d.1 ∈ spineInc L (truncatedFaceIndex c)) :
    c ≤ Sum.inl d := by
  classical
  cases c with
  | inl c =>
    have hm : qCubeToCoordinate d.1 ∈ cofaces L (qCubeToCoordinate c.1) := by
      aesop (add simp [spineInc, truncatedFaceIndex])
    obtain ⟨j, _, _, he⟩ := mem_cofaces.mp hm
    apply (qCubeToCoordinate_face_iff c.1 d.1).mpr
    intro v
    rw [he]
    by_cases hv : v = j
    · left
      subst v
      exact Function.update_self _ _ _
    · right
      simp [hv]
  | inr σ =>
    classical grind [FiniteChains.Davis.freeSet_qCubeToCoordinate, FiniteChains.freeSet_posCube, FiniteChains.Davis.cut_le_old_coordinate_iff, qCubeToCoordinate, posCube, spineInc, truncatedFaceIndex, freeSet]

end FiniteChains.Davis
