import RequestProject.TruncatedCellDimension
import RequestProject.SpineCollapse


/-! Read actual codimension-one face incidences in the collapse's coordinate indices. -/
namespace FiniteChains.Davis
open RACG Mirror
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

theorem mem_cofaces_of_coordinateFace {c d : Cube V}
    (hface : CoordinateFace c d) (hc : (freeSet c).card = 2)
    (hd : (freeSet d).card = 3) (hL : freeSet d ∈ L.faces) : d ∈ cofaces L c := by
  classical
  have hsub : freeSet c ⊆ freeSet d := by
    intro v hv
    rcases hface v with h | h
    · exact mem_freeSet.mpr h
    simp_all
  have hcard : (freeSet d \ freeSet c).card = 1 := by
    grind
  cases' Finset.card_eq_one.mp hcard with j hj
  have hjd : j ∈ freeSet d := by grind
  have hjc : j ∉ freeSet c := by grind
  have hset : freeSet d = insert j (freeSet c) := by
    ext v
    constructor
    · intro hv
      by_cases hvc : v ∈ freeSet c
      · exact Finset.mem_insert_of_mem hvc
      · have hm : v ∈ freeSet d \ freeSet c := by grind
        simp_all
    grind
  apply mem_cofaces.mpr
  refine ⟨j, (by simp_all), hset ▸ hL, ?_⟩
  funext v
  by_cases hvj : v = j
  · subst v
    simpa using mem_freeSet.mp hjd
  · rw [Function.update_of_ne hvj]
    by_cases hvd : v ∈ freeSet d
    · have hvc : v ∈ freeSet c := by
        simp_all
      exact (mem_freeSet.mp hvd).trans (mem_freeSet.mp hvc).symm
    · exact ((hface v).resolve_left (fun h => hvd (mem_freeSet.mpr h))).symm

theorem truncatedCell_inc_of_le (c : TruncatedCell A) d
    (hcd : c ≤ Sum.inl d) (hc : truncatedCellDimension c = 2)
    (hd : d.1.spx.card = 3) (hL : d.1.spx ∈ L.faces) :
    qCubeToCoordinate d.1 ∈ spineInc L (truncatedFaceIndex c) := by
  classical
  cases c with
  | inl c =>
    have hf := (qCubeToCoordinate_face_iff c.1 d.1).mp hcd
    have hdim : (freeSet (qCubeToCoordinate c.1)).card = 2 := by
      aesop
    have hc' : c.1.spx.card = 2 := hc
    simpa [spineInc, truncatedFaceIndex, hc'] using
      mem_cofaces_of_coordinateFace hf hdim
        (by simpa using hd) (by simpa using hL)
  | inr σ =>
    have hsub := hcd.1
    have hσ : σ.1.card = 3 := by
      change σ.1.card - 1 = 2 at hc
      omega
    have he :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have ht : IsTri L σ.1 := ⟨he ▸ hL, hσ⟩
    have ht' := he ▸ ht
    have hz := qCubeToCoordinate_sgn_zero d.1 hcd.2
    simp [spineInc, truncatedFaceIndex, ht', hz, he]

theorem truncatedCell_le_of_inc c (d : QOld A)
    (hi : qCubeToCoordinate d.1 ∈ spineInc L (truncatedFaceIndex c)) :
    c ≤ Sum.inl d := by
  classical
  cases c with
  | inl c =>
    have hm : qCubeToCoordinate d.1 ∈ cofaces L (qCubeToCoordinate c.1) := by
      grind [spineInc, truncatedFaceIndex]
    obtain ⟨j, _, _, he⟩ := mem_cofaces.mp hm
    apply (qCubeToCoordinate_face_iff c.1 d.1).mpr
    intro v
    rw [he]
    grind
  | inr σ =>
    have he : qCubeToCoordinate d.1 = posCube σ.1 := by
      grind [spineInc, truncatedFaceIndex]
    have hs : d.1.spx = σ.1 := by
      have hh := congrArg freeSet he
      simpa using hh
    apply (cut_le_old_coordinate_iff σ d).mpr
    simp_all
