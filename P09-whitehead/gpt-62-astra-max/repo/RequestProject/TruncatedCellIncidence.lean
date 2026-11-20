module

public import RequestProject.TruncatedCellDimension
public import RequestProject.SpineCollapse

@[expose] public section

/-! Read actual codimension-one face incidences in the collapse's coordinate indices. -/
namespace FiniteChains.Davis
open RACG Mirror
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

variable {L : ASC V}

theorem mem_cofaces_of_coordinateFace {c d : Cube V}
    (hface : CoordinateFace c d) (hc : (freeSet c).card = 2)
    (hd : (freeSet d).card = 3) (hL : freeSet d ∈ L.faces) : d ∈ cofaces L c := by
  classical
  have hsub : freeSet c ⊆ freeSet d := by
    intro v hv
    have hvf := mem_freeSet.mp hv
    rcases hface v with h | h <;> simp_all
  have hcard : (freeSet d \ freeSet c).card = 1 := by
    grind
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hjd := (Finset.mem_sdiff.mp
    (hj ▸ Finset.mem_singleton_self j)).1
  have hjc := (Finset.mem_sdiff.mp
    (hj ▸ Finset.mem_singleton_self j)).2
  have hset : freeSet d = insert j (freeSet c) := by
    ext v
    constructor
    · intro hv
      by_cases hvc : v ∈ freeSet c
      · exact Finset.mem_insert_of_mem hvc
      · have hm := Finset.mem_sdiff.mpr ⟨hv, hvc⟩
        simp_all
    · grind
  apply mem_cofaces.mpr
  refine ⟨j, (fun h => hjc (mem_freeSet.mpr h)), hset ▸ hL, ?_⟩
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

variable (c : TruncatedCell A) (d : QOld A)

theorem truncatedCell_inc_of_le
    (hcd : c ≤ Sum.inl d) (hc : truncatedCellDimension c = 2)
    (hd : d.1.spx.card = 3) (hL : d.1.spx ∈ L.faces) :
    qCubeToCoordinate d.1 ∈ spineInc L (truncatedFaceIndex c) := by
  classical
  cases c with
  | inl c =>
    have hdim : (freeSet (qCubeToCoordinate c.1)).card = 2 := by
      simpa [truncatedCellDimension] using hc
    have hc' : c.1.spx.card = 2 := hc
    simpa [spineInc, truncatedFaceIndex, hc'] using
      mem_cofaces_of_coordinateFace ((qCubeToCoordinate_face_iff c.1 d.1).mp hcd) hdim
        (by simp_all) (by simp_all)
  | inr σ =>
    have hσ : σ.1.card = 3 := by
      change σ.1.card - 1 = 2 at hc
      omega
    have he :=
      Finset.eq_of_subset_of_card_le hcd.1 (by omega)
    have ht : IsTri L σ.1 := ⟨he ▸ hL, hσ⟩
    have ht' := he ▸ ht
    simp [spineInc, truncatedFaceIndex, ht', (qCubeToCoordinate_sgn_zero d.1 hcd.2), he]

theorem truncatedCell_le_of_inc
    (hi : qCubeToCoordinate d.1 ∈ spineInc L (truncatedFaceIndex c)) :
    c ≤ Sum.inl d := by
  classical
  cases c with
  | inl c =>
    have hm : qCubeToCoordinate d.1 ∈ cofaces L (qCubeToCoordinate c.1) := by
      simp only [spineInc, truncatedFaceIndex] at hi
      aesop
    obtain ⟨j, _, _, he⟩ := mem_cofaces.mp hm
    apply (qCubeToCoordinate_face_iff c.1 d.1).mpr
    intro v
    by_cases hv : v = j
    · simp_all
    · simp_all
  | inr σ =>
    have he : qCubeToCoordinate d.1 = posCube σ.1 := by
      simp only [spineInc, truncatedFaceIndex] at hi
      aesop
    have hs : d.1.spx = σ.1 := by
      simpa using (congrArg freeSet he)
    simp_all [cut_le_old_coordinate_iff]

end FiniteChains.Davis
