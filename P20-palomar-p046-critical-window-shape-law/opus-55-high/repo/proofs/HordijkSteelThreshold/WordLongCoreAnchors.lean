module

public import proofs.HordijkSteelThreshold.WordEndPaths
public import proofs.HordijkSteelThreshold.WordCoreSideVolume

public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

theorem word_exists_padded_core (s : List Bool) (r : ℕ) (h : 2 * r < s.length) :
    ∃ core left right : List Bool, core ≠ [] ∧ s = left ++ core ++ right ∧
      left.length = r ∧ right.length = r :=
  ⟨(s.drop r).take $ s.length - 2 * r, s.take r, (s.drop r).drop $ s.length - 2 * r,
    List.ne_nil_of_length_pos $ by simp; omega, by simp, by simp; omega, by simp; omega⟩

end HordijkSteelThreshold
