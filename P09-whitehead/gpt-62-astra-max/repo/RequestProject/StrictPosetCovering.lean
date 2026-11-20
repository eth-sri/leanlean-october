module


public import RequestProject.PosetCoverUpTransform
public import RequestProject.StrictOrderComplex

@[expose] public section

/-! A poset covering restricts to the genuine nondegenerate cellular
two-skeleton. This is the cover used with strict cellular acyclicity.
Unverified source. -/

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
  (hf : IsPosetCover f)

def strictMap := strictOrderCxMap f hf.strictMono

include hf in
/-- Restrict interval lifting to nonidentity arrows. -/
theorem strictRelCover : RelCover (· < ·) (· < ·) f where
  mono := hf.strictMono
  surj := hf.surj
  up a q h := by
    obtain ⟨b, ⟨hab, hb⟩, uniq⟩ := hf.up a q h.le
    exact ⟨b, ⟨lt_of_le_of_ne hab (by rintro rfl; grind), hb⟩, fun z hz => uniq z ⟨hz.1.le, hz.2⟩⟩
  down a q h := by
    obtain ⟨b, ⟨hba, hb⟩, uniq⟩ := hf.down a q h.le
    exact ⟨b, ⟨lt_of_le_of_ne hba (by rintro rfl; grind), hb⟩, fun z hz => uniq z ⟨hz.1.le, hz.2⟩⟩

theorem strictMap_isCovering : IsCovering hf.strictMap := hf.strictRelCover.isCovering

end FiniteChains.Comb.IsPosetCover
