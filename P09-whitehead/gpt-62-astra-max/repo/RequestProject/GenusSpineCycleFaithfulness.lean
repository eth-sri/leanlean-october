module

public import RequestProject.GenusSpineRetractionHomotopy
public import RequestProject.OrderNormalizedMapInjectivity

@[expose] public section

/-! The actual normalized full-cube map reflects zero on surviving-spine two-cycles. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def genusSpineOrdinaryCells : Set (GenusSpineCell q) :=
  {c | ∃ a : QOld _, c.1 = Sum.inl a}

def genusSpineCellToFullCube (c : GenusSpineCell q) :=
  (genusSpineCellToOld q c).1

theorem genusSpineCellToFullCube_monotone : Monotone (genusSpineCellToFullCube q) :=
  fun _ _ h => genusSpineCellToOld_monotone q h

theorem genusSpineCellToFullCube_injOn_ordinary :
    Set.InjOn (genusSpineCellToFullCube q) (genusSpineOrdinaryCells q) := by
  rintro c ⟨a, ha⟩ d ⟨b, hb⟩ he
  have hab : a = b := Subtype.ext (by
    simp_all [genusSpineCellToFullCube, genusSpineCellToOld, truncatedCellRetraction, ha, hb])
  apply Subtype.ext <;> simp_all

theorem genusSpineRetraction_ordinary (c : GenusSpineCell q) :
    genusSpineRetraction q c ∈ genusSpineOrdinaryCells q :=
  ⟨truncatedCellRetraction c.1, rfl⟩

theorem genusSpine_normalized_retraction_support
    (z : (orderCx (GenusSpineCell q)).F →₀ ℤ)
    (t : StrictOrdTri (GenusSpineCell q))
    (ht : t ∈ (normalizeOrdChain2 (chain2
      (orderCxMap (genusSpineRetraction q) (genusSpineRetraction_monotone q)) z)).support) :
    t.1.1 ∈ genusSpineOrdinaryCells q ∧ t.1.2.1 ∈ genusSpineOrdinaryCells q ∧
      t.1.2.2 ∈ genusSpineOrdinaryCells q := by
  classical
  obtain ⟨a, ha, he⟩ := normalizeOrdChain2_support _ _ ht
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha); erw [← he, ← hb]; exact ⟨genusSpineRetraction_ordinary q _,
    genusSpineRetraction_ordinary q _, genusSpineRetraction_ordinary q _⟩

variable (d : (genusSpineCx q).F →₀ ℤ) (hd : Comb.bdry2 (genusSpineCx q) d = 0)
include hd

/-- Every actual strict two-cycle of the surviving spine is supported on retained
ordinary cells, by the proved dimension-two retraction homotopy. -/
theorem genusSpine_cycle_ordinary_support (t : (genusSpineCx q).F)
    (ht : t ∈ d.support) :
    t.1.1 ∈ genusSpineOrdinaryCells q ∧ t.1.2.1 ∈ genusSpineOrdinaryCells q ∧
      t.1.2.2 ∈ genusSpineOrdinaryCells q := by
  change Comb.bdry2 (strictOrderCx (GenusSpineCell q)) d = 0 at hd
  let z := chain2 (strictOrderIncl (GenusSpineCell q)) d
  have hcycle : Comb.bdry2 _ z = 0 := by
    rw [bdry2_chain2, hd, map_zero]
  have he := genusSpine_normalized_retraction_cycle q z hcycle
  erw [(normalizeOrdChain2_inclusion d)] at he
  apply genusSpine_normalized_retraction_support q z t
  rwa [he]

/-- The actual normalized map to full quotient cubes is faithful on surviving-spine
cycles; this is proved from ordinary-cell injectivity and the actual spine retraction. -/
theorem genusSpine_cycle_zero_of_normalized_full_image
    (hz : normalizedStrictChain2 _
      (genusSpineCellToFullCube_monotone q) d = 0) : d = 0 :=
  normalizedStrictChain2_zero_of_injOn _ _ _
    (genusSpineCellToFullCube_injOn_ordinary q) d
    (genusSpine_cycle_ordinary_support q d hd) hz

end FiniteChains.Davis.Genus
