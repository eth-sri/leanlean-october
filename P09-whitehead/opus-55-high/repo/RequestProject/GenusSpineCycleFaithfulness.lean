import RequestProject.GenusSpineRetractionHomotopy
import RequestProject.OrderNormalizedMapInjectivity
import RequestProject.Tac


/-! The actual normalized full-cube map reflects zero on surviving-spine two-cycles. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def genusSpineOrdinaryCells : Set (GenusSpineCell q) :=
  {c | ∃ a : QOld (cmpRel _), c.1 = Sum.inl a}

def genusSpineCellToFullCube (c : GenusSpineCell q) :=
  (genusSpineCellToOld q c).1

theorem genusSpineCellToFullCube_monotone : Monotone (genusSpineCellToFullCube q) :=
  fun _ _ h => genusSpineCellToOld_monotone q h

theorem genusSpineCellToFullCube_injOn_ordinary :
    Set.InjOn (genusSpineCellToFullCube q) (genusSpineOrdinaryCells q) := by
  rintro c ⟨a, ha⟩ d ⟨b, hb⟩ he
  have hab := Subtype.ext (by
    simpa [genusSpineCellToFullCube, genusSpineCellToOld, truncatedCellRetraction, ha, hb] using he)
  apply Subtype.ext
  simp_all

theorem genusSpineRetraction_ordinary c :
    genusSpineRetraction q c ∈ genusSpineOrdinaryCells q :=
  ⟨truncatedCellRetraction c.1, rfl⟩

theorem genusSpine_normalized_retraction_support
    z
    t
    (ht : t ∈ (normalizeOrdChain2 (chain2
      (orderCxMap (genusSpineRetraction q) (genusSpineRetraction_monotone q)) z)).support) :
    t.1.1 ∈ genusSpineOrdinaryCells q ∧ t.1.2.1 ∈ genusSpineOrdinaryCells q ∧
      t.1.2.2 ∈ genusSpineOrdinaryCells q := by
  classical
  obtain ⟨a, ha, he⟩ := normalizeOrdChain2_support _ _ ht
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  rwd [← he, ← hb]
  exact ⟨genusSpineRetraction_ordinary q b.1.1,
    genusSpineRetraction_ordinary q b.1.2.1, genusSpineRetraction_ordinary q b.1.2.2⟩

/-- Every actual strict two-cycle of the surviving spine is supported on retained
ordinary cells, by the proved dimension-two retraction homotopy. -/
theorem genusSpine_cycle_ordinary_support d
    (hd : Comb.bdry2 (genusSpineCx q) d = 0) t
    (ht : t ∈ d.support) :
    t.1.1 ∈ genusSpineOrdinaryCells q ∧ t.1.2.1 ∈ genusSpineOrdinaryCells q ∧
      t.1.2.2 ∈ genusSpineOrdinaryCells q := by
  let z := chain2 (strictOrderIncl _) d
  have hcycle : Comb.bdry2 _ z = 0 := by
    rwd [bdry2_chain2, hd, map_zero]
  have he := genusSpine_normalized_retraction_cycle q z hcycle
  have hnorm := normalizeOrdChain2_inclusion d
  apply genusSpine_normalized_retraction_support q z t
  aesop

/-- The actual normalized map to full quotient cubes is faithful on surviving-spine
cycles; this is proved from ordinary-cell injectivity and the actual spine retraction. -/
theorem genusSpine_cycle_zero_of_normalized_full_image d
    (hd : Comb.bdry2 (genusSpineCx q) d = 0)
    (hz : normalizedStrictChain2 (genusSpineCellToFullCube q)
      (genusSpineCellToFullCube_monotone q) d = 0) : d = 0 :=
  normalizedStrictChain2_zero_of_injOn _ _ _
    (genusSpineCellToFullCube_injOn_ordinary q) d
    (genusSpine_cycle_ordinary_support q d hd) hz
