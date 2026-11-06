import Mathlib.Tactic

import RequestProject.GenusSpineRetractionHomotopy
import RequestProject.OrderNormalizedMapInjectivity

/-! The actual normalized full-cube map reflects zero on surviving-spine two-cycles. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def genusSpineOrdinaryCells : Set (GenusSpineCell q) :=
  {c | ∃ a : QOld (cmpRel (GenusVertex q)), c.1 = Sum.inl a}

def genusSpineCellToFullCube (c : GenusSpineCell q)  :=
  (genusSpineCellToOld q c).1

abbrev genusSpineCellToFullCube_monotone :=
  FiniteChains.Davis.Genus.genusSpineCellToOld_monotone

theorem genusSpineCellToFullCube_injOn_ordinary :
    Set.InjOn (genusSpineCellToFullCube q) (genusSpineOrdinaryCells q) := by
  rintro c ⟨a, ha⟩ d ⟨b, hb⟩ he
  have hab : a = b := Subtype.ext (by
    simp_all [genusSpineCellToFullCube, genusSpineCellToOld, truncatedCellRetraction])
  apply Subtype.ext
  rw  [ha, hb, hab]

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
  
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  rw (config := { transparency := .default }) [← he, ← hb]
  exact ⟨genusSpineRetraction_ordinary q b.1.1,
    genusSpineRetraction_ordinary q b.1.2.1, genusSpineRetraction_ordinary q b.1.2.2⟩

variable (d : (genusSpineCx q).F →₀ ℤ)
variable (hd : Comb.bdry2 (genusSpineCx q) d = 0)
include hd in
/-- Every actual strict two-cycle of the surviving spine is supported on retained
ordinary cells, by the proved dimension-two retraction homotopy. -/
theorem genusSpine_cycle_ordinary_support 
     (t : (genusSpineCx q).F)
    (ht : t ∈ d.support) :
    t.1.1 ∈ genusSpineOrdinaryCells q ∧ t.1.2.1 ∈ genusSpineOrdinaryCells q ∧
      t.1.2.2 ∈ genusSpineOrdinaryCells q := by
  change Comb.bdry2 (strictOrderCx (GenusSpineCell q)) d = 0 at hd
  let z := chain2 (strictOrderIncl (GenusSpineCell q)) d
  have hcycle : Comb.bdry2 (orderCx (GenusSpineCell q)) z = 0 := by
    grind [FiniteChains.Comb.bdry2_chain2]
  have he := genusSpine_normalized_retraction_cycle q z hcycle
  have hnorm : normalizeOrdChain2 z = d := normalizeOrdChain2_inclusion d
  rw  [hnorm] at he
  apply genusSpine_normalized_retraction_support q z t
  rwa [he]

include hd in
/-- The actual normalized map to full quotient cubes is faithful on surviving-spine
cycles; this is proved from ordinary-cell injectivity and the actual spine retraction. -/
abbrev genusSpine_cycle_zero_of_normalized_full_image 
    
    (hz : normalizedStrictChain2 (genusSpineCellToFullCube q)
      (genusSpineCellToFullCube_monotone q) d = 0)  :=
  normalizedStrictChain2_zero_of_injOn _ _ (genusSpineOrdinaryCells q)
    (genusSpineCellToFullCube_injOn_ordinary q) d
    (genusSpine_cycle_ordinary_support q d hd) hz

end FiniteChains.Davis.Genus
