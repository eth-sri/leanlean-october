module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction
public import OAI.NumberTheory.DirichletL.Mellin.FiniteEulerRestoration

@[expose] public section

namespace OAI

section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    
open ActualEisensteinCubic
 
open   RationalPrimeExtraction ShortDraftLatticeCount
 
 
 
open EisensteinEmbedding ConcreteTraceCRT  
 
 
open scoped LSeries.notation ArithmeticFunction.Moebius
 
 
 
 
 
 
 
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal      
 
 
 
 
 
 

 
namespace FiniteSFactor

end FiniteSFactor

 

namespace CompactScaleBridge

open ConcretePrimeRowBridge ShortDraftHeckeBridge



theorem idealsUpTo_card_le  N  :
    (idealsUpTo N).card ≤ 64 * (N + 1) := by
  classical
  have himage : (columnsUpTo N).card = (idealsUpTo N).card := by
    unfold columnsUpTo
    exact Finset.card_image_of_injective _ idealGenerator_injective
  rw [← himage]
  apply ShortDraftLatticeCount.actual_eisenstein_count
  intro x hx
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hx
  have hnorm : Ideal.absNorm I ≤ N := (mem_idealsUpTo.mp hI).2
  have hqNat : ShortDraftLatticeCount.qNat (idealGenerator I) ≤ N := by
    rw [ActualEisensteinCubic.qNat_eq_absNorm_span, span_idealGenerator]
    exact hnorm
  have hnonneg := ShortDraftLatticeCount.qO_nonneg (idealGenerator I)
  
  change (ShortDraftLatticeCount.q
    (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat ≤ N at hqNat
  simp_all









end CompactScaleBridge

end

end OAI
