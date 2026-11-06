module
public import Mathlib

public import PottsDiscontinuity.TorusRC.BoxProduct
public import PottsDiscontinuity.TorusRC.CollarEdges
public import PottsDiscontinuity.TorusRC.RetainedOpening

/-! # The corrected chain estimate on each barrier-compatible fiber -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}


noncomputable local instance cPrimeFiberEdgeDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _
noncomputable local instance cPrimeFiberRemaining (hN : Even N) (hM : Even M)
    (F : FK.Configuration (fullDiamondGraph hN hM)) :
    Fintype (FK.RemainingConfiguration (fullDiamondGraph hN hM) F) := Fintype.ofFinite _

noncomputable local instance cPrimeFiberBoxEdges (c : RotatedVertex) (R : ℕ) :
    Fintype (liftedBoxGraph c R).edgeSet := Fintype.ofFinite _

noncomputable section

def interiorChainIndices (M n R : ℕ) : Finset ℕ :=
  (Finset.range (M / (2 * n))).filter  fun j => R < 2 * n * j ∧ 2 * n * j + R < M 

/-- The finite-energy exponent 2(R+2n) is independent of M. On every exterior
state compatible with B, C-prime is bounded below by this factor times the
product of the free-box connection probabilities for all interior blocks. -/
theorem liftedCPrime_fiber_lower_bound (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (x : ℤ) (hx : Even x) (n R : ℕ)
    (hn : 0 < n) (hnleft : 3 * n ≤ N / 2) (hnR : 2 * n ≤ R)
    (hRN : 2 * R < N) (hRM : 2 * R < M)
    (hleft : (N / 2 : ℤ) ≤ x - R) (hright : x + R ≤ (N : ℤ))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (hH : H ∈ rightHalfBarrierExterior hN hM hN4 hM4 hNp hMp n) :
    fkOpenEnergy (torusRCBridgeParameters q) ^ (2 * (R + 2 * n)) *
       ∏ j ∈ interiorChainIndices M n R,
        liftedBoxFreeConnectionProbability (torusRCBridgeParameters q)
          (liftedChainSite x hx n j) R (liftedChainSite x hx n j)
          (liftedChainSite x hx n (j + 1))  ≤
      torusRCFiberEventProbability
        (torusRCFiberLaw hN hM hN4 hM4 q (rightHalfFrozenEdges hN hM hN4 hM4) H)
        {A | rightHalfRestore hN hM hN4 hM4 H A ∈
          liftedCPrime hNp hMp (N / 2 : ℤ) (N : ℤ) x hx hM n R} := by
  
  let F := rightHalfFrozenEdges hN hM hN4 hM4
  let y := liftedChainSite x hx n
  let I := interiorChainIndices M n R
  let E : Set (FK.RemainingConfiguration (fullDiamondGraph hN hM) F) :=
    {A | ∀ j ∈ I, liftedBoxConnection hNp hMp
      (rightHalfRestore hN hM hN4 hM4 H A) (N / 2 ) N R (y j) (y (j + 1))}
  let s := columnCollarEdges hNp hMp x (R + 2 * n)
  
  
  have hs : ∀ e ∈ s, rightHalfInteriorSite e :=
    columnCollarEdges_interior hNp hMp x (R + 2 * n) (by omega) (by omega)
  let S := rightHalfRetainedSet hN hM hN4 hM4 s hs
  
  
  
  have hcard : S.card ≤ 2 * (R + 2 * n) := by
    rw [rightHalfRetainedSet_card]
    exact columnCollarEdges_card_le hNp hMp x (R + 2 * n)
  have hc0 := (fkOpenEnergy_pos (torusRCBridgeParameters q)).le
  
  
  have hmul := mul_le_mul (pow_le_pow_of_le_one hc0
                             (fkOpenEnergy_le_one (torusRCBridgeParameters q)) hcard) (liftedBoxFreeConnectionProbability_prod_le_fiber hN hM hN4 hM4 hNp hMp q
                                   I y (fun j => y (j + 1)) R hRN hRM
                                   (fun _ _ => hleft) (fun _ _ => hright)
                                    fun j hj => by
                                     
                                     have hb' :  R  < 2 * (n : ℤ) * j := by exact_mod_cast  (Finset.mem_filter.mp hj).2.1 
                                     change 0 < 2 * (n : ℤ) * j - R
                                     omega 
                                   (fun j hj => by
                                     
                                     change 2 *  n  * j + R < (M : ℤ)
                                     exact_mod_cast  (Finset.mem_filter.mp hj).2.2 ) H) (by
                                        apply Finset.prod_nonneg
                                        intro j _
                                        exact torusRCFiberEventProbability_nonneg _ _) (pow_nonneg hc0 S.card)
  apply (hmul.trans (torusRCFiber_allOpen_inter_ge hN hM hN4 hM4 q F H S E (fun A B hAB hA j hj => liftedBoxConnection_mono hNp hMp _ _ R (y j) (y (j + 1))
                                                                        (rightHalfRestore_mono hN hM hN4 hM4 H hAB) (hA j hj)))).trans
  apply FK.FiniteProbability.expectation_mono
  intro A
  have hsub : A ∈  {A | (FK.edgeRestrictionConfigurationEquiv (fullDiamondGraph hN hM)
        F S).val ⊆ A.val} ∩ E  →
      rightHalfRestore hN hM hN4 hM4 H A ∈
        liftedCPrime hNp hMp (N / 2 ) N x hx hM n R := by
    rintro ⟨hopenA, hEA⟩
    
    apply liftedCPrime_of_interior_and_collar hNp hMp _ _ x hx hM n R hn hnR
      (by omega) (by omega) _
    · apply columnCollarOpen_of_barrier_and_edges hNp hMp x (R + 2 * n) n
        (by omega) (by omega) hnleft _ ((barrier_rightHalfRestore_iff hN hM hN4 hM4 hNp hMp n hnleft H A _).mpr hH)
      exact rightHalfRetainedSet_open hN hM hN4 hM4 s hs H A hopenA
    · intro j hj hb ht
      exact hEA j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hb, ht⟩)
  by_cases hA : A ∈  {A | (FK.edgeRestrictionConfigurationEquiv (fullDiamondGraph hN hM)
        F S).val ⊆ A.val} ∩ E 
  · simp_all
  · simp only [Set.indicator_of_notMem hA]
    by_cases hC : rightHalfRestore hN hM hN4 hM4 H A ∈
        liftedCPrime hNp hMp (N / 2 ) N x hx hM n R <;>
      simp [hC]

end

end PottsDiscontinuity.TorusRC
