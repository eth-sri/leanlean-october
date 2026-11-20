module

public import PottsDiscontinuity.TorusRC.BoxInterior
public import PottsDiscontinuity.TorusRC.BoxTranslation
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

section

variable
  (θ : FK.Parameters)
    (c : RotatedVertex) (R : ℕ) (u v : RotatedVertex)

theorem liftedBoxFreeConnectionProbability_nonneg :
    0 ≤ liftedBoxFreeConnectionProbability θ c R u v :=
  torusRCFiberEventProbability_nonneg _ _

theorem liftedBoxFreeConnectionProbability_le_one :
    liftedBoxFreeConnectionProbability θ c R u v ≤ 1 := by
  simpa only [liftedBoxFreeConnectionProbability, torusRCFiberEventProbability, Set.indicator_univ, FK.FiniteProbability.expectation_const] using
    torusRCFiberEventProbability_mono (FK.law (liftedBoxGraph c R) θ (FK.BoundaryCondition.free ∅))
      (Set.subset_univ (liftedBoxFreeConnectionEvent c R u v))

end

def interiorChainIndices (M n R : ℕ) : Finset ℕ :=
  (Finset.range (M / (2 * n))).filter (fun j => R < 2 * n * j ∧ 2 * n * j + R < M)

/-- The finite-energy exponent 2(R+2n) is independent of M. On every exterior
state compatible with B, C-prime is bounded below by this factor times the
free-box connection probability raised to the number of blocks. Missing
interior factors may be inserted since probabilities are at most one. -/
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
      liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) rotatedLatticeOrigin R
        rotatedLatticeOrigin (rotatedDiagonalSite n) ^ (M / (2 * n)) ≤
      torusRCFiberEventProbability
        (torusRCFiberLaw hN hM hN4 hM4 q (rightHalfFrozenEdges hN hM hN4 hM4) H)
        {A | rightHalfRestore hN hM hN4 hM4 H A ∈
          liftedCPrime hNp hMp (N / 2 : ℤ) (N : ℤ) x hx hM n R} := by
  classical
  let F := rightHalfFrozenEdges hN hM hN4 hM4
  let y := liftedChainSite x hx n
  let I := interiorChainIndices M n R
  let E' (j : ℕ) : Set (FK.RemainingConfiguration (fullDiamondGraph hN hM) F) :=
    {A | liftedBoxConnection hNp hMp (rightHalfRestore hN hM hN4 hM4 H A)
      (N / 2 : ℤ) (N : ℤ) R (y j) (y (j + 1))}
  let E := {A | ∀ j ∈ I, A ∈ E' j}
  let s := columnCollarEdges hNp hMp x (R + 2 * n)
  have hxleft : (N / 2 : ℤ) ≤ x := by omega
  have hxright : x + 1 ≤ (N : ℤ) := by omega
  have hs : ∀ e ∈ s, rightHalfInteriorSite e :=
    columnCollarEdges_interior hNp hMp x (R + 2 * n) hxleft hxright
  let S := rightHalfRetainedSet hN hM hN4 hM4 s hs
  have hmono (j : ℕ) : IsUpperSet (E' j) := fun _ _ hAB hA =>
    liftedBoxConnection_mono hNp hMp _ _ R (y j) (y (j + 1))
      (rightHalfRestore_mono hN hM hN4 hM4 H hAB) hA
  have hbox := torusRCFiberEventProbability_finset_inter_ge_prod hN hM hN4 hM4 q F H I E'
    (fun j => liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) (y j) R (y j) (y (j + 1)))
    hmono (fun _ _ => liftedBoxFreeConnectionProbability_nonneg ..)
    (fun j hj => liftedBoxFreeConnectionProbability_le_free_remaining hN hM hN4 hM4 hNp hMp
      q (y j) R (y (j + 1)) hRN hRM hleft hright (by
        apply sub_pos.mpr
        change (R : ℤ) < 2 * (n : ℤ) * j
        exact_mod_cast (Finset.mem_filter.mp hj).2.1) (by
        change 2 * (n : ℤ) * j + R < (M : ℤ)
        exact_mod_cast (Finset.mem_filter.mp hj).2.2) H)
  have hE : IsUpperSet E := fun _ _ hAB hA j hj => hmono j hAB (hA j hj)
  have hopen := torusRCFiber_allOpen_inter_ge hN hM hN4 hM4 q F H S E hE
  have hcard : S.card ≤ 2 * (R + 2 * n) := by
    rw [rightHalfRetainedSet_card]
    exact columnCollarEdges_card_le hNp hMp x (R + 2 * n)
  have hc0 := (fkOpenEnergy_pos (torusRCBridgeParameters q)).le
  have hcost := pow_le_pow_of_le_one hc0
    (fkOpenEnergy_le_one (torusRCBridgeParameters q)) hcard
  dsimp only [y] at hbox
  simp_rw [liftedBoxFreeConnectionProbability_chain] at hbox
  rw [Finset.prod_const] at hbox
  let P := liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) rotatedLatticeOrigin R
    rotatedLatticeOrigin (rotatedDiagonalSite n)
  have hP : 0 ≤ P := liftedBoxFreeConnectionProbability_nonneg ..
  have hpow : P ^ (M / (2 * n)) ≤ P ^ I.card :=
    pow_le_pow_of_le_one hP (liftedBoxFreeConnectionProbability_le_one ..)
      ((Finset.card_filter_le _ _).trans_eq (Finset.card_range _))
  refine ((mul_le_mul hcost (hpow.trans hbox) (pow_nonneg hP _)
    (pow_nonneg hc0 _)).trans hopen).trans (torusRCFiberEventProbability_mono _ ?_)
  intro A
  rintro ⟨hopenA, hEA⟩
  have hB : rightHalfRestore hN hM hN4 hM4 H A ∈ torusRCBarrier hNp hMp n :=
    (barrier_rightHalfRestore_iff hN hM hN4 hM4 hNp hMp n hnleft H A _).mpr hH
  apply liftedCPrime_of_interior_and_collar hNp hMp _ _ x hx hM n R hn hnR
    hxleft hxright _
  · apply columnCollarOpen_of_barrier_and_edges hNp hMp x (R + 2 * n) n
      hxleft hxright hnleft _ hB
    exact rightHalfRetainedSet_open hN hM hN4 hM4 s hs H A hopenA
  · intro j hj hb ht
    exact hEA j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hb, ht⟩)

end

end PottsDiscontinuity.TorusRC
