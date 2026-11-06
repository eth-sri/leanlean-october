module

public import PottsDiscontinuity.TorusRC.MeasureFacts
public import PottsDiscontinuity.TorusTopology.BarrierEvent

/-! A finite configuration witnessing the exact-one vertical-winding event on
large widths divisible by eight. -/

@[expose] public section

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open Torus TorusRC CorrLength

def exactOneWitnessConfig (N M : ℕ) :
    RCConfig N M := fun e => decide (e.1.val ≠ 1)

private theorem exactOneWitnessConfig_isolatedSeamIndex {N M : ℕ}
    (_hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) :
    ∀ j : Fin M,
      exactOneWitnessConfig N M (⟨1, by omega⟩, j) = false :=
  fun _ => by change decide (1 ≠ 1) = false; simp

private theorem exactOneWitnessConfig_seam_all_but_one {N M : ℕ}
    (_hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hM : 0 < M) :
    TorusRC.torusRCSeamAllButOneOpen hM (exactOneWitnessConfig N M) :=
  ⟨⟨1, by omega⟩, by change decide (1 ≠ 1) = false; simp, fun i hi => by
    change decide (i.val ≠ 1) = true
    exact decide_eq_true_eq.mpr fun h => hi (Fin.ext h)⟩

private theorem exactOneWitnessConfig_noLeftCrossing {N M : ℕ}
    (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hMpos : 0 < M) :
    ¬ TorusRC.torusRCLeftStripCrossing (by omega) hMpos
      (exactOneWitnessConfig N M) 1 := by
  rintro ⟨u, v, hu, hv, ⟨w⟩⟩
  have hNpos : 0 < N := by omega
  cases w with
  | nil => omega
  | @cons _ z _ hadj _ =>
    have hzxabs : |z.val.1| = 1 := by simpa [hu] using hadj.1.1
    have hzx : z.val.1 = 1 := by
      rw [abs_of_nonneg hadj.2.2.2.1] at hzxabs; omega
    have hfirst : (TorusRC.liftedEdgeIndex hNpos hMpos u z).1 = (⟨1, by omega⟩ : Fin N) := by
      apply Fin.ext
      change (TorusRC.periodicCoordinate hNpos (max u.val.1 z.val.1)).val = 1
      rw [hu, hzx, max_eq_right (by norm_num : (0 : ℤ) ≤ 1)]
      exact congrArg Fin.val (TorusTopology.periodicCoordinate_nat hNpos (⟨1, by omega⟩ : Fin N))
    have hclosed := exactOneWitnessConfig_isolatedSeamIndex hNdiv hNlarge
      (TorusRC.liftedEdgeIndex hNpos hMpos u z).2
    rw [← hfirst, Prod.mk.eta] at hclosed
    exact Bool.noConfusion (hclosed.symm.trans hadj.2.1)

private theorem exactOneWitnessConfig_in_CPrime {N M : ℕ}
    (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hMeven : Even M) (hMpos : 0 < M) :
    (exactOneWitnessConfig N M) ∈
      TorusRC.torusCPrime (by omega) hMpos hNdiv hMeven 1 := by
  obtain ⟨kN, hkN⟩ := hNdiv
  have hcolLt : 3 * (N / 4) + 1 < N := by omega
  have hx : TorusRC.sourceRightColumn N = (3 * (N / 4) : ℕ) := rfl
  have hxEven : Even (TorusRC.sourceRightColumn N) := TorusRC.sourceRightColumn_even ⟨kN, hkN⟩
  have hstripLo : (N / 2 : ℤ) ≤ TorusRC.sourceRightColumn N := by
    rw [hx]; exact_mod_cast (show N / 2 ≤ 3 * (N / 4) by omega)
  have hstripHi : TorusRC.sourceRightColumn N + 1 ≤ (N : ℤ) := by
    rw [hx]; exact_mod_cast (show 3 * (N / 4) + 1 ≤ N by omega)
  have hcolumnOpen (j : Fin M) :
      exactOneWitnessConfig N M (⟨3 * (N / 4) + 1, hcolLt⟩, j) = true := by
    change decide (3 * (N / 4) + 1 ≠ 1) = true
    exact decide_eq_true_eq.mpr (by omega)
  have hlocal (j : ℕ) (hj : j < M / 2) :
      TorusRC.liftedBoxConnection (by omega) hMpos (exactOneWitnessConfig N M)
        (N / 2 : ℤ) (N : ℤ) (N / 4)
        (TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 j)
        (TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 (j + 1)) := by
    let t : ℤ := 2 * (j : ℤ)
    let u : RotatedVertex := TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 j
    let v : RotatedVertex := TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 (j + 1)
    let z : RotatedVertex := ⟨(TorusRC.sourceRightColumn N + 1, t + 1), by
      rcases hxEven with ⟨x, hx⟩; exact ⟨x + j + 1, by dsimp [t]; omega⟩⟩
    have hNpos : 0 < N := by omega
    have hcolIndex : TorusRC.periodicCoordinate hNpos (TorusRC.sourceRightColumn N + 1) =
        (⟨3 * (N / 4) + 1, hcolLt⟩ : Fin N) := by
      simpa [TorusRC.sourceRightColumn] using
        TorusTopology.periodicCoordinate_nat hNpos (⟨3 * (N / 4) + 1, hcolLt⟩ : Fin N)
    have hux : u.val.1 = TorusRC.sourceRightColumn N := rfl
    have hzx : z.val.1 = TorusRC.sourceRightColumn N + 1 := rfl
    have hvx : v.val.1 = TorusRC.sourceRightColumn N := rfl
    have huy : u.val.2 = t := by change 2 * (1 : ℤ) * (j : ℤ) = t; simp [t]
    have hzy : z.val.2 = t + 1 := rfl
    have hvy : v.val.2 = t + 2 := by change 2 * (1 : ℤ) * ((j + 1 : ℕ) : ℤ) = t + 2; simp [t]; ring
    have hindex1 : TorusRC.liftedEdgeIndex hNpos hMpos u z =
        (⟨3 * (N / 4) + 1, hcolLt⟩, TorusRC.periodicCoordinate hMpos (t + 1)) :=
      Prod.ext (by
        change TorusRC.periodicCoordinate hNpos (max u.val.1 z.val.1) = _
        rw [hux, hzx, max_eq_right (by omega), hcolIndex])
        (by change TorusRC.periodicCoordinate hMpos (max u.val.2 z.val.2) = _
            rw [huy, hzy, max_eq_right (by omega)])
    have hindex2 : TorusRC.liftedEdgeIndex hNpos hMpos z v =
        (⟨3 * (N / 4) + 1, hcolLt⟩, TorusRC.periodicCoordinate hMpos (t + 2)) :=
      Prod.ext (by
        change TorusRC.periodicCoordinate hNpos (max z.val.1 v.val.1) = _
        rw [hzx, hvx, max_eq_left (by omega), hcolIndex])
        (by change TorusRC.periodicCoordinate hMpos (max z.val.2 v.val.2) = _
            rw [hzy, hvy, max_eq_right (by omega)])
    have hAdj1 : (TorusRC.liftedStripGraph hNpos hMpos (exactOneWitnessConfig N M)
        (N / 2 : ℤ) (N : ℤ)).Adj u z :=
      ⟨by change |u.val.1 - z.val.1| = 1 ∧ |u.val.2 - z.val.2| = 1; rw [hux, hzx, huy, hzy]; norm_num,
        by rw [hindex1]; exact hcolumnOpen _,
        ⟨by rw [hux]; exact hstripLo, by rw [hux]; omega⟩,
        ⟨by rw [hzx]; omega, by rw [hzx]; exact hstripHi⟩⟩
    have hAdj2 : (TorusRC.liftedStripGraph hNpos hMpos (exactOneWitnessConfig N M)
        (N / 2 : ℤ) (N : ℤ)).Adj z v :=
      ⟨by change |z.val.1 - v.val.1| = 1 ∧ |z.val.2 - v.val.2| = 1; rw [hzx, hvx, hzy, hvy]; norm_num,
        by rw [hindex2]; exact hcolumnOpen _,
        ⟨by rw [hzx]; omega, by rw [hzx]; exact hstripHi⟩,
        ⟨by rw [hvx]; exact hstripLo, by rw [hvx]; omega⟩⟩
    refine ⟨SimpleGraph.Walk.cons hAdj1 (SimpleGraph.Walk.cons hAdj2 .nil), ?_⟩
    have hR : 2 ≤ (N / 4 : ℤ) := by exact_mod_cast (show 2 ≤ N / 4 by omega)
    intro w hw
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · simp [TorusRC.inLiftedBox]; positivity
    · change |z.val.1 - u.val.1| ≤ (N / 4 : ℤ) ∧ |z.val.2 - u.val.2| ≤ (N / 4 : ℤ)
      rw [hux, hzx, huy, hzy]; constructor <;> norm_num <;> omega
    · change |v.val.1 - u.val.1| ≤ (N / 4 : ℤ) ∧ |v.val.2 - u.val.2| ≤ (N / 4 : ℤ)
      rw [hux, hvx, huy, hvy]; constructor <;> norm_num <;> omega
  change (exactOneWitnessConfig N M) ∈
    TorusRC.liftedCPrime (by omega) hMpos (N / 2 : ℤ) (N : ℤ)
      (TorusRC.sourceRightColumn N) hxEven hMeven 1 (N / 4)
  simp only [TorusRC.liftedCPrime, Set.mem_ofPred_eq]
  refine ⟨fun j hj => hlocal j (by simpa using hj), ?_⟩
  rw [show M / (2 * 1) = M / 2 by omega,
    show TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 (M / 2) =
      TorusRC.liftedColumnSite (TorusRC.sourceRightColumn N) M hxEven (by exact_mod_cast hMeven) by
    refine Subtype.ext (Prod.ext rfl ?_)
    rcases hMeven with ⟨m, rfl⟩
    change 2 * (1 : ℤ) * (((m + m) / 2 : ℕ) : ℤ) = ((m + m : ℕ) : ℤ)
    omega]
  exact ⟨SimpleGraph.Walk.nil, by simp [TorusRC.inLiftedBox]; positivity⟩

theorem exactOneProbability_pos_of_large_eight_width
    {N M : ℕ} (q : Set.Ici (1 : ℝ)) (hN : Even N) (hM : Even M)
    (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hMpos : 0 < M)
    (hMlarge : N / 2 < M) :
    0 < TorusRC.torusRCProbability hN hM q
      {A | rcVerticalWinding hN hM ⟨0, hMpos⟩ A = 1} :=
  (TorusRC.torusRCProbability_pos_iff hN hM q _).2
    ⟨exactOneWitnessConfig N M,
      TorusTopology.hBCU_proved hN hM (by omega) hMpos hNdiv 1 (by omega) hMlarge _
        ⟨exactOneWitnessConfig_noLeftCrossing hNdiv hNlarge hMpos,
          exactOneWitnessConfig_seam_all_but_one hNdiv hNlarge hMpos⟩
        (exactOneWitnessConfig_in_CPrime hNdiv hNlarge hM hMpos)⟩

end PottsDiscontinuity.RCMProof
