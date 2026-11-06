module

public import PottsDiscontinuity.TorusRC.MeasureFacts
public import PottsDiscontinuity.TorusTopology.BarrierEvent

/-! A finite configuration witnessing the exact-one vertical-winding event on
large widths divisible by eight. -/

public section

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open Torus TorusRC CorrLength

def exactOneWitnessConfig (N M : ℕ) :
    RCConfig N M := fun e => decide (e.1.val ≠ 1)

section
variable {N M : ℕ} (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N)
include hNdiv hNlarge
theorem exactOneWitnessConfig_isolatedSeamIndex  :
    ∀ j : Fin M,
      exactOneWitnessConfig N M (⟨1, by omega⟩, j) = false := by
  tauto

theorem exactOneWitnessConfig_seam_all_but_one (hM : 0 < M) :
    TorusRC.torusRCSeamAllButOneOpen hM (exactOneWitnessConfig N M) := by
  refine ⟨⟨1, by omega⟩, ?_, ?_⟩
  · rfl
  · intro i hi
    have hi' : i.val ≠ 1 := by grind
    change decide (i.val ≠ 1) = true
    simp_all

theorem exactOneWitnessConfig_noLeftCrossing (hMpos : 0 < M) :
    ¬ TorusRC.torusRCLeftStripCrossing (by omega) hMpos
      (exactOneWitnessConfig N M) 1 := by
  intro hcross
  rcases hcross with ⟨u, v, hu, hv, hreach⟩
  have hNpos : 0 < N := by omega
  let G := TorusRC.liftedStripGraph hNpos hMpos
    (exactOneWitnessConfig N M) 0 3
  have hisolated (z : RotatedVertex) (hz : G.Adj u z) : False := by
    have hzxnonneg := hz.2.2.2.1
    have hzxabs : |z.val.1| = 1 := by
      simpa [hu] using hz.1.1
    have hzx : z.val.1 = 1 := by
      grind
    have hfirst : (TorusRC.liftedEdgeIndex hNpos hMpos u z).1 =
        (⟨1, by omega⟩ : Fin N) := by
      apply Fin.ext
      change (TorusRC.periodicCoordinate hNpos (max u.val.1 z.val.1)).val = 1
      rw [hu, hzx, max_eq_right (by norm_num : (0 : ℤ) ≤ 1)]
      exact congrArg Fin.val
        (TorusTopology.periodicCoordinate_nat hNpos (⟨1, by omega⟩ : Fin N))
    have hclosed := exactOneWitnessConfig_isolatedSeamIndex hNdiv hNlarge
      (TorusRC.liftedEdgeIndex hNpos hMpos u z).2
    have hopen := hz.2.1
    grind
  rcases hreach with ⟨w⟩
  cases w with
  | nil => omega
  | cons hadj _ => grind

theorem exactOneWitnessConfig_in_CPrime (hMeven : Even M) (hMpos : 0 < M) :
    (exactOneWitnessConfig N M) ∈
      TorusRC.torusCPrime (by omega) hMpos hNdiv hMeven 1 := by
  have hNdivCopy := hNdiv
  obtain ⟨kN, hkN⟩ := hNdivCopy
  have hkNpos : 1 ≤ kN := by omega
  have hNformula := hkN
  have hcol : 3 * (N / 4) = 6 * kN := by omega
  have hcolLt : 3 * (N / 4) + 1 < N := by omega
  have hx : TorusRC.sourceRightColumn N = (3 * (N / 4) : ℕ) := rfl
  have hxEven :=
    TorusRC.sourceRightColumn_even hNdiv
  have hstripLo : (N / 2 : ℤ) ≤ TorusRC.sourceRightColumn N := by
    omega
  have hstripHi : TorusRC.sourceRightColumn N + 1 ≤ (N : ℤ) := by
    omega
  have hcolumnOpen (j : Fin M) :
      exactOneWitnessConfig N M
        (⟨3 * (N / 4) + 1, hcolLt⟩, j) = true := by
    change decide (3 * (N / 4) + 1 ≠ 1) = true
    grind
  have hlocal (j : ℕ) (hj : j < M / 2) :
      TorusRC.liftedBoxConnection (by omega) hMpos (exactOneWitnessConfig N M)
        (N / 2 : ℤ) (N : ℤ) (N / 4)
        (TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 j)
        (TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 (j + 1)) := by
    let t : ℤ := 2 * (j : ℤ)
    let u : RotatedVertex := TorusRC.liftedChainSite
      (TorusRC.sourceRightColumn N) hxEven 1 j
    let v : RotatedVertex := TorusRC.liftedChainSite
      (TorusRC.sourceRightColumn N) hxEven 1 (j + 1)
    let z : RotatedVertex := ⟨(TorusRC.sourceRightColumn N + 1, t + 1), by
      grind⟩
    have hNpos : 0 < N := by omega
    have hcolIndex : TorusRC.periodicCoordinate hNpos
        (TorusRC.sourceRightColumn N + 1) =
          (⟨3 * (N / 4) + 1, hcolLt⟩ : Fin N) := by
      have hp := TorusTopology.periodicCoordinate_nat hNpos
        (⟨3 * (N / 4) + 1, hcolLt⟩ : Fin N)
      grind
    have hux : u.val.1 = TorusRC.sourceRightColumn N := by rfl
    have hzx : z.val.1 = TorusRC.sourceRightColumn N + 1 := by rfl
    have hvx : v.val.1 = TorusRC.sourceRightColumn N := by rfl
    have huy : u.val.2 = t := by
      rfl
    have hvy : v.val.2 = t + 2 := by
      rfl
    have hindex1 : TorusRC.liftedEdgeIndex hNpos hMpos u z =
        (⟨3 * (N / 4) + 1, hcolLt⟩,
          TorusRC.periodicCoordinate hMpos (t + 1)) := by
      apply Prod.ext
      · apply Fin.ext
        change (TorusRC.periodicCoordinate hNpos (max u.val.1 z.val.1)).val = _
        grind
      · change TorusRC.periodicCoordinate hMpos (max u.val.2 z.val.2) = _
        grind
    have hindex2 : TorusRC.liftedEdgeIndex hNpos hMpos z v =
        (⟨3 * (N / 4) + 1, hcolLt⟩,
          TorusRC.periodicCoordinate hMpos (t + 2)) := by
      apply Prod.ext
      · apply Fin.ext
        change (TorusRC.periodicCoordinate hNpos (max z.val.1 v.val.1)).val = _
        grind
      · change TorusRC.periodicCoordinate hMpos (max z.val.2 v.val.2) = _
        grind
    have hAdj1 :
        (TorusRC.liftedStripGraph hNpos hMpos (exactOneWitnessConfig N M)
          (N / 2 : ℤ) (N : ℤ)).Adj u z := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · change |u.val.1 - z.val.1| = 1 ∧ |u.val.2 - z.val.2| = 1
        grind
      · grind
      · omega
      omega
    have hAdj2 :
        (TorusRC.liftedStripGraph hNpos hMpos (exactOneWitnessConfig N M)
          (N / 2 : ℤ) (N : ℤ)).Adj z v := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · change |z.val.1 - v.val.1| = 1 ∧ |z.val.2 - v.val.2| = 1
        grind
      · grind
      · omega
      omega
    refine ⟨SimpleGraph.Walk.cons hAdj1 (SimpleGraph.Walk.cons hAdj2 .nil), ?_⟩
    have hR : 2 ≤ (N / 4 : ℤ) := by
      omega
    have hboxU : TorusRC.inLiftedBox (N / 4) u u := by
      grind [TorusRC.inLiftedBox]
    have hboxZ : TorusRC.inLiftedBox (N / 4) u z := by
      change |z.val.1 - u.val.1| ≤ (N / 4 : ℤ) ∧
        |z.val.2 - u.val.2| ≤ (N / 4 : ℤ)
      grind
    have hboxV : TorusRC.inLiftedBox (N / 4) u v := by
      change |v.val.1 - u.val.1| ≤ (N / 4 : ℤ) ∧
        |v.val.2 - u.val.2| ≤ (N / 4 : ℤ)
      grind
    intro w hw
    simp at hw
    grind
  refine ⟨?_, ?_⟩
  · tauto
  · have hk : M / (2 * 1) = M / 2 := by omega
    have hy : TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 (M / 2) =
        TorusRC.liftedColumnSite (TorusRC.sourceRightColumn N) M hxEven
          (by grind) := by
      apply Subtype.ext
      change (TorusRC.sourceRightColumn N, 2 * (1 : ℤ) * ((M / 2 : ℕ) : ℤ)) =
        (TorusRC.sourceRightColumn N, (M : ℤ))
      grind
    rw [hk, hy]
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    simp [TorusRC.inLiftedBox]
    positivity
end

theorem exactOneProbability_pos_of_large_eight_width
    {N M : ℕ} (q : Set.Ici (1 : ℝ)) (hN : Even N) (hM : Even M)
    (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hMpos : 0 < M)
    (hMlarge : N / 2 < M) :
    0 < TorusRC.torusRCProbability hN hM q
      {A | rcVerticalWinding hN hM ⟨0, hMpos⟩ A = 1} := by
  have hNpos : 0 < N := by omega
  have hB : exactOneWitnessConfig N M ∈ TorusRC.torusRCBarrier hNpos hMpos 1 := by
    refine ⟨exactOneWitnessConfig_noLeftCrossing hNdiv hNlarge hMpos, ?_⟩
    simp_all [exactOneWitnessConfig_seam_all_but_one]
  have hU := TorusTopology.hBCU_proved hN hM hNpos hMpos hNdiv 1
    (by omega) hMlarge _ hB (exactOneWitnessConfig_in_CPrime hNdiv hNlarge hM hMpos)
  apply (TorusRC.torusRCProbability_pos_iff hN hM q _).2
  exact ⟨exactOneWitnessConfig N M, hU⟩

end PottsDiscontinuity.RCMProof
