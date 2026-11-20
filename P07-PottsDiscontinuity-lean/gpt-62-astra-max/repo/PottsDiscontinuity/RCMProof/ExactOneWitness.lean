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

section
variable {N M : ℕ} (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hMeven : Even M) (hMpos : 0 < M)
include hNdiv hNlarge

private theorem exactOneWitnessConfig_isolatedSeamIndex :
    ∀ j : Fin M,
      exactOneWitnessConfig N M (⟨1, by omega⟩, j) = false := by
  intro j
  rfl

private theorem exactOneWitnessConfig_seam_all_but_one (hM : 0 < M) :
    TorusRC.torusRCSeamAllButOneOpen hM (exactOneWitnessConfig N M) := by
  refine ⟨⟨1, by omega⟩, ?_, ?_⟩
  · rfl
  · intro i hi
    change decide (i.val ≠ 1) = true
    grind

private theorem exactOneWitnessConfig_noLeftCrossing :
    ¬ TorusRC.torusRCLeftStripCrossing (by omega) hMpos
      (exactOneWitnessConfig N M) 1 := by
  intro hcross
  rcases hcross with ⟨u, v, hu, hv, hreach⟩
  have hNpos : 0 < N := by omega
  have hisolated (z : RotatedVertex) (hz : (TorusRC.liftedStripGraph hNpos hMpos (exactOneWitnessConfig N M) 0 3).Adj u z) : False := by
    have hzxnonneg := hz.2.2.2.1
    have hzxabs : |z.val.1| = 1 := by
      simpa [hu] using hz.1.1
    have hzx : z.val.1 = 1 := by
      grind
    have hfirst : (TorusRC.liftedEdgeIndex hNpos hMpos u z).1 =
        ⟨1, by omega⟩ := by
      apply Fin.ext
      change (TorusRC.periodicCoordinate hNpos (max u.val.1 z.val.1)).val = 1
      rw [hu, hzx, max_eq_right (by norm_num)]
      exact congrArg Fin.val
        (TorusTopology.periodicCoordinate_nat hNpos ⟨1, by omega⟩)
    grind [exactOneWitnessConfig_isolatedSeamIndex, hz.2]
  rcases hreach with ⟨w⟩
  cases w with
  | nil => omega
  | cons hadj _ => grind

private theorem exactOneWitnessConfig_in_CPrime :
    (exactOneWitnessConfig N M) ∈
      TorusRC.torusCPrime (by omega) hMpos hNdiv hMeven 1 := by
  have hNdivCopy := hNdiv
  obtain ⟨kN, hkN⟩ := hNdivCopy
  have hcolLt : 3 * (N / 4) + 1 < N := by omega
  have hx : TorusRC.sourceRightColumn N = (3 * (N / 4)) := rfl
  have hxEven :=
    TorusRC.sourceRightColumn_even hNdiv
  have hcolumnOpen (j : Fin M) :
      exactOneWitnessConfig N M
        (⟨3 * (N / 4) + 1, hcolLt⟩, j) = true := by
    change decide (3 * (N / 4) + 1 ≠ 1) = true
    grind
  have hlocal (j : ℕ) (hj : j < M / 2) :
      TorusRC.liftedBoxConnection (by omega) hMpos (exactOneWitnessConfig N M)
        (N / 2 : ℤ) (N : ℤ) (N / 4)
        (TorusRC.liftedChainSite hxEven 1 j)
        (TorusRC.liftedChainSite hxEven 1 (j + 1)) := by
    let t := 2 * (j : ℤ)
    let u := TorusRC.liftedChainSite hxEven 1 j
    let v := TorusRC.liftedChainSite hxEven 1 (j + 1)
    let z : RotatedVertex := ⟨(TorusRC.sourceRightColumn N + 1, t + 1), by
      grind⟩
    have hNpos : 0 < N := by omega
    have hcolIndex : TorusRC.periodicCoordinate hNpos
        (TorusRC.sourceRightColumn N + 1) =
          ⟨3 * (N / 4) + 1, hcolLt⟩ := by
      have hp := TorusTopology.periodicCoordinate_nat hNpos
        (⟨3 * (N / 4) + 1, hcolLt⟩ : Fin N)
      assumption
    have hux : u.val.1 = TorusRC.sourceRightColumn N := rfl
    have hzx : z.val.1 = TorusRC.sourceRightColumn N + 1 := rfl
    have hvx : v.val.1 = TorusRC.sourceRightColumn N := rfl
    have huy : u.val.2 = t := rfl
    have hzy : z.val.2 = t + 1 := rfl
    have hvy : v.val.2 = t + 2 := rfl
    have hindex1 : TorusRC.liftedEdgeIndex hNpos hMpos u z =
        (⟨3 * (N / 4) + 1, hcolLt⟩,
          TorusRC.periodicCoordinate hMpos (t + 1)) := by
      apply Prod.ext
      · apply Fin.ext
        change (TorusRC.periodicCoordinate hNpos (max u.val.1 z.val.1)).val = _
        grind
      · change TorusRC.periodicCoordinate hMpos (max u.val.2 z.val.2) = _
        simp [*]
    have hindex2 : TorusRC.liftedEdgeIndex hNpos hMpos z v =
        (⟨3 * (N / 4) + 1, hcolLt⟩,
          TorusRC.periodicCoordinate hMpos (t + 2)) := by
      apply Prod.ext
      · apply Fin.ext
        change (TorusRC.periodicCoordinate hNpos (max z.val.1 v.val.1)).val = _
        grind
      · change TorusRC.periodicCoordinate hMpos (max z.val.2 v.val.2) = _
        simp [*]
    have hAdj1 :
        (TorusRC.liftedStripGraph hNpos hMpos (exactOneWitnessConfig N M)
          (N / 2 : ℤ) (N : ℤ)).Adj u z := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · change |u.val.1 - z.val.1| = 1 ∧ |u.val.2 - z.val.2| = 1
        simp [hux, hzx, huy, hzy]
      · grind
      · omega
      · omega
    have hAdj2 :
        (TorusRC.liftedStripGraph hNpos hMpos (exactOneWitnessConfig N M)
          (N / 2 : ℤ) (N : ℤ)).Adj z v := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · change |z.val.1 - v.val.1| = 1 ∧ |z.val.2 - v.val.2| = 1
        simp [hzx, hvx, hzy, hvy]
      · grind
      · omega
      · omega
    refine ⟨SimpleGraph.Walk.cons hAdj1 (SimpleGraph.Walk.cons hAdj2 .nil), ?_⟩
    have hboxZ : TorusRC.inLiftedBox (N / 4) u z := by
      change _ ∧
        _
      grind
    have hboxV : TorusRC.inLiftedBox (N / 4) u v := by
      change _ ∧
        _
      rw [hux, hvx, huy, hvy]
      constructor <;> norm_num <;> omega
    intro w hw
    simp at hw
    rcases hw with rfl | rfl | rfl
    · exact (by
      simp [TorusRC.inLiftedBox]
      positivity)
    · exact hboxZ
    · exact hboxV
  change _ ∈
    _
  refine ⟨?_, ?_⟩
  · assumption
  · have hk : M / (2 * 1) = M / 2 := by omega
    have hy : TorusRC.liftedChainSite (x := (TorusRC.sourceRightColumn N)) hxEven 1 (M / 2) =
        TorusRC.liftedColumnSite (x := (TorusRC.sourceRightColumn N)) (t := M) hxEven
          (by exact_mod_cast hMeven) := by
      apply Subtype.ext
      change (TorusRC.sourceRightColumn N, 2 * (1 : ℤ) * (M / 2 : ℕ)) =
        (TorusRC.sourceRightColumn N, (M : ℤ))
      grind
    rw [hk, hy]
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    simp [TorusRC.inLiftedBox]
    positivity

end

theorem exactOneProbability_pos_of_large_eight_width
    {N M : ℕ} (q : Set.Ici 1) (hN : Even N) (hM : Even M)
    (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hMpos : 0 < M)
    (hMlarge : N / 2 < M) :
    0 < TorusRC.torusRCProbability hN hM q
      {A | rcVerticalWinding hN hM ⟨0, hMpos⟩ A = 1} := by
  have hNpos : 0 < N := by omega
  have hU := TorusTopology.hBCU_proved hN hM hNpos hMpos hNdiv 1
    (by omega) hMlarge _ (by
      refine ⟨exactOneWitnessConfig_noLeftCrossing hNdiv hNlarge hMpos, ?_⟩
      exact exactOneWitnessConfig_seam_all_but_one hNdiv hNlarge hMpos) (exactOneWitnessConfig_in_CPrime hNdiv hNlarge hM hMpos)
  apply (TorusRC.torusRCProbability_pos_iff hN hM q _).2
  exact ⟨exactOneWitnessConfig N M, hU⟩

end PottsDiscontinuity.RCMProof
