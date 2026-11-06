module

public import PottsDiscontinuity.TorusLoops.LoopTailRectangleFK
public import PottsDiscontinuity.TorusLoops.RectangleExplorationProductBound

/-!
# Union bound over disjoint horizontal crossings

The crossing count is covered by root-set events. Each fixed root set is
estimated by the exploration product bound, and the number of possible root
sets is at most exponential in the height of the rectangle.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK
open PottsDiscontinuity.Zhang

open scoped Classical

variable {N M : ℕ}

noncomputable section

local instance rectangleUnionEdgeFintype (hN : Even N) (hM : Even M) :
    Fintype (rectangleBaseGraph hN hM).edgeSet := Fintype.ofFinite _

local instance rectangleUnionEdgeDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (rectangleBaseGraph hN hM).edgeSet := Classical.decEq _

/-- Left-boundary face vertices of the cut rectangle. -/
abbrev RectangleLeftRoot (N M : ℕ) :=
  {u : FaceVertex N M true // u.val.1.val = 0}

/-- The distinct-root crossing event indexed by a finite set of left roots. -/
def rectangleLeftRootSetEvent (hN : Even N) (hM : Even M)
    (S : Finset (RectangleLeftRoot N M)) :
    Set (Configuration (rectangleBaseGraph hN hM)) :=
  rectangleDistinctRootCrossingEvent hN hM (S.toList.map Subtype.val)

private theorem rectangleCutGraph_eq_fullDiamondGraph_closedOnSeams
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    rectangleOpenGraph hN hM A = diamondOpenGraph hN hM true A := by
  ext u w
  rw [rectangleOpenGraph, diamondOpenGraph, SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
  exact ⟨by rintro ⟨⟨v, hv, _, _, hp⟩, hne⟩; exact ⟨⟨v, hv, hp⟩, hne⟩,
    by rintro ⟨⟨v, hv, hp⟩, hne⟩
       exact ⟨⟨v, hv, fun hz => by rw [hclosed v (Or.inl hz)] at hv; contradiction,
         fun hz => by rw [hclosed v (Or.inr hz)] at hv; contradiction, hp⟩, hne⟩⟩

theorem rectangleFKCrossingEvent_exists_rootSet
    (hN : Even N) (hM : Even M)
    (k : ℕ) (C : Configuration (rectangleBaseGraph hN hM))
    (hC : C ∈ rectangleFKCrossingEvent hN hM k) :
    ∃ S : Finset (RectangleLeftRoot N M), S.card = k ∧
      C ∈ rectangleLeftRootSetEvent hN hM S := by
  classical
  let A := rectangleRCConfigOfConfiguration hN hM C
  let R := rectangleOpenGraph hN hM A
  let K := rectangleCrossingComponents hN hM A
  obtain ⟨T, hTK, hTcard⟩ := Finset.exists_subset_card_eq (hC : k ≤ K.card)
  have hclosed := rectangleRCConfigOfConfiguration_closedOnSeams hN hM C
  have hgraph : R = FK.openGraph (rectangleBaseGraph hN hM) C := by
    change rectangleOpenGraph hN hM A = FK.openGraph (rectangleBaseGraph hN hM) C
    rw [rectangleCutGraph_eq_fullDiamondGraph_closedOnSeams hN hM A hclosed,
      ← rectangleConfigurationOfRC_rectangleRCConfigOfConfiguration hN hM C]
    exact (rectangleOpenGraph_eq_diamondOpenGraph_closedOnSeams hN hM A hclosed).symm
  have witness (c : R.ConnectedComponent) (hc : c ∈ T) :
      ∃ x : RectangleLeftRoot N M, ∃ y : FaceVertex N M true,
        y.val.1.val + 1 = N ∧ R.connectedComponentMk x.val = c ∧ R.Reachable x.val y := by
    rcases Finset.mem_filter.mp (hTK hc) with ⟨_, x, y, hx, hy, hxc, hreach⟩
    exact ⟨⟨x, hx⟩, y, hy, hxc, hreach⟩
  let chosen (c : R.ConnectedComponent) (hc : c ∈ T) : RectangleLeftRoot N M :=
    Classical.choose (witness c hc)
  have chosen_data (c : R.ConnectedComponent) (hc : c ∈ T) :=
    Classical.choose_spec (witness c hc)
  let S : Finset (RectangleLeftRoot N M) := T.attach.image fun c => chosen c.val c.property
  have hchosen_inj : ∀ a ∈ T.attach, ∀ b ∈ T.attach,
      chosen a.val a.property = chosen b.val b.property → a = b := fun a _ b _ hab =>
    Subtype.ext <| (Classical.choose_spec (chosen_data a.val a.property)).2.1.symm.trans <|
      (congrArg (fun z : RectangleLeftRoot N M => R.connectedComponentMk z.val) hab).trans
        (Classical.choose_spec (chosen_data b.val b.property)).2.1
  refine ⟨S, by rw [Finset.card_image_iff.mpr hchosen_inj, Finset.card_attach, hTcard],
    ?_, (Finset.nodup_toList S).map Subtype.val_injective, ?_⟩
  · intro x hx
    rcases List.mem_map.mp hx with ⟨xr, hxr, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_toList.mp hxr) with ⟨c, _, hcx⟩
    obtain ⟨y, hy, _, hreach⟩ := chosen_data c.val c.property
    refine ⟨y, hy, ?_⟩
    change (FK.openGraph (rectangleBaseGraph hN hM) C).Reachable (↑xr) y
    rwa [← hgraph, ← hcx]
  · intro x hx y hy hxy hconn
    rcases List.mem_map.mp hx with ⟨xr, hxr, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_toList.mp hxr) with ⟨c, _, hcx⟩
    rcases List.mem_map.mp hy with ⟨yr, hyr, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_toList.mp hyr) with ⟨d, _, hdy⟩
    obtain ⟨_, _, hcc, _⟩ := chosen_data c.val c.property
    obtain ⟨_, _, hdd, _⟩ := chosen_data d.val d.property
    have hreach : R.Reachable (chosen c.val c.property).val (chosen d.val d.property).val := by
      rw [hgraph, hcx, hdy]; exact hconn
    have hcd : c = d := Subtype.ext (hcc.symm.trans ((SimpleGraph.ConnectedComponent.sound hreach).trans hdd))
    subst d
    exact hxy (congrArg Subtype.val (hcx.symm.trans hdy))

theorem rectangleLeftRoot_card_le (N M : ℕ) :
    Fintype.card (RectangleLeftRoot N M) ≤ M := by
  classical
  refine (Fintype.card_le_of_injective (fun u : RectangleLeftRoot N M => u.val.val.2) ?_).trans_eq
    (Fintype.card_fin M)
  intro a b hab
  exact Subtype.ext (Subtype.ext (Prod.ext (Fin.ext (a.property.trans b.property.symm)) hab))

private theorem rectangleFKEventProbability_eq_measure
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (Configuration (rectangleBaseGraph hN hM))) :
    rectangleFKEventProbability hN hM q E =
      (measure (rectangleBaseGraph hN hM) (rectangleFKParameters q)
        (BoundaryCondition.free ∅) E).toReal := by
  rw [measure_toReal_eq_indicator_sum]
  unfold rectangleFKEventProbability rectangleFKEventWeight
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun C _ => by
    by_cases h : C ∈ E <;> simp [Set.indicator, h, configurationProbability, mul_comm]

theorem rectangleFKCrossingEvent_probability_le_rootUnion
    (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (k : ℕ) :
    rectangleFKEventProbability hN hM q (rectangleFKCrossingEvent hN hM k) ≤
      (2 : ℝ) ^ M *
        rectangleFreeOneArmProbability q (N / 2 - 1) ^ k := by
  classical
  let Left := RectangleLeftRoot N M
  let I := {S : Finset Left // S.card = k}
  let event : I → Set (Configuration (rectangleBaseGraph hN hM)) :=
    fun S => rectangleLeftRootSetEvent hN hM S.val
  let μ := measure (rectangleBaseGraph hN hM) (rectangleFKParameters q)
    (BoundaryCondition.free ∅)
  let ρ := rectangleFreeOneArmProbability q (N / 2 - 1)
  have hcardI : Fintype.card I ≤ 2 ^ M :=
    (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans <|
      Fintype.card_finset.trans_le (Nat.pow_le_pow_right (by omega) (rectangleLeftRoot_card_le N M))
  have hsubset : rectangleFKCrossingEvent hN hM k ⊆ ⋃ S : I, event S := fun C hC => by
    obtain ⟨S, hSk, hCS⟩ := rectangleFKCrossingEvent_exists_rootSet hN hM k C hC
    exact Set.mem_iUnion.mpr ⟨⟨S, hSk⟩, hCS⟩
  have hprobS (S : I) : rectangleBaseEventProbability hN hM q (event S) ≤ ρ ^ k := by
    let roots := S.val.toList.map Subtype.val
    have hleft : ∀ u ∈ roots, u.val.1.val = 0 := by
      rintro u hu; rcases List.mem_map.mp hu with ⟨r, _, rfl⟩; exact r.property
    simpa [event, rectangleLeftRootSetEvent, roots, S.property, ρ] using
      rectangleDistinctRootCrossingEvent_probability_le_pow hN hM q roots hleft
  have hsum : (∑ S : I, μ.real (event S)) ≤ (Fintype.card I : ℝ) * ρ ^ k := by
    calc (∑ S : I, μ.real (event S))
      _ ≤ ∑ _S : I, ρ ^ k := Finset.sum_le_sum fun S _ => by
          simpa [μ, Measure.real, rectangleBaseEventProbability] using hprobS S
      _ = (Fintype.card I : ℝ) * ρ ^ k := by simp
  have hcardR : (Fintype.card I : ℝ) ≤ (2 : ℝ) ^ M := by exact_mod_cast hcardI
  have hρ : 0 ≤ ρ := by simp [ρ, rectangleFreeOneArmProbability]
  rw [rectangleFKEventProbability_eq_measure hN hM q]
  simpa [μ, Measure.real] using
    (measureReal_mono hsubset).trans ((measureReal_iUnion_fintype_le event).trans
      (hsum.trans (mul_le_mul_of_nonneg_right hcardR (pow_nonneg hρ k))))

end

end PottsDiscontinuity.TorusLoops
