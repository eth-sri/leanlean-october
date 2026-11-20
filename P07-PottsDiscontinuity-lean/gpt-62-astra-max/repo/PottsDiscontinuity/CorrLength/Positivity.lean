module

public import PottsDiscontinuity.CorrLength.ConnectionEvents
public import PottsDiscontinuity.FK.Events

/-!
# Positive probability of finite-distance connection

Every pair of square-lattice vertices has a deterministic finite path. The
event that all of its edges are open has positive probability in a sufficiently
large finite free box, and hence in the canonical free limit.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.CorrLength

open PottsDiscontinuity.FK

noncomputable section

private theorem squareLattice_reachable_origin_posX (n : ℕ) :
    squareLattice.Reachable (0, 0) (n, 0) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      have hadj : squareLattice.Adj (n, 0) ((n + 1), 0) := by
        simp_all [squareLattice_adj_iff]
      exact ih.trans hadj.reachable

private theorem squareLattice_reachable_origin_negX (n : ℕ) :
    squareLattice.Reachable (0, 0) (-n, 0) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      have hadj : squareLattice.Adj (-n, 0) (-(n + 1), 0) := by
        simp_all [squareLattice_adj_iff]
      exact ih.trans hadj.reachable

private theorem squareLattice_reachable_origin_posY (n : ℕ) :
    squareLattice.Reachable (0, 0) (0, n) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      have hadj : squareLattice.Adj (0, n) (0, (n + 1)) := by
        simp_all [squareLattice_adj_iff]
      exact ih.trans hadj.reachable

private theorem squareLattice_reachable_origin_negY (n : ℕ) :
    squareLattice.Reachable (0, 0) (0, -n) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      have hadj : squareLattice.Adj (0, -n) (0, -(n + 1)) := by
        simp_all [squareLattice_adj_iff]
      exact ih.trans hadj.reachable

private theorem squareLattice_reachable_origin_x (a : ℤ) :
    squareLattice.Reachable (0, 0) (a, 0) := by
  cases a with
  | ofNat n => exact squareLattice_reachable_origin_posX n
  | negSucc n =>
      rw [Int.negSucc_eq]
      convert squareLattice_reachable_origin_negX (n + 1) using 1
      push_cast; ring

private theorem squareLattice_reachable_origin_y (b : ℤ) :
    squareLattice.Reachable (0, 0) (0, b) := by
  cases b with
  | ofNat n => exact squareLattice_reachable_origin_posY n
  | negSucc n =>
      rw [Int.negSucc_eq]
      convert squareLattice_reachable_origin_negY (n + 1) using 1
      push_cast; ring

private theorem squareLattice_reachable_all (u v : LatticeVertex) :
    squareLattice.Reachable u v := by
  let d := (v.1 - u.1, v.2 - u.2)
  have hy' : squareLattice.Reachable (d.1, 0) (d.1, d.2) := by
    have h := (SimpleGraph.Iso.reachable_iff
      (φ := latticeTranslationIso (d.1, 0))).mpr (squareLattice_reachable_origin_y d.2)
    simpa [d, latticeTranslationIso, latticeTranslate] using h
  have h' : squareLattice.Reachable (latticeTranslate u (0, 0))
      (latticeTranslate u d) := (SimpleGraph.Iso.reachable_iff
      (φ := latticeTranslationIso u)).mpr ((squareLattice_reachable_origin_x d.1).trans hy')
  simpa [d, latticeTranslate] using h'

private theorem squareLattice_reachable_finite_actualConnected {u v : LatticeVertex}
    (h : squareLattice.Reachable u v) :
    ∃ F, ActualConnected (G := squareLattice) F u v := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact ⟨∅, by simp⟩
  | @cons u v w huv tail ih =>
      obtain ⟨F, hF⟩ := ih
      let e : squareLattice.edgeSet := ⟨s(u, v), squareLattice.mem_edgeSet.mpr huv⟩
      refine ⟨insert e F, ?_⟩
      have hfirst : ActualConnected (insert e F) u v := by
        have hAdj : (openGraph (insert e F)).Adj u v := by
          apply (openGraph_adj _ u v).mpr
          exact ⟨e, by simp, rfl⟩
        exact hAdj.reachable
      exact hfirst.trans (actualConnected_mono (Finset.subset_insert e F) hF)

private theorem exists_finite_connection_witness (u v : LatticeVertex) :
    ∃ F, ActualConnected (G := squareLattice) F u v :=
  squareLattice_reachable_finite_actualConnected (squareLattice_reachable_all u v)

private theorem eventually_edge_lift_origin_boxGraph (e : squareLattice.edgeSet) :
    ∀ᶠ n : ℕ in atTop, ∃ f : (boxGraph (0, 0) n).edgeSet,
      Sym2.map Subtype.val f.1 = e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      filter_upwards [eventually_mem_box x, eventually_mem_box y] with n hx hy
      let u : BoxVertex (0, 0) n := ⟨x, (by
        grind [latticeBox_origin_eq_box])⟩
      let v : BoxVertex (0, 0) n := ⟨y, (by
        grind [latticeBox_origin_eq_box])⟩
      refine ⟨⟨s(u, v), ((boxGraph _ n).mem_edgeSet.mpr (by assumption))⟩, ?_⟩
      rfl

private theorem freeBoxLimit_allOpen_pos (θ : Parameters)
    (F : Finset squareLattice.edgeSet) :
    Classical.choose (freeBoxLimit_existsUnique θ) (LatticeConfiguration.allOpen F) > 0 := by
  let law := boxProbabilityMeasure θ (0, 0)
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((eventually_all_finset F).2 fun e _ => eventually_edge_lift_origin_boxGraph e)
  have hbox : 0 < ((law N : Measure LatticeConfiguration)
      (LatticeConfiguration.allOpen F)) := by
    rw [boxProbabilityMeasure_allOpen]
    exact (measure_pos_iff _ θ _ _).2 (by
      refine ⟨Finset.univ, ?_⟩
      intro e he
      let ex := hN N le_rfl e he
      let f := Classical.choose ex
      apply Finset.mem_map.mpr
      refine ⟨f, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      exact (Classical.choose_spec ex))
  have hmono (n : ℕ) (hn : N ≤ n) :
      law N (LatticeConfiguration.allOpen F) ≤
        law n (LatticeConfiguration.allOpen F) := by
    have h := boxProbabilityMeasure_allOpen_mono θ _ _ N n
      (latticeBox_mono (0, 0) hn) F
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
    exact ENNReal.coe_le_coe.mp h
  have hlimit :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (LatticeConfiguration.tendsto_allOpen_of_weak ((Classical.choose_spec (freeBoxLimit_existsUnique θ)).1 (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive) F)
      (Filter.eventually_atTop.2 ⟨N, fun n hn => hmono n hn⟩)
  exact lt_of_lt_of_le (by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hbox
    exact ENNReal.coe_pos.mp hbox) hlimit

/-- Every fixed finite-distance connection has strictly positive probability
under the canonical free box limit. -/
theorem freeBoxLimit_connection_positive (θ : Parameters) (u v : LatticeVertex) :
    (Classical.choose (freeBoxLimit_existsUnique θ)).toMeasure.real (connectionEvent u v) > 0 := by
  obtain ⟨F, hF⟩ := exists_finite_connection_witness u v
  have hsubset : LatticeConfiguration.allOpen F ⊆ connectionEvent u v := by
    intro ω hω
    exact ⟨F, hF, hω⟩
  let ν :=
    Classical.choose (freeBoxLimit_existsUnique θ)
  have hbox := freeBoxLimit_allOpen_pos θ F
  exact ENNReal.toReal_pos (ne_of_gt (by
    have hleft : 0 < ν.toMeasure (LatticeConfiguration.allOpen F) := by
      rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact by positivity
    exact lt_of_lt_of_le hleft (measure_mono (μ := ν.toMeasure) hsubset))) (measure_ne_top _ _)

/-- Every free infinite-volume limit has strictly positive probability of a
finite-distance connection. -/
theorem isRCInfiniteVolumeLimit_connection_positive {θ : Parameters}
    (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) (u v : LatticeVertex) :
    μ.real (connectionEvent u v) > 0 := by
  rw [(PottsDiscontinuity.rc_limit_unique hμ (isRCInfiniteVolumeLimit_of_freeBox_tendsto ((Classical.choose_spec (freeBoxLimit_existsUnique θ)).1 (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive)))]
  exact freeBoxLimit_connection_positive θ u v

end

end PottsDiscontinuity.CorrLength
