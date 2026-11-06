module

public import Mathlib

/-!
# Homeomorphisms of compact convex sets

Compact convex sets are reduced to unit balls in their affine spans and then to
finite-dimensional cubes. These homeomorphisms transfer the cubical fixed-point
theorem to arbitrary nonempty compact convex domains.
-/

@[expose] public section

lemma homeo_unit_ball {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s)
    (hni : (interior s).Nonempty):
    Nonempty (s ≃ₜ Metric.closedBall (0: V) 1) := by {
  
  
  cases  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcvx hni) (IsCompact.isBounded hcmpct) 
  rename_i e he
  
  have e2 := Homeomorph.image e s
  rw [ closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcmpct) ] at he
  rw [he.2.1] at e2
  exact Nonempty.intro e2
}

theorem homeo_of_finrank_eq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hreq : Module.finrank ℝ V = Module.finrank ℝ W) :
    Nonempty (Metric.closedBall (0: V) 1 ≃ₜ Metric.closedBall (0: W) 1) := by {
  have L := ContinuousLinearEquiv.ofFinrankEq hreq
  let pL := L ⁻¹'  Metric.closedBall 0 1 
  have hpL : pL = L.toHomeomorph ⁻¹'  Metric.closedBall 0 1  := rfl
  
  have h5 : IsCompact pL := by {
    rw [hpL,Homeomorph.isCompact_preimage]
    exact isCompact_closedBall 0 1
  }
  have h6 : (interior pL).Nonempty := by {
    rw [hpL, ← Homeomorph.preimage_interior]
    refine (Function.Surjective.nonempty_preimage ?_).mpr ?_
    exact Homeomorph.surjective L.toHomeomorph
    
    rw [interior_closedBall]
    all_goals simp_all
  }
  have e1 : pL ≃ₜ Metric.closedBall (0:W) 1 := by {
    rw [hpL]
    exact L.toHomeomorph.sets hpL
  }
  have h7 := homeo_unit_ball _ (Convex.linear_preimage (convex_closedBall 0 1) L.toLinearMap) h5 h6
  cases h7
  rename_i e2
  apply Nonempty.intro
  exact e2.symm.trans e1
}

lemma unit_cube_homeo_unit_ball {n}
    : Nonempty (Set.Icc (0 : Fin n → ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 ) := by
  apply homeo_unit_ball _ (convex_Icc 0 1) isCompact_Icc
  have h1 : Set.Icc (0 : Fin n → ℝ) 1 = Set.univ.pi  fun _ => Set.Icc  0  1  := by
    ext x; simp [Pi.le_def]
  rw [h1, interior_pi_set Set.finite_univ]
  exact Set.univ_pi_nonempty_iff.mpr fun _ => by
    simp_all

lemma homeo_unit_cube_of_convex_compact {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : s.Nonempty)
    : ∃ k, Nonempty (s ≃ₜ Set.Icc (0 : Fin k → ℝ) 1) := by {
  have := hne.coe_sort
  let W := affineSpan ℝ s
  obtain ⟨ps, hps⟩ := hne
  let pss : W := ⟨ps, mem_affineSpan ℝ hps⟩
  let g2 := AffineIsometryEquiv.constVSub ℝ pss
  let g1 : W → V := fun x ↦ x.1
  
  let s3 := g2.symm ⁻¹'  g1 ⁻¹' s 
  have h32 : Convex ℝ s3 := hcvx.affine_preimage
                        ((affineSpan ℝ s).subtype.comp
                        (AffineIsometryEquiv.constVSub ℝ pss).symm.toAffineMap)
  
  let g3 := g1.comp g2.symm
  have h4 : Topology.IsEmbedding g3 := by {
    apply Topology.IsEmbedding.subtypeVal.comp g2.symm.toHomeomorph.isEmbedding
  }
  have h5 : Set.MapsTo g3 s3 s := by
                                    solve_by_elim [_root_.Set.MapsTo.comp_right]
  
  let e1 := (h4.restrict h5).toHomeomorphOfSurjective (by {
                                                         refine (Set.MapsTo.restrict_surjective_iff h5).mpr ?_
                                                         refine Set.SurjOn.comp_right ?_ ?_
                                                         exact AffineIsometryEquiv.surjective g2.symm
                                                         intro v h1
                                                         
                                                         
                                                         use ⟨v, (mem_affineSpan ℝ h1)⟩
                                                         
                                                         apply And.intro h1 rfl
                                                       })
  
  obtain ⟨e2⟩ := homeo_unit_ball s3 h32 (by {
                                           have h51 : _ → IsCompact Set.univ := (Homeomorph.isCompact_image e1).mp
                                           simp only [Set.image_univ, EquivLike.range_eq_univ] at h51
                                           apply isCompact_iff_isCompact_univ.mpr
                                           apply h51 $ isCompact_iff_isCompact_univ.mp hcmpct
                                         }) (by {
                                               refine (Convex.interior_nonempty_iff_affineSpan_eq_top h32).mpr ?_
                                               unfold s3
                                               rw [←AffineIsometryEquiv.coe_toAffineEquiv]
                                               rw [← AffineSubspace.comap_span]
                                               rw [affineSpan_coe_preimage_eq_top]
                                               rfl
                                             })
  let k := Module.finrank ℝ W.direction
  obtain ⟨e3⟩ := @unit_cube_homeo_unit_ball k
  have h2 : k = Module.finrank ℝ (Fin k → ℝ) := (Module.finrank_fin_fun ℝ).symm
  obtain ⟨e4⟩ := homeo_of_finrank_eq h2
  
  use k
  exact Nonempty.intro ((e1.symm.trans e2).trans (e4.trans e3.symm))
}
