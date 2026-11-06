module

public import Mathlib

/-!
# Homeomorphisms of compact convex sets

Compact convex sets are reduced to unit balls in their affine spans and then to
finite-dimensional cubes. These homeomorphisms transfer the cubical fixed-point
theorem to arbitrary nonempty compact convex domains.
-/

@[expose] public section

theorem homeo_unit_ball {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s)
    (hni : (interior s).Nonempty):
    Nonempty (s ≃ₜ Metric.closedBall (0: V) 1) := by
  cases ((exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcvx hni) (IsCompact.isBounded hcmpct))
  rename_i e he
  have h4 := closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcmpct)
  have e2 := Homeomorph.image e s
  simp_all
  rw [he.2.1] at e2
  tauto

theorem homeo_of_finrank_eq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hreq : Module.finrank ℝ V = Module.finrank ℝ W) :
    Nonempty (Metric.closedBall (0: V) 1 ≃ₜ Metric.closedBall (0: W) 1) := by
  have L := ContinuousLinearEquiv.ofFinrankEq hreq
  let pL := L ⁻¹' (Metric.closedBall (0:W) 1)
  have hpL : pL = L.toHomeomorph ⁻¹' (Metric.closedBall (0:W) 1) := rfl
  have h4 := Convex.linear_preimage (convex_closedBall 0 1) L.toLinearMap
  have h5 : IsCompact pL := by
    rw [hpL,Homeomorph.isCompact_preimage]
    exact isCompact_closedBall 0 1
  have h6 : (interior pL).Nonempty := by
    rw [hpL, ← Homeomorph.preimage_interior]
    refine (Function.Surjective.nonempty_preimage ?_).mpr ?_
    exact Homeomorph.surjective L.toHomeomorph
    use 0
    rw [interior_closedBall]
    {simp only [Metric.mem_ball, dist_self, zero_lt_one]}
    simp
  have e1 : pL ≃ₜ Metric.closedBall (0:W) 1 :=
    L.toHomeomorph.sets hpL
  cases (homeo_unit_ball _ h4 h5 h6)
  rename_i e2
  apply Nonempty.intro
  exact e2.symm.trans e1

theorem unit_cube_homeo_unit_ball {n}
    : Nonempty (Set.Icc (0 : Fin n → ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 ) := by
  apply homeo_unit_ball _ (convex_Icc 0 1) isCompact_Icc
  have h1 : Set.Icc (0 : Fin n → ℝ) 1 = Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) := by
    aesop
  rw [h1, interior_pi_set Set.finite_univ]
  exact Set.univ_pi_nonempty_iff.mpr fun _ => by
    simp

theorem homeo_unit_cube_of_convex_compact {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : s.Nonempty)
    : ∃ k, Nonempty (s ≃ₜ Set.Icc (0 : Fin k → ℝ) 1) := by
  have := hne.coe_sort
  let W := affineSpan ℝ s
  obtain ⟨ps, hps⟩ := hne
  let pss : W := ⟨ps, mem_affineSpan ℝ hps⟩
  let g2 := AffineIsometryEquiv.constVSub ℝ pss
  let g1 : W → V := fun x ↦ x.1
  let s2 := g1 ⁻¹' s
  let s3 := g2.symm ⁻¹' s2
  have h32 : Convex ℝ s3 :=
    hcvx.affine_preimage
      ((affineSpan ℝ s).subtype.comp
      (AffineIsometryEquiv.constVSub ℝ pss).symm.toAffineMap)
  have h34 : (interior s3).Nonempty := by
    refine (Convex.interior_nonempty_iff_affineSpan_eq_top h32).mpr ?_
    unfold s3
    rw [←AffineIsometryEquiv.coe_toAffineEquiv, ← AffineSubspace.comap_span]
    aesop
  let g3 := g1.comp g2.symm
  have h4 : Topology.IsEmbedding g3 := by
    apply Topology.IsEmbedding.subtypeVal.comp g2.symm.toHomeomorph.isEmbedding
  have h5 : Set.MapsTo g3 s3 s := by
    tauto
  have h6 : Function.Surjective (Set.MapsTo.restrict g3 s3 s h5) := by
    refine (Set.MapsTo.restrict_surjective_iff h5).mpr ?_
    refine Set.SurjOn.comp_right ?_ ?_
    exact AffineIsometryEquiv.surjective g2.symm
    intro v h1
    have h11 := mem_affineSpan ℝ h1
    aesop
  let e1 := (h4.restrict h5).toHomeomorphOfSurjective h6
  have h31 : IsCompact s3 := by
    have h51 : _ → IsCompact Set.univ := (Homeomorph.isCompact_image e1).mp
    simp at h51
    apply isCompact_iff_isCompact_univ.mpr
    apply h51 $ isCompact_iff_isCompact_univ.mp hcmpct
  obtain ⟨e2⟩ := homeo_unit_ball s3 h32 h31 h34
  let k := Module.finrank ℝ W.direction
  obtain ⟨e3⟩ := @unit_cube_homeo_unit_ball k
  have h2 : k = Module.finrank ℝ (Fin k → ℝ) := by simp
  obtain ⟨e4⟩ := homeo_of_finrank_eq h2
  let e5 := (e1.symm.trans e2).trans (e4.trans e3.symm)
  tauto
