module

public import RequestProject.DiskAttachmentAvoidCenters

@[expose] public section

noncomputable section
open scoped Classical unitInterval
open Set Topology

namespace FiniteChains.RelativeAttachment

variable {E X J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialDiskPoint (t : I) (x : ClosedUnitBall E) : ClosedUnitBall E :=
  ⟨((1 - (t : ℝ)) + (t : ℝ) / ‖x.val‖) • x.val, by
    have ht0 := t.property.1; have ht1 := t.property.2; have hr := x.property
    have hs : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) / ‖x.val‖ :=
      add_nonneg (sub_nonneg.mpr ht1) (div_nonneg ht0 (norm_nonneg _))
    rw [norm_smul, Real.norm_of_nonneg hs, add_mul]
    by_cases hx : ‖x.val‖ = 0
    · simp [hx]
    · rw [div_mul_cancel₀ _ hx]; nlinarith⟩

def radialCoreBack (r : BoundaryFamily J E → X) : puncturedAttachment r → X
  | ⟨.inl x, _⟩ => x
  | ⟨.inr d, hd⟩ => r ⟨d.val.1, annulusBoundary 0 le_rfl ⟨d.val.2, Classical.choose hd⟩⟩

theorem radialCoreBack_mem_iff (r : BoundaryFamily J E → X)
    (z : puncturedAttachment r) (U : Set X) :
    radialCoreBack r z ∈ U ↔ z.val ∈ oldCollar r 0 le_rfl U := by
  rcases z with ⟨x | d, hz⟩
  · rfl
  · exact ⟨fun h => ⟨Classical.choose hz, h⟩, fun ⟨_, h⟩ => h⟩

variable [TopologicalSpace X]

theorem radialCoreBack_continuous (r : BoundaryFamily J E → X) (hr : Continuous r) :
    Continuous (radialCoreBack r) :=
  continuous_def.mpr fun U hU => by
    rw [show radialCoreBack r ⁻¹' U = Subtype.val ⁻¹' oldCollar r 0 le_rfl U
      from Set.ext fun z => radialCoreBack_mem_iff r z U]
    exact (oldCollar_isOpen r hr 0 le_rfl zero_lt_one U hU).preimage continuous_subtype_val

def radialDiskPath (r : BoundaryFamily J E → X) (j : J) (x : ClosedUnitBall E) :
    C(I, DiskAttachment r) :=
  ⟨fun t => cell r (boundaryFamilyInclusion J E) ⟨j, radialDiskPoint t x⟩,
    (cell_continuous r _).comp (continuous_sigmaMk.comp
      (Continuous.subtype_mk (((continuous_const.sub continuous_subtype_val).add
        (continuous_subtype_val.div_const _)).smul continuous_const) _))⟩

def radialFamily (r : BoundaryFamily J E → X) : DiskAttachment r → C(I, DiskAttachment r)
  | .inl x => ContinuousMap.const I (old r (boundaryFamilyInclusion J E) x)
  | .inr d => radialDiskPath r d.val.1 d.val.2

theorem radialFamily_continuousOn (r : BoundaryFamily J E → X) (hr : Continuous r) :
    ContinuousOn (radialFamily r) (puncturedAttachment r) := by
  have hcell (d : DiskFamily J E) :
      radialFamily r (cell r (boundaryFamilyInclusion J E) d) = radialDiskPath r d.1 d.2 := by
    by_cases hd : d ∈ Set.range (boundaryFamilyInclusion J E)
    · obtain ⟨a, rfl⟩ := hd
      have hcb := cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
      rw [hcb]
      refine ContinuousMap.ext fun t => ?_
      change old r (boundaryFamilyInclusion J E) (r a) =
        cell r (boundaryFamilyInclusion J E) ⟨a.1, radialDiskPoint t (unitBoundaryInclusion E a.2)⟩
      rw [show radialDiskPoint t (unitBoundaryInclusion E a.2) = unitBoundaryInclusion E a.2
        from Subtype.ext (by simp [radialDiskPoint, unitBoundaryInclusion, a.2.property])]
      exact (hcb a).symm
    · rw [cell_of_not_mem r _ d hd]; rfl
  have hq : IsQuotientMap (quotientMap r (boundaryFamilyInclusion J E)) :=
    ⟨⟨rfl⟩, quotientMap_surjective r _⟩
  apply (hq.continuousOn_isOpen_iff (puncturedAttachment_isOpen r hr)).mpr
  apply continuousOn_of_forall_continuousAt
  rintro (x | ⟨j, x⟩) hz
  · exact IsOpenEmbedding.inl.continuousAt_iff.mp
      (⟨fun z : X × I => old r (boundaryFamilyInclusion J E) z.1,
        (old_continuous r _).comp continuous_fst⟩ : C(X × I, _)).curry.continuous.continuousAt
  · apply IsOpenEmbedding.inr.continuousAt_iff.mp
    have he : radialFamily r ∘ cell r (boundaryFamilyInclusion J E) =
        fun d : DiskFamily J E => radialDiskPath r d.1 d.2 := funext hcell
    change ContinuousAt (radialFamily r ∘ cell r (boundaryFamilyInclusion J E)) ⟨j, x⟩
    rw [he]
    apply IsOpenEmbedding.sigmaMk.continuousAt_iff.mp
    have hx : 0 < ‖x.val‖ :=
      ((cell_mem_oldCollar r 0 le_rfl zero_lt_one Set.univ j x).mp hz).choose
    have ho : IsOpen {x : ClosedUnitBall E | 0 < ‖x.val‖} :=
      isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
    have hpos : Continuous (fun z : {x : ClosedUnitBall E // 0 < ‖x.val‖} =>
        radialDiskPath r j z.val) :=
      (⟨fun z : {x : ClosedUnitBall E // 0 < ‖x.val‖} × I =>
          cell r (boundaryFamilyInclusion J E) ⟨j, radialDiskPoint z.2 z.1.val⟩,
        (cell_continuous r _).comp (continuous_sigmaMk.comp
          (Continuous.subtype_mk (((continuous_const.sub continuous_snd.subtype_val).add
            (continuous_snd.subtype_val.div (by fun_prop) fun z => ne_of_gt z.1.property)).smul
              (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))) _))⟩ :
        C(_, _)).curry.continuous
    exact (ho.isOpenEmbedding_subtypeVal.continuousAt_iff
      (g := fun x : ClosedUnitBall E => radialDiskPath r j x) (x := ⟨x, hx⟩)).mp hpos.continuousAt

def radialCoreHomotopy (r : BoundaryFamily J E → X) (hr : Continuous r) :
    ContinuousMap.Homotopy
      (⟨Subtype.val, continuous_subtype_val⟩ : C(puncturedAttachment r, DiskAttachment r))
      (⟨fun z => old r (boundaryFamilyInclusion J E) (radialCoreBack r z),
        (old_continuous r _).comp (radialCoreBack_continuous r hr)⟩) where
  toContinuousMap :=
    (⟨fun z => radialFamily r z.val, (radialFamily_continuousOn r hr).restrict⟩ :
      C(puncturedAttachment r, C(I, DiskAttachment r))).uncurry.comp ⟨Prod.swap, continuous_swap⟩
  map_zero_left := by
    rintro ⟨x | d, _⟩
    · rfl
    · change cell r (boundaryFamilyInclusion J E) ⟨d.val.1, radialDiskPoint 0 d.val.2⟩ = .inr d
      rw [show radialDiskPoint 0 d.val.2 = d.val.2 from Subtype.ext (by simp [radialDiskPoint])]
      exact cell_of_not_mem r _ d.val d.property
  map_one_left := by
    rintro ⟨x | d, hz⟩
    · rfl
    · change cell r (boundaryFamilyInclusion J E) ⟨d.val.1, radialDiskPoint 1 d.val.2⟩ = _
      rw [show radialDiskPoint 1 d.val.2 =
          unitBoundaryInclusion E (annulusBoundary 0 le_rfl ⟨d.val.2, Classical.choose hz⟩)
        from Subtype.ext (by simp [radialDiskPoint, annulusBoundary, unitBoundaryInclusion, one_div])]
      exact cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
        ⟨d.val.1, annulusBoundary 0 le_rfl ⟨d.val.2, Classical.choose hz⟩⟩

theorem radialCoreHomotopy_mem_oldCollar (r : BoundaryFamily J E → X)
    (hr : Continuous r) (t : I) (z : puncturedAttachment r) (U : Set X)
    (hz : z.val ∈ oldCollar r 0 le_rfl U) :
    radialCoreHomotopy r hr (t, z) ∈ oldCollar r 0 le_rfl U := by
  rcases z with ⟨x | d, _⟩
  · exact hz
  · obtain ⟨hx, hU⟩ := hz
    have hs : 0 < (1 - (t : ℝ)) + (t : ℝ) / ‖d.val.2.val‖ := by
      rcases eq_or_lt_of_le t.2.2 with ht | ht
      · rw [ht]; positivity
      · exact add_pos_of_pos_of_nonneg (sub_pos.mpr ht) (div_nonneg t.2.1 hx.le)
    have hpos : 0 < ‖(radialDiskPoint t d.val.2).val‖ := by
      change 0 < ‖((1 - (t : ℝ)) + (t : ℝ) / ‖d.val.2.val‖) • d.val.2.val‖
      rw [norm_smul, Real.norm_of_nonneg hs.le]; exact mul_pos hs hx
    have hnorm : annulusBoundary 0 le_rfl ⟨radialDiskPoint t d.val.2, hpos⟩ =
        annulusBoundary 0 le_rfl ⟨d.val.2, hx⟩ := by
      apply Subtype.ext
      change ‖((1 - (t : ℝ)) + (t : ℝ) / ‖d.val.2.val‖) • d.val.2.val‖⁻¹ •
        (((1 - (t : ℝ)) + (t : ℝ) / ‖d.val.2.val‖) • d.val.2.val) = ‖d.val.2.val‖⁻¹ • d.val.2.val
      rw [norm_smul, Real.norm_of_nonneg hs.le, smul_smul,
        mul_inv_rev, mul_assoc, inv_mul_cancel₀ (ne_of_gt hs), mul_one]
    change cell r (boundaryFamilyInclusion J E)
      ⟨d.val.1, radialDiskPoint t d.val.2⟩ ∈ oldCollar r 0 le_rfl U
    rw [cell_mem_oldCollar r 0 le_rfl zero_lt_one]
    exact ⟨hpos, by simpa only [hnorm] using hU⟩

theorem twoCellAttachment_path_into_old
    (r : BoundaryFamily J (Fin 2 → ℝ) → X) (hr : Continuous r) (x y : X)
    (p : Path (old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) x)
      (old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) y)) :
    ∃ q : Path x y, Path.Homotopic p
      (q.map (old_continuous r (boundaryFamilyInclusion J (Fin 2 → ℝ)))) := by
  obtain ⟨q, hq, hpq⟩ := diskAttachment_path_avoid_centers r hr
    (by rw [rank_fun']; norm_num)
    (x := old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) x)
    (y := old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) y) trivial trivial p
  let Q : Path (⟨old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) x, trivial⟩ : puncturedAttachment r)
      ⟨old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) y, trivial⟩ :=
    ⟨⟨fun t => ⟨q t, hq ⟨t, rfl⟩⟩, q.continuous.subtype_mk _⟩,
      Subtype.ext q.source, Subtype.ext q.target⟩
  let v : Path x y := Q.map (radialCoreBack_continuous r hr)
  let H := radialCoreHomotopy r hr
  refine ⟨v, hpq.trans ⟨{
    toFun := fun ts => H (ts.1, Q ts.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk (Q.continuous.comp continuous_snd))
    map_zero_left := fun s => H.map_zero_left (Q s)
    map_one_left := fun s => H.map_one_left (Q s)
    prop' := by
      rintro t s (rfl | hs)
      · change H (t, Q 0) = q 0; rw [Q.source, q.source]; rfl
      · subst hs; change H (t, Q 1) = q 1; rw [Q.target, q.target]; rfl }⟩⟩
