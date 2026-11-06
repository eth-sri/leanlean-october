import RequestProject.DiskAttachmentAvoidCenters


/-! Explicit radial deformation of the complement of the disk centers to
the literal old space. Continuity is proved with the actual attachment
quotient and compact-open currying; infinite families need no extra premise.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

namespace FiniteChains.RelativeAttachment

variable {E X J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]

def radialDiskPoint (t : I) (x : ClosedUnitBall E) : ClosedUnitBall E :=
  ⟨((1 - (t : ℝ)) + (t : ℝ) / ‖x.val‖) • x.val, by
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hr := x.property
    have hs : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) / ‖x.val‖ :=
      by positivity
    rw [norm_smul, Real.norm_of_nonneg hs, add_mul]
    by_cases hx : ‖x.val‖ = 0
    · simp_all
    · rw [div_mul_cancel₀ _ hx]
      nlinarith⟩

theorem radialDiskPoint_zero (x : ClosedUnitBall E) : radialDiskPoint 0 x = x := by
  apply Subtype.ext
  simp [radialDiskPoint]

theorem radialDiskPoint_boundary t x :
    radialDiskPoint t (unitBoundaryInclusion E x) = unitBoundaryInclusion E x := by
  apply Subtype.ext
  simp [radialDiskPoint, unitBoundaryInclusion, x.property]

theorem radialDiskPoint_one x hx :
    radialDiskPoint 1 x =
      unitBoundaryInclusion E (annulusBoundary 0 le_rfl ⟨x, hx⟩) := by
  apply Subtype.ext
  simp [radialDiskPoint, annulusBoundary, unitBoundaryInclusion, one_div]

theorem radialDiskPoint_continuous (x : ClosedUnitBall E) :
    Continuous (radialDiskPoint · x) := by
  apply Continuous.subtype_mk
  fun_prop

theorem radialDiskPoint_continuous_positive :
    Continuous (fun z : {x : ClosedUnitBall E // 0 < ‖x.val‖} × I =>
      radialDiskPoint z.2 z.1.val) := by
  apply Continuous.subtype_mk
  have hn : Continuous (fun z : {x : ClosedUnitBall E // 0 < ‖x.val‖} × I => ‖z.1.val.val‖) := by
    fun_prop
  exact ((continuous_const.sub continuous_snd.subtype_val).add
    (continuous_snd.subtype_val.div hn (by simp))).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))

def radialCoreBack (r : BoundaryFamily J E → X) (z : puncturedAttachment r) : X :=
  match z with
  | ⟨Sum.inl x, _⟩ => x
  | ⟨Sum.inr d, hd⟩ =>
      r ⟨d.val.1, annulusBoundary 0 le_rfl ⟨d.val.2, hd.choose⟩⟩

omit [TopologicalSpace X] in
theorem radialCoreBack_mem_iff (r : BoundaryFamily J E → X)
    (z : puncturedAttachment r) (U : Set X) :
    radialCoreBack r z ∈ U ↔ z.val ∈ oldCollar r 0 le_rfl U := by
  rcases z with ⟨x | d, hz⟩
  · rfl
  · change r ⟨d.val.1, annulusBoundary 0 le_rfl ⟨d.val.2, hz.choose⟩⟩ ∈ U ↔
      ∃ h : 0 < ‖d.val.2.val‖, r ⟨d.val.1, annulusBoundary 0 le_rfl ⟨d.val.2, h⟩⟩ ∈ U
    tauto

theorem radialCoreBack_continuous (r : BoundaryFamily J E → X) (hr : Continuous r) :
    Continuous (radialCoreBack r) := by
  apply continuous_def.mpr
  intro U hU
  have he : radialCoreBack r ⁻¹' U =
      Subtype.val ⁻¹' oldCollar r 0 le_rfl U := by
    ext z
    exact radialCoreBack_mem_iff r z U
  rw [he]
  exact (oldCollar_isOpen r hr 0 le_rfl zero_lt_one U hU).preimage continuous_subtype_val

def radialDiskPath (r : BoundaryFamily J E → X) (j : J) (x : ClosedUnitBall E) :
    C(I, DiskAttachment r) :=
  ⟨fun t => cell r _ ⟨j, radialDiskPoint t x⟩,
    (cell_continuous r _).comp (continuous_sigmaMk.comp (radialDiskPoint_continuous x))⟩

def radialFamily (r : BoundaryFamily J E → X) : DiskAttachment r → C(I, DiskAttachment r)
  | Sum.inl x => ContinuousMap.const I (old r (boundaryFamilyInclusion J E) x)
  | Sum.inr d => radialDiskPath r d.val.1 d.val.2

theorem radialFamily_cell (r : BoundaryFamily J E → X) d :
    radialFamily r (cell r (boundaryFamilyInclusion J E) d) = radialDiskPath r d.1 d.2 := by
  by_cases hd : d ∈ Set.range (boundaryFamilyInclusion J E)
  · obtain ⟨a, rfl⟩ := hd
    rw [cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective]
    apply ContinuousMap.ext
    intro t
    change old r (boundaryFamilyInclusion J E) (r a) =
      cell r _ ⟨a.1, radialDiskPoint t (unitBoundaryInclusion E a.2)⟩
    rw [radialDiskPoint_boundary]
    exact (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective a).symm
  aesop

theorem radialDiskPath_continuous_positive (r : BoundaryFamily J E → X) j :
    Continuous (fun x : {x : ClosedUnitBall E // 0 < ‖x.val‖} => radialDiskPath r j x.val) := by
  let F : C({x : ClosedUnitBall E // 0 < ‖x.val‖} × I, DiskAttachment r) :=
    ⟨fun z => cell r _ ⟨j, radialDiskPoint z.2 z.1.val⟩,
      (cell_continuous r _).comp (continuous_sigmaMk.comp radialDiskPoint_continuous_positive)⟩
  exact F.curry.continuous

theorem radialFamily_continuousOn (r : BoundaryFamily J E → X) (hr : Continuous r) :
    ContinuousOn (radialFamily r) (puncturedAttachment r) := by
  have hq : IsQuotientMap (quotientMap r (boundaryFamilyInclusion J E)) :=
    ⟨⟨rfl⟩, quotientMap_surjective r _⟩
  apply (hq.continuousOn_isOpen_iff (puncturedAttachment_isOpen r hr)).mpr
  apply continuousOn_of_forall_continuousAt
  rintro (x | d) hz
  · apply IsOpenEmbedding.inl.continuousAt_iff.mp
    let F : C(X × I, DiskAttachment r) :=
      ⟨fun z => old r _ z.1, (old_continuous r _).comp continuous_fst⟩
    exact F.curry.continuous.continuousAt
  · apply IsOpenEmbedding.inr.continuousAt_iff.mp
    have he : radialFamily r ∘ cell r _ =
        fun d => radialDiskPath r d.1 d.2 :=
      funext (radialFamily_cell r)
    change ContinuousAt (radialFamily r ∘ cell r _) d
    rw [he]
    cases' d with j x
    apply IsOpenEmbedding.sigmaMk.continuousAt_iff.mp
    have hx :=
      ((cell_mem_oldCollar r 0 le_rfl zero_lt_one Set.univ j x).mp hz).choose
    have ho : IsOpen {x : ClosedUnitBall E | 0 < ‖x.val‖} :=
      isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
    have hh : ContinuousAt
        (fun z : {x : ClosedUnitBall E // 0 < ‖x.val‖} => radialDiskPath r j z.val)
        ⟨x, hx⟩ := (radialDiskPath_continuous_positive r j).continuousAt
    exact (ho.isOpenEmbedding_subtypeVal.continuousAt_iff
      (g := fun x => radialDiskPath r j x) (x := ⟨x, hx⟩)).mp hh

/-- The radial homotopy lands in the actual attachment and fixes every
old point at every time. This is the part needed to cellularize paths. -/
def radialCoreHomotopy (r : BoundaryFamily J E → X) (hr : Continuous r) :
    ContinuousMap.Homotopy
      (⟨Subtype.val, continuous_subtype_val⟩ : C(puncturedAttachment r, DiskAttachment r))
      (⟨fun z => old r (boundaryFamilyInclusion J E) (radialCoreBack r z),
        (old_continuous r _).comp (radialCoreBack_continuous r hr)⟩) := by
  let F : C(puncturedAttachment r, C(I, DiskAttachment r)) :=
    ⟨fun z => radialFamily r z.val, (radialFamily_continuousOn r hr).restrict⟩
  refine {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := ?_
    map_one_left := ?_ }
  · rintro ⟨x | d, hz⟩
    · rfl
    · change cell r _ ⟨d.val.1, radialDiskPoint 0 d.val.2⟩ = Sum.inr d
      rw [radialDiskPoint_zero]
      aesop
  · rintro ⟨x | d, hz⟩
    · rfl
    · change cell r (boundaryFamilyInclusion J E) ⟨d.val.1, radialDiskPoint 1 d.val.2⟩ = _
      rw [radialDiskPoint_one d.val.2 hz.choose]
      exact cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
        ⟨d.val.1, annulusBoundary 0 le_rfl ⟨d.val.2, hz.choose⟩⟩


theorem radialDiskPoint_positive t (x : ClosedUnitBall E)
    (hx : 0 < ‖x.val‖) : 0 < ‖(radialDiskPoint t x).val‖ := by
  have hs : 0 < (1 - t) + t / ‖x.val‖ := by
    by_cases ht : (t : ℝ) < 1
    · exact add_pos_of_pos_of_nonneg (sub_pos.mpr ht)
        (div_nonneg t.property.1 hx.le)
    · have ht' : t = 1 := by grind
      simp_all
  change 0 < ‖((1 - t) + t / ‖x.val‖) • x.val‖
  aesop

theorem radialDiskPoint_normalize t (x : ClosedUnitBall E)
    hx :
    annulusBoundary 0 le_rfl ⟨radialDiskPoint t x, radialDiskPoint_positive t x hx⟩ =
      annulusBoundary 0 le_rfl ⟨x, hx⟩ := by
  have hs : 0 < (1 - t) + t / ‖x.val‖ := by
    by_cases ht : (t : ℝ) < 1
    · exact add_pos_of_pos_of_nonneg (sub_pos.mpr ht)
        (div_nonneg t.property.1 hx.le)
    · have ht' : t = 1 := by grind
      simp_all
  apply Subtype.ext
  change ‖((1 - t) + t / ‖x.val‖) • x.val‖⁻¹ •
      (((1 - t) + t / ‖x.val‖) • x.val) = ‖x.val‖⁻¹ • x.val
  simp [norm_smul, Real.norm_of_nonneg hs.le, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (ne_of_gt hs), mul_one]

/-- Every radial ray remains over its same point of the old space. -/
theorem radialCoreHomotopy_mem_oldCollar (r : BoundaryFamily J E → X)
    hr t z U
    (hz : z.val ∈ oldCollar r 0 le_rfl U) :
    radialCoreHomotopy r hr (t, z) ∈ oldCollar r 0 le_rfl U := by
  rcases z with ⟨x | d, hzcore⟩
  · exact hz
  · cases' hz with hx hU
    change cell r _
      ⟨d.val.1, radialDiskPoint t d.val.2⟩ ∈ oldCollar r 0 le_rfl U
    rw [cell_mem_oldCollar r 0 le_rfl zero_lt_one]
    exact ⟨radialDiskPoint_positive t d.val.2 hx,
      by simp_all [radialDiskPoint_normalize t d.val.2 hx]⟩

/-- A path between old points in a disk attachment of dimension at least
two is homotopic, fixing its endpoints, to an actual path in the old space. -/
theorem diskAttachment_path_into_old r (hr : Continuous r)
    (hdim : 1 < Module.rank ℝ E) (x y : X)
    p :
    ∃ q : Path x y, Path.Homotopic p (q.map (old_continuous r (boundaryFamilyInclusion J E))) := by
  obtain ⟨q, hq, hpq⟩ := diskAttachment_path_avoid_centers r hr hdim
    (x := old r _ x)
    (y := old r _ y) trivial trivial p
  let Q : Path (⟨old r (boundaryFamilyInclusion J E) x, trivial⟩ : puncturedAttachment r)
      ⟨old r _ y, trivial⟩ := {
    toFun := fun t => ⟨q t, hq ⟨t, rfl⟩⟩
    continuous_toFun := q.continuous.subtype_mk _
    source' := Subtype.ext q.source
    target' := Subtype.ext q.target }
  let v := Q.map (radialCoreBack_continuous r hr)
  let H := radialCoreHomotopy r hr
  have hqv : q.Homotopic (v.map (old_continuous r _)) := by
    refine ⟨{
      toFun := fun ts => H (ts.1, Q ts.2)
      continuous_toFun := H.continuous.comp (continuous_fst.prodMk (Q.continuous.comp continuous_snd))
      map_zero_left := by aesop
      map_one_left := by aesop
      prop' := ?_ }⟩
    aesop
  exact ⟨v, hpq.trans hqv⟩

theorem twoCellAttachment_path_into_old
    r (hr : Continuous r) (x y : X)
    p :
    ∃ q : Path x y, Path.Homotopic p
      (q.map (old_continuous r (boundaryFamilyInclusion J (Fin 2 → ℝ)))) := by
  apply diskAttachment_path_into_old r hr _ x y p
  simp
