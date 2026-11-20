module

public import RequestProject.ClassicalCellAttachmentMaps
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

/-! Explicit Hausdorff separation for arbitrary families of attached normed
disks. Old open sets extend through radial annuli; there is no local finiteness
assumption on the cell family. Pending Lean verification. -/

noncomputable section
open scoped Classical
open Set Topology

namespace FiniteChains.RelativeAttachment

universe u
variable {J E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]

variable (c : ℝ) (hc : 0 ≤ c)

def annulusBoundary
    (x : {x : ClosedUnitBall E // c < ‖x.val‖}) : UnitBoundary E :=
  ⟨‖x.val.val‖⁻¹ • x.val.val, by
    grind [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]⟩

theorem annulusBoundary_continuous :
    Continuous (annulusBoundary (E := E) c hc) := by
  apply Continuous.subtype_mk
  apply Continuous.smul
  · exact (continuous_norm.comp
      (continuous_subtype_val.comp continuous_subtype_val)).inv₀
        (fun x => ne_of_gt (lt_of_le_of_lt hc x.property))
  · exact continuous_subtype_val.comp continuous_subtype_val

variable (r : BoundaryFamily J E → X)

variable (c : ℝ) (hc : 0 ≤ c)

variable (U : Set X)

/-- An open set of the old space together with its radial collar of width
`1-c` in every attached disk. -/
def oldCollar :
    Set (DiskAttachment r) :=
  fun z => match z with
    | Sum.inl x => x ∈ U
    | Sum.inr d => ∃ h : c < ‖d.val.2.val‖,
        r ⟨d.val.1, annulusBoundary c hc ⟨d.val.2, h⟩⟩ ∈ U

omit [TopologicalSpace X] in
@[simp] theorem old_mem_oldCollar (x : X) :
    old r _ x ∈ oldCollar r c hc U ↔ x ∈ U := Iff.rfl

omit [TopologicalSpace X] in
theorem cell_mem_oldCollar (hcone : c < 1) (U : Set X)
    (j : J) (x : ClosedUnitBall E) :
    cell r _ ⟨j, x⟩ ∈ oldCollar r c hc U ↔
      ∃ h : c < ‖x.val‖, r ⟨j, annulusBoundary c hc ⟨x, h⟩⟩ ∈ U := by
  by_cases hx : ‖x.val‖ = 1
  · let a : UnitBoundary E := ⟨x.val, hx⟩
    have hb : cell r _ ⟨j, x⟩ =
        old r (boundaryFamilyInclusion J E) _ :=
      cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective ⟨j, a⟩
    rw [hb, old_mem_oldCollar]
    have he (h : c < ‖x.val‖) : annulusBoundary c hc ⟨x, h⟩ = a := by
      apply Subtype.ext
      simp [annulusBoundary, hx, inv_one, one_smul, a]
    constructor <;> grind
  · rw [cell_of_not_mem r _ _ (fun h => hx ((boundaryFamilyInclusion_range J E _).mp h))]
    rfl

theorem oldCollar_isOpen (hr : Continuous r)
    (c : ℝ) (hc : 0 ≤ c) (hcone : c < 1) (U : Set X) (hU : IsOpen U) :
    IsOpen (oldCollar r c hc U) := by
  refine ⟨hU, ?_⟩
  apply isOpen_sigma_iff.mpr
  intro j
  let A : Set (ClosedUnitBall E) := {x | c < ‖x.val‖}
  have he : (fun x : ClosedUnitBall E => cell r _ ⟨j, x⟩) ⁻¹'
      oldCollar r c hc U =
      Subtype.val '' ((fun x : A => r ⟨j, annulusBoundary c hc x⟩) ⁻¹' U) := by
    ext x
    rw [Set.mem_preimage, cell_mem_oldCollar r c hc hcone U j x]
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨⟨x, h⟩, hh, rfl⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨x'.property, hx'⟩
  change IsOpen ((fun x : ClosedUnitBall E => cell r _ _) ⁻¹'
    oldCollar r c hc U)
  rw [he]
  apply (isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)).isOpenEmbedding_subtypeVal.isOpenMap
  exact hU.preimage (hr.comp (continuous_sigmaMk.comp (annulusBoundary_continuous c hc)))

omit [TopologicalSpace X] in
theorem oldCollar_disjoint (c : ℝ) (hc : 0 ≤ c)
    {U V : Set X} (hUV : Disjoint U V) :
    Disjoint (oldCollar r c hc U) (oldCollar r c hc V) := by
  apply Set.disjoint_left.mpr
  rintro (x | d) hx hy
  · apply Set.disjoint_left.mp <;> assumption
  · obtain ⟨h, hh⟩ := hx
    obtain ⟨h', hh'⟩ := hy
    grind

theorem separate_old_fresh (hr : Continuous r)
    (x : X) (d : {d : DiskFamily J E // d ∉ Set.range _}) :
    ∃ U V : Set _, IsOpen U ∧ IsOpen V ∧
      old r _ x ∈ U ∧
      fresh r (boundaryFamilyInclusion J E) d ∈ V ∧ Disjoint U V := by
  have hdlt :=
    lt_of_le_of_ne d.val.2.property
      (fun h => d.property ((boundaryFamilyInclusion_range J E _).mpr h))
  let c := (‖d.val.2.val‖ + 1) / 2
  have hc : 0 ≤ c := by positivity
  have hdc : ‖d.val.2.val‖ < c := by dsimp [c]; linarith
  let V : Set {d : DiskFamily J E // d ∉ Set.range (boundaryFamilyInclusion J E)} :=
    {d | ‖d.val.2.val‖ < c}
  have hV : IsOpen V := by
    have hn : Continuous (fun d : DiskFamily J E => ‖d.2.val‖) := by
      apply continuous_sigma
      fun_prop
    exact isOpen_lt (hn.comp continuous_subtype_val) continuous_const
  refine ⟨oldCollar r c hc Set.univ,
    fresh r _ '' V,
    oldCollar_isOpen r hr c hc (by dsimp [c]; linarith) Set.univ isOpen_univ,
    (fresh_isOpenEmbedding r _
      (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range).isOpenMap _ hV,
    trivial, ⟨d, hdc, rfl⟩, ?_⟩
  apply Set.disjoint_left.mpr
  rintro _ hU ⟨d', hd', rfl⟩
  obtain ⟨h, _⟩ := hU <;> grind

/-- Adjoining any family of genuine normed disks to a Hausdorff space along
continuous boundary maps preserves Hausdorffness. -/
theorem diskAttachment_t2Space [T2Space X]
    (r : BoundaryFamily J E → X) (hr : Continuous r) : T2Space (DiskAttachment r) where
  t2 := by
    rintro (x | d) (y | e) hne
    · obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation (fun h => hne (congrArg Sum.inl h))
      exact ⟨oldCollar r 0 le_rfl U, oldCollar r 0 le_rfl V,
        oldCollar_isOpen r hr 0 le_rfl zero_lt_one U hU,
        oldCollar_isOpen r hr 0 le_rfl zero_lt_one V hV,
        hx, hy, oldCollar_disjoint r 0 le_rfl hUV⟩
    · apply separate_old_fresh <;> assumption
    · obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := separate_old_fresh r hr y d
      exact ⟨V, U, hV, hU, hy, hx, hUV.symm⟩
    · obtain ⟨U, V, hU, hV, hd, he, hUV⟩ := t2_separation (fun h => hne (congrArg Sum.inr h))
      have hf := fresh_isOpenEmbedding r _
        (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range
      refine ⟨fresh r _ '' U, fresh r _ '' V, hf.isOpenMap _ hU, hf.isOpenMap _ hV,
        ⟨d, hd, rfl⟩, ⟨e, he, rfl⟩, ?_⟩
      apply Set.disjoint_left.mpr
      rintro _ ⟨d', hd', rfl⟩ ⟨e', he', heq⟩
      have heq' := hf.injective heq
      grind

end FiniteChains.RelativeAttachment
