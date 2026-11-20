module

public import RequestProject.TruncatedCubePoset
public import RequestProject.OrderCxNullTransfer

@[expose] public section

/-! Retraction of the actual boundary with its cut facet deleted onto retained proper faces. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

variable (t : QOld A)

variable (hne : t.1.spx.Nonempty)

def fullCutCell : CutCell A :=
  ⟨t.1.spx, hne, t.1.isSimplex⟩

def CutPuncturedBoundary :=
  {c : TruncatedCell A // c < Sum.inl t ∧ c ≠ Sum.inr (fullCutCell t hne)}

def RetainedProperBoundary := {c : QOld A // c < t}

instance (hne : t.1.spx.Nonempty) :
    PartialOrder (CutPuncturedBoundary t hne) := Subtype.partialOrder _
instance : PartialOrder (RetainedProperBoundary t) := Subtype.partialOrder _

variable (hne : t.1.spx.Nonempty)

def cutBoundaryRetraction
    (c : CutPuncturedBoundary t hne) : RetainedProperBoundary t := by
  refine ⟨truncatedCellRetraction c.1, lt_of_le_of_ne (truncatedCellRetraction_monotone c.2.1.le) ?_⟩
  intro he
  rcases c with ⟨c, hc⟩
  cases c with
  | inl d => exact hc.1.ne (congrArg Sum.inl he)
  | inr σ =>
    exact hc.2 (congrArg Sum.inr (Subtype.ext (congrArg (fun d : QOld A => d.1.spx) he)))

def cutBoundarySection
    (c : RetainedProperBoundary t) : CutPuncturedBoundary t hne :=
  ⟨Sum.inl c.1, lt_of_le_of_ne c.2.le (fun h => c.2.ne (Sum.inl.inj h)), by simp⟩

theorem cutBoundaryRetraction_monotone :
    Monotone (cutBoundaryRetraction t hne) := by
  solve_by_elim [truncatedCellRetraction_monotone]

theorem cutBoundarySection_monotone :
    Monotone (cutBoundarySection t hne) := by solve_by_elim

theorem cutBoundary_le_section_retraction
    (c : CutPuncturedBoundary t hne) :
    c ≤ cutBoundarySection t hne (cutBoundaryRetraction t hne c) :=
  by apply truncatedCell_le_retraction

/-- The remaining simple-connectedness problem is exactly the retained proper-face boundary.
The retraction and its order homotopy are constructed, not assumed. -/
theorem cutPuncturedBoundary_simplyConnected_of_retained (hsc : SimplyConnected (orderCx (RetainedProperBoundary t))) :
    SimplyConnected (orderCx (CutPuncturedBoundary t hne)) := by
  intro a p hp
  let r := cutBoundaryRetraction t hne
  let s := cutBoundarySection t hne
  have hr := cutBoundaryRetraction_monotone t hne
  have hs := cutBoundarySection_monotone t hne
  have hpush := mapPath_htpy (orderCxMap s hs) (hsc (r a) (mapPath (orderCxMap r hr) p) (isPath_mapPath (orderCxMap r hr) hp))
  have hnil : Htpy _ (s (r a)) (s (r a))
      (mapPath (orderCxMap (s ∘ r) (hs.comp hr)) p) [] := by
    simpa [mapPath, orderCxMap, List.map_map, Function.comp_def] using hpush
  have hid := (htpy_nil_mapPath_le_iff monotone_id _
    (cutBoundary_le_section_retraction t hne) hp).mpr hnil
  simp_all [mapPath, orderCxMap]

theorem cutPuncturedBoundary_connected_of_retained (hconn : IsConnected (orderCx (RetainedProperBoundary t))) :
    IsConnected (orderCx (CutPuncturedBoundary t hne)) := by
  intro a b
  obtain ⟨p, hp⟩ := hconn _ _
  have hs := isPath_mapPath (orderCxMap (cutBoundarySection t hne)
    (cutBoundarySection_monotone t hne)) hp
  exact ⟨[ordPos _] ++
      mapPath _ p ++
      [ordNeg _],
    ((isPath_ordPos (cutBoundary_le_section_retraction t hne a)).append hs).append
      (isPath_ordNeg (cutBoundary_le_section_retraction t hne b))⟩

end FiniteChains.Davis
