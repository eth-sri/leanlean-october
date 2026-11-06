import RequestProject.TruncatedCubePoset
import RequestProject.OrderCxNullTransfer
import RequestProject.Tac


/-! Retraction of the actual boundary with its cut facet deleted onto retained proper faces. -/
bwd

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def fullCutCell (t : QOld A) (hne : t.1.spx.Nonempty) : CutCell A :=
  ⟨t.1.spx, hne, t.1.isSimplex⟩

def CutPuncturedBoundary (t : QOld A) (hne : t.1.spx.Nonempty) :=
  {c : TruncatedCell A // c < Sum.inl t ∧ c ≠ Sum.inr (fullCutCell t hne)}

def RetainedProperBoundary (t : QOld A) := {c : QOld A // c < t}

instance (t : QOld A) hne :
    PartialOrder (CutPuncturedBoundary t hne) := Subtype.partialOrder _
instance (t : QOld A) : PartialOrder (RetainedProperBoundary t) := Subtype.partialOrder _

def cutBoundaryRetraction (t : QOld A) hne
    (c : CutPuncturedBoundary t hne) : RetainedProperBoundary t := by
  have hle :=
    truncatedCellRetraction_monotone c.2.1.le
  refine ⟨truncatedCellRetraction c.1, lt_of_le_of_ne hle ?_⟩
  intro he
  cases' c with c hc
  cases c with
  | inl d => exact hc.1.ne (congrArg Sum.inl he)
  | inr σ =>
    have hs : σ.1 = t.1.spx := by aesop
    exact hc.2 (congrArg Sum.inr (Subtype.ext hs))

def cutBoundarySection (t : QOld A) hne
    (c : RetainedProperBoundary t) : CutPuncturedBoundary t hne :=
  ⟨Sum.inl c.1, lt_of_le_of_ne c.2.le (by grind), by simp⟩

theorem cutBoundaryRetraction_monotone (t : QOld A) hne :
    Monotone (cutBoundaryRetraction t hne) := by
  intro c d h
  exact truncatedCellRetraction_monotone h

theorem cutBoundarySection_monotone (t : QOld A) hne :
    Monotone (cutBoundarySection t hne) := by tauto

theorem cutBoundary_le_section_retraction (t : QOld A) hne
    c :
    c ≤ cutBoundarySection t hne (cutBoundaryRetraction t hne c) :=
  truncatedCell_le_retraction c.1

/-- The remaining simple-connectedness problem is exactly the retained proper-face boundary.
The retraction and its order homotopy are constructed, not assumed. -/
theorem cutPuncturedBoundary_simplyConnected_of_retained (t : QOld A)
    hne (hsc : SimplyConnected (orderCx (RetainedProperBoundary t))) :
    SimplyConnected (orderCx (CutPuncturedBoundary t hne)) := by
  intro a p hp
  let r := cutBoundaryRetraction t hne
  let s := cutBoundarySection t hne
  have hr := cutBoundaryRetraction_monotone t hne
  have hs := cutBoundarySection_monotone t hne
  have hn := hsc _ _ (isPath_mapPath (orderCxMap r hr) hp)
  have hpush := mapPath_htpy (orderCxMap s hs) hn
  have hnil : Htpy _ (s (r a)) (s (r a))
      (mapPath (orderCxMap _ (hs.comp hr)) p) [] := by
    simpa [mapPath, orderCxMap, List.map_map, Function.comp_def] using hpush
  have hid := (htpy_nil_mapPath_le_iff monotone_id _
    (cutBoundary_le_section_retraction t hne) hp).mpr hnil
  simpa [mapPath, orderCxMap] using hid

theorem cutPuncturedBoundary_connected_of_retained (t : QOld A)
    hne (hconn : IsConnected (orderCx (RetainedProperBoundary t))) :
    IsConnected (orderCx (CutPuncturedBoundary t hne)) := by
  intro a b
  cases' hconn _ _ with p hp
  have hs := isPath_mapPath (orderCxMap (cutBoundarySection t hne)
    (cutBoundarySection_monotone t hne)) hp
  exact ⟨[ordPos (cutBoundary_le_section_retraction t hne a)] ++
      mapPath (orderCxMap _ (cutBoundarySection_monotone t hne)) p ++
      [ordNeg (cutBoundary_le_section_retraction t hne b)],
    ((isPath_ordPos _).append hs).append
      (by aesop)⟩
