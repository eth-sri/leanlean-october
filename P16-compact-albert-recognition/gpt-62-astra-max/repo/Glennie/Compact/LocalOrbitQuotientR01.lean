/- Genuine quotient topology of the admitted local ordered-frame domain by the
actual simultaneous product-and-trace automorphism action. -/
module
public import Glennie.Compact.NearbyOrbitsClosed

@[expose] public section
namespace Glennie.Compact.LocalOrbitQuotientR01
noncomputable section
open Glennie Glennie.Compact.Affine20 Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections Glennie.Compact.NearbyOrbits
open Glennie.Compact.FrameTopology
set_option autoImplicit false

/-- All actual ordered triples admitted by the chosen exact local domain. -/
abbrev Admitted (d : LocalData) :=
  {T : Triple // (∀ a : Fin 3, Frame (T a)) ∧ encode20 (fullLedger T) ∈ d.V}

/-- One actual automorphism acts simultaneously on every labeled atom. -/
def orbitSetoid (d : LocalData) : Setoid (Admitted d) where
  r T S := ∃ g : CompactAutomorphism, mapAtoms g T.1 = S.1
  iseqv := by
    constructor
    · intro T
      exact ⟨CompactAutomorphism.refl, mapAtoms_refl T.1⟩
    · intro T S h
      obtain ⟨g, hg⟩ := h
      refine ⟨g.symm, ?_⟩
      rw [← hg, mapAtoms_symm_mapAtoms]
    · intro T S R hTS hSR
      obtain ⟨g, hg⟩ := hTS
      obtain ⟨h, hh⟩ := hSR
      refine ⟨h.comp g, ?_⟩
      rw [← mapAtoms_comp, hg, hh]

abbrev OrbitQuotient (d : LocalData) := Quotient (orbitSetoid d)

instance (d : LocalData) : Setoid (Admitted d) := orbitSetoid d

/-- The chart on all native triples is continuous. -/
theorem continuous_chart :
    Continuous (fun T : Triple => encode20 (fullLedger T)) :=
  continuous_encode20.comp continuous_ledger54

/-- The admitted coordinate, retaining proof that it lies in the exact V. -/
def chart (d : LocalData) (T : Admitted d) : d.V :=
  ⟨encode20 (fullLedger T.1), T.2.2⟩

/-- All admitted actual frame triples belong to the full fibre over their own chart. -/
theorem admitted_mem_fibre (d : LocalData) (T : Admitted d) :
    T.1 ∈ fibre54 (chart d T).1 := ⟨T.2.1, NearbyOrbits.ledger54_eq_decode20 T.2.1 rfl⟩

theorem phi_ne_zero (d : LocalData) (T : Admitted d) : phiOf T.1 ≠ 0 :=
  abs_pos.mp (lt_trans (by norm_num) (d.margin _ T.2.2 (admitted_mem_fibre d T)))

/-- The sign tag has no zero ambiguity anywhere in the admitted domain. -/
def sheet (d : LocalData) (T : Admitted d) : Bool := decide (0 < phiOf T.1)

theorem sheet_true_iff (d : LocalData) (T : Admitted d) :
    sheet d T = true ↔ 0 < phiOf T.1 := by
  simp [sheet]

theorem sheet_false_iff (d : LocalData) (T : Admitted d) :
    sheet d T = false ↔ phiOf T.1 < 0 := by
  grind [sheet, phi_ne_zero]

/-- Actual simultaneous automorphisms preserve both coordinate and Phi. -/
theorem chart_eq_of_rel (d : LocalData) {T S : Admitted d}
    (h : (orbitSetoid d).r T S) : chart d T = chart d S := by
  obtain ⟨g, hg⟩ := h
  apply Subtype.ext
  change encode20 (fullLedger T.1) = encode20 (fullLedger S.1)
  rw [← hg, ledger54_map]

theorem sheet_eq_of_rel (d : LocalData) {T S : Admitted d}
    (h : (orbitSetoid d).r T S) : sheet d T = sheet d S := by
  obtain ⟨g, hg⟩ := h
  simp [sheet, ← hg, phiOf_mapAtoms]

/-- Equal chart and sheet imply an actual automorphism, using whole-fibre cover. -/
theorem rel_of_chart_sheet_eq (d : LocalData) {T S : Admitted d}
    (hc : chart d T = chart d S) (hs : sheet d T = sheet d S) :
    (orbitSetoid d).r T S := by
  apply PairNormNearby.rigid S.property.1 T.property.1
  · exact (admitted_mem_fibre d S).2.trans (hc ▸ (admitted_mem_fibre d T).2.symm)
  · cases h : sheet d T
    · exact Or.inl ⟨(sheet_false_iff ..).mp (hs.symm.trans h), (sheet_false_iff ..).mp h⟩
    · exact Or.inr ⟨(sheet_true_iff ..).mp (hs.symm.trans h), (sheet_true_iff ..).mp h⟩

/-- Thus classification is orbit equivalence, not coordinate equality by definition. -/
theorem rel_iff_chart_sheet_eq (d : LocalData) (T S : Admitted d) :
    (orbitSetoid d).r T S ↔ chart d T = chart d S ∧ sheet d T = sheet d S := by
  grind [chart, sheet, chart_eq_of_rel, sheet_eq_of_rel, rel_of_chart_sheet_eq]

/-- The sign sheet is continuous because the two strict signs exhaust the domain. -/
theorem continuous_sheet (d : LocalData) : Continuous (sheet d) := by
  rw [continuous_bool_rng true]
  have hc : Continuous (fun T : Admitted d => phiOf T.1) :=
    continuous_phiOf.comp continuous_subtype_val
  rw [show sheet d ⁻¹' ({true} : Set Bool) = {T | 0 < phiOf T.1} by ext; simp [sheet]]
  refine ⟨?_, isOpen_lt continuous_const hc⟩
  convert isClosed_le (continuous_const (y := (0:ℝ))) hc using 1
  ext T; exact lt_iff_le_and_ne.trans (and_iff_left (phi_ne_zero d T).symm)

/-- The complete orbit invariant has both a continuous coordinate and a continuous sign. -/
def invariant (d : LocalData) (T : Admitted d) : d.V × Bool :=
  (chart d T, sheet d T)

theorem invariant_eq_of_rel (d : LocalData) {T S : Admitted d}
    (h : (orbitSetoid d).r T S) : invariant d T = invariant d S := Prod.ext (chart_eq_of_rel d h) (sheet_eq_of_rel d h)

theorem continuous_invariant (d : LocalData) : Continuous (invariant d) := by
  apply Continuous.prodMk
  · exact (continuous_chart.comp continuous_subtype_val).subtype_mk _
  exact continuous_sheet d

/-- The forward map is a lift from the actual automorphism-orbit quotient. -/
def forward (d : LocalData) : OrbitQuotient d → d.V × Bool :=
  Quotient.lift (invariant d) (fun _ _ h => invariant_eq_of_rel d h)

theorem continuous_forward (d : LocalData) : Continuous (forward d) :=
  (continuous_invariant d).quotient_lift (fun _ _ h => invariant_eq_of_rel d h)

/-- A continuous choice of a representative on the disjoint pair of chart domains. -/
def select (d : LocalData) : d.V × Bool → Admitted d
  | (b,false) => ⟨d.neg b.val, d.frameNeg _ b.2, (d.chartNeg _ b.2).symm ▸ b.2⟩
  | (b,true) => ⟨d.pos b.val, d.framePos _ b.2, (d.chartPos _ b.2).symm ▸ b.2⟩

theorem continuous_select (d : LocalData) : Continuous (select d) := by
  apply continuous_prod_of_discrete_right.mpr; intro b; cases b
  · exact d.contNeg.domRestrict.subtype_mk _
  · exact d.contPos.domRestrict.subtype_mk _

theorem chart_select (d : LocalData) (z : d.V × Bool) : invariant d (select d z) = z := by
  rcases z with ⟨b,s⟩; cases s
  · exact Prod.ext (Subtype.ext (d.chartNeg _ b.2)) ((sheet_false_iff ..).mpr (d.phiNeg _ b.2))
  · exact Prod.ext (Subtype.ext (d.chartPos _ b.2)) ((sheet_true_iff ..).mpr (d.phiPos _ b.2))

theorem select_rel (d : LocalData) (T : Admitted d) : (orbitSetoid d).r (select d (invariant d T)) T :=
  (rel_iff_chart_sheet_eq ..).mpr (Prod.mk.inj (chart_select d (invariant d T)))

def inverse (d : LocalData) (z : d.V × Bool) : OrbitQuotient d := Quotient.mk' (select d z)

theorem continuous_inverse (d : LocalData) : Continuous (inverse d) := continuous_quotient_mk'.comp (continuous_select d)

theorem forward_inverse (d : LocalData) (z : d.V × Bool) : forward d (inverse d z) = z := chart_select d z

theorem inverse_forward (d : LocalData) (q : OrbitQuotient d) : inverse d (forward d q) = q :=
  Quotient.inductionOn q fun T => Quotient.sound (select_rel d T)

end
end Glennie.Compact.LocalOrbitQuotientR01
