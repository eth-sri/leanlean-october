/- Genuine quotient topology of the admitted local ordered-frame domain by the
actual simultaneous product-and-trace automorphism action. -/
module
public import Glennie.Compact.NearbyOrbitsClosed
@[expose] public section
namespace Glennie.SubmissionR04Quotient
noncomputable section
open Glennie.Compact.Affine20 Glennie.SubmissionR03

abbrev ChartPoint := Fin 20 → ℝ

/-- Admission requires actual ordered frames and the exact centered chart. -/
abbrev Admitted (V : Set ChartPoint) :=
  {T : Triple // (IsFrameTriple T) ∧
    Glennie.SubmissionR03.encode20 (fullLedger T) ∈ V}

def invariant (V : Set ChartPoint) (T : Admitted V) : V × Bool :=
  (⟨Glennie.SubmissionR03.encode20 (fullLedger T.1), T.2.2⟩,
    decide (0 < phiOf T.1))

/-- One actual simultaneous product-and-trace automorphism, on fixed labels. -/
def orbitSetoid (V : Set ChartPoint) : Setoid (Admitted V) where
  r T S := ∃ g : CompactAutomorphism, Glennie.SubmissionR03.mapAtoms g T.1 = S.1
  iseqv := by
    constructor
    · intro T
      exact ⟨NativeAction.refl, by funext a i; rfl⟩
    · intro T S h
      obtain ⟨g, hg⟩ := h
      refine ⟨NativeAction.symm g, ?_⟩
      rw [← hg]
      funext a i
      exact g.equiv.symm_apply_apply (T.1 a i)
    · intro T S R hTS hSR
      obtain ⟨g, hg⟩ := hTS
      obtain ⟨h, hh⟩ := hSR
      refine ⟨NativeAction.comp h g, ?_⟩
      rw [← hh, ← hg]
      rfl

abbrev OrbitQuotient (V : Set ChartPoint) := Quotient (orbitSetoid V)
end
end Glennie.SubmissionR04Quotient

namespace Glennie.Compact.LocalOrbitQuotientR01
noncomputable section
open Glennie Glennie.Compact.Affine20 Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections Glennie.Compact.NearbyOrbits
open Glennie.Compact.FrameTopology Glennie.Compact.NearbyOrbitsClosed Glennie.Compact.PairNormNearby
set_option autoImplicit false

abbrev Admitted (d : LocalData) := SubmissionR04Quotient.Admitted d.V
abbrev orbitSetoid (d : LocalData) := SubmissionR04Quotient.orbitSetoid d.V
abbrev OrbitQuotient (d : LocalData) := SubmissionR04Quotient.OrbitQuotient d.V

instance (d : LocalData) : Setoid (Admitted d) := orbitSetoid d

/-- The chart on all native triples is continuous. -/
theorem continuous_chart :
    Continuous (fun T : Triple => encode20 (ledger54 T)) :=
  continuous_encode20.comp continuous_ledger54

/-- The admitted coordinate, retaining proof that it lies in the exact V. -/
def chart (d : LocalData) (T : Admitted d) : d.V :=
  ⟨encode20 (ledger54 T.1), T.2.2⟩

/-- All admitted actual frame triples belong to the full fibre over their own chart. -/
theorem admitted_mem_fibre (d : LocalData) (T : Admitted d) :
    T.1 ∈ fibre54 (chart d T).1 := by
  exact ⟨T.2.1, NearbyOrbits.ledger54_eq_decode20 T.2.1 rfl⟩

theorem phi_ne_zero (d : LocalData) (T : Admitted d) : phiOf T.1 ≠ 0 :=
  abs_pos.mp (lt_trans (by norm_num) (d.margin T.2.1 T.2.2))

/-- The sign tag has no zero ambiguity anywhere in the admitted domain. -/
def sheet (d : LocalData) (T : Admitted d) : Bool := decide (0 < phiOf T.1)

theorem sheet_true_iff (d : LocalData) (T : Admitted d) :
    sheet d T = true ↔ 0 < phiOf T.1 := by
  simp [sheet]

theorem sheet_false_iff (d : LocalData) (T : Admitted d) :
    sheet d T = false ↔ phiOf T.1 < 0 := by
  rw [sheet, decide_eq_false_iff_not, not_lt, le_iff_lt_or_eq]
  simp [phi_ne_zero d T]

theorem rel_of_chart_sheet_eq (d : LocalData) {T S : Admitted d}
    (hc : chart d T = chart d S) (hs : sheet d T = sheet d S) :
    (orbitSetoid d).r T S := by
  refine orbit_of_same_sign _ _ S.2.1 T.2.1
    ((admitted_mem_fibre d S).2.trans (hc ▸ (admitted_mem_fibre d T).2.symm)) ?_
  cases h : sheet d T
  · exact Or.inl ⟨(sheet_false_iff d S).1 (hs.symm.trans h), (sheet_false_iff d T).1 h⟩
  · exact Or.inr ⟨(sheet_true_iff d S).1 (hs.symm.trans h), (sheet_true_iff d T).1 h⟩

abbrev invariant (d : LocalData) := SubmissionR04Quotient.invariant d.V

theorem invariant_apply (d : LocalData) (T : Admitted d) :
    invariant d T = (chart d T, sheet d T) := rfl

/-- The complete invariant classifies the actual automorphism relation. -/
theorem rel_iff_invariant (d : LocalData) (T S : Admitted d) :
    (orbitSetoid d).r T S ↔ invariant d T = invariant d S := by
  simp only [invariant_apply, Prod.mk.injEq]
  refine ⟨?_, fun h => rel_of_chart_sheet_eq d h.1 h.2⟩
  rintro ⟨g, hg⟩
  refine ⟨Subtype.ext ?_, ?_⟩
  · change encode20 (ledger54 T.1) = encode20 (ledger54 S.1)
    rw [← hg, ledger54_map]
  · simp only [sheet, ← hg, phiOf_mapAtoms]

/-- The sign sheet is continuous because the two strict signs exhaust the domain. -/
theorem continuous_sheet (d : LocalData) : Continuous (sheet d) := by
  apply continuous_discrete_rng.mpr
  have hc : Continuous (fun T : Admitted d => phiOf T.1) :=
    continuous_phiOf.comp continuous_subtype_val
  rintro (_ | _)
  · convert isOpen_lt hc continuous_const using 1
    ext T; exact sheet_false_iff d T
  · convert isOpen_lt continuous_const hc using 1
    ext T; exact sheet_true_iff d T

theorem continuous_invariant (d : LocalData) : Continuous (invariant d) := by
  apply Continuous.prodMk
  · exact (continuous_chart.comp continuous_subtype_val).subtype_mk _
  · exact continuous_sheet d

/-- The forward map is a lift from the actual automorphism-orbit quotient. -/
def forward (d : LocalData) : OrbitQuotient d → d.V × Bool :=
  Quotient.lift (invariant d) (fun _ _ h => (rel_iff_invariant d _ _).mp h)

theorem continuous_forward (d : LocalData) : Continuous (forward d) :=
  (continuous_invariant d).quotient_lift (fun _ _ h => (rel_iff_invariant d _ _).mp h)

/-- The chosen representative on a sheet, with admission included. -/
def branch (d : LocalData) (b : d.V) (s : Bool) : Admitted d :=
  if s then ⟨d.pos b, d.framePos b b.2, (d.chartPos b b.2).symm ▸ b.2⟩
  else ⟨d.neg b, d.frameNeg b b.2, (d.chartNeg b b.2).symm ▸ b.2⟩

theorem invariant_branch (d : LocalData) (b : d.V) (s : Bool) :
    invariant d (branch d b s) = (b,s) := by
  cases s <;> simp [invariant_apply, branch, chart, sheet,
    d.chartPos _ b.2, d.chartNeg _ b.2, d.phiPos _ b.2, (d.phiNeg _ b.2).not_gt]

theorem branch_rel (d : LocalData) (T : Admitted d) :
    (orbitSetoid d).r (branch d (chart d T) (sheet d T)) T :=
  (rel_iff_invariant d _ _).mpr (invariant_branch d _ _)

theorem continuous_branch (d : LocalData) (s : Bool) : Continuous (fun b => branch d b s) := by
  cases s
  · exact d.contNeg.domRestrict.subtype_mk _
  · exact d.contPos.domRestrict.subtype_mk _

def inverse (d : LocalData) (z : d.V × Bool) : OrbitQuotient d :=
  Quotient.mk' (branch d z.1 z.2)

theorem continuous_inverse (d : LocalData) : Continuous (inverse d) :=
  continuous_prod_of_discrete_right.mpr fun s => continuous_quotient_mk'.comp (continuous_branch d s)

theorem forward_inverse (d : LocalData) (z : d.V × Bool) : forward d (inverse d z) = z :=
  invariant_branch d z.1 z.2

theorem inverse_forward (d : LocalData) (q : OrbitQuotient d) : inverse d (forward d q) = q :=
  Quotient.inductionOn q fun T => Quotient.sound (branch_rel d T)

end
end Glennie.Compact.LocalOrbitQuotientR01
