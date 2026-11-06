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
abbrev LocalData := Sections.ClassifiedSections

def localData : LocalData :=
  Classical.choice NearbyOrbitsClosed.nearby_fibres_two_orbits_unconditional

/-- All actual ordered triples admitted by the chosen exact local domain. -/
abbrev Admitted (d : LocalData) :=
  {T : Triple // (∀ a : Fin 3, Frame (T a)) ∧ encode20 (ledger54 T) ∈ d.V}

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

/-- The explicit twenty-coordinate chart is continuous on the complete ledger. -/
theorem continuous_chart :
    Continuous (fun T : Triple => encode20 (ledger54 T)) :=
  continuous_encode20.comp continuous_ledger54

/-- The admitted coordinate, retaining proof that it lies in the exact V. -/
def chart (d : LocalData) (T : Admitted d) : d.V :=
  ⟨encode20 (ledger54 T.1), T.2.2⟩

/-- All admitted actual frame triples belong to the full fibre over their own chart. -/
theorem admitted_mem_fibre (d : LocalData) (T : Admitted d) :
    T.1 ∈ fibre54 (chart d T).1 := ⟨T.2.1, NearbyOrbits.ledger54_eq_decode20 T.2.1 rfl⟩

/-- The two chosen sections really land in the entire admitted subtype. -/
def sectionPoint (d : LocalData) (b : d.V) (s : Bool) : Admitted d :=
  if s then ⟨d.pos b.1, d.framePos b.1 b.2, by rw [d.chartPos b.1 b.2]; exact b.2⟩
  else ⟨d.neg b.1, d.frameNeg b.1 b.2, by rw [d.chartNeg b.1 b.2]; exact b.2⟩

/-- The whole-fibre theorem covers every admitted actual triple, not merely section images. -/
theorem admitted_cover (d : LocalData) (T : Admitted d) :
    T.1 ∈ autOrbit (d.neg (chart d T).1) ∪ autOrbit (d.pos (chart d T).1) := by
  rw [← d.cover (chart d T).1 (chart d T).2]
  exact admitted_mem_fibre d T

theorem phi_ne_zero (d : LocalData) (T : Admitted d) : phiOf T.1 ≠ 0 := by
  rcases admitted_cover d T with hn | hp
  · rw [phiOf_eq_of_mem_autOrbit hn]
    exact ne_of_lt (d.phiNeg _ (chart d T).2)
  · rw [phiOf_eq_of_mem_autOrbit hp]
    exact ne_of_gt (d.phiPos _ (chart d T).2)

/-- The sign tag has no zero ambiguity anywhere in the admitted domain. -/
def sheet (d : LocalData) (T : Admitted d) : Bool := decide (0 < phiOf T.1)

/-- The sign sheet is continuous because the two strict signs exhaust the domain. -/
theorem continuous_sheet (d : LocalData) : Continuous (sheet d) := by
  rw [continuous_bool_rng true]
  have hc : Continuous (fun T : Admitted d => phiOf T.1) :=
    continuous_phiOf.comp continuous_subtype_val
  constructor
  · convert isClosed_le (f := fun _ : Admitted d => (0 : ℝ)) continuous_const hc using 1
    ext T
    change (sheet d T = true) ↔ 0 ≤ phiOf T.1
    simp only [sheet, decide_eq_true_eq]
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (Ne.symm (phi_ne_zero d T))⟩
  · change IsOpen {T : Admitted d | sheet d T = true}
    simpa only [sheet, decide_eq_true_eq] using isOpen_lt (f := fun _ : Admitted d => (0 : ℝ)) continuous_const hc

/-- The complete orbit invariant has both a continuous coordinate and a continuous sign. -/
def invariant (d : LocalData) (T : Admitted d) : d.V × Bool :=
  (chart d T, sheet d T)

theorem invariant_eq_of_rel (d : LocalData) {T S : Admitted d}
    (h : (orbitSetoid d).r T S) : invariant d T = invariant d S := by
  obtain ⟨g, hg⟩ := h
  apply Prod.ext
  · apply Subtype.ext
    change encode20 (ledger54 T.1) = encode20 (ledger54 S.1)
    rw [← hg, ledger54_map]
  · simp only [invariant, sheet, ← hg, phiOf_mapAtoms]

theorem rel_iff_invariant_eq (d : LocalData) (T S : Admitted d) :
    (orbitSetoid d).r T S ↔ invariant d T = invariant d S := by
  constructor
  · exact invariant_eq_of_rel d
  · intro h
    have hc := congrArg Prod.fst h
    have hs := congrArg Prod.snd h
    apply NearbyOrbitsClosed.same_sign_rigidity S.1 T.1 S.2.1 T.2.1
    · rw [ledger54_eq_decode20 S.2.1 rfl, ledger54_eq_decode20 T.2.1 rfl]
      exact congrArg decode20 (congrArg Subtype.val hc).symm
    · have hnT := phi_ne_zero d T
      have hnS := phi_ne_zero d S
      simp only [invariant, sheet, decide_eq_decide] at hs
      grind

theorem continuous_invariant (d : LocalData) : Continuous (invariant d) := by
  apply Continuous.prodMk
  · exact (continuous_chart.comp continuous_subtype_val).subtype_mk _
  · exact continuous_sheet d

/-- The forward map is a lift from the actual automorphism-orbit quotient. -/
def forward (d : LocalData) : OrbitQuotient d → d.V × Bool :=
  Quotient.lift (invariant d) (fun _ _ h => invariant_eq_of_rel d h)

theorem continuous_forward (d : LocalData) : Continuous (forward d) :=
  (continuous_invariant d).quotient_lift (fun _ _ h => invariant_eq_of_rel d h)

theorem continuous_sectionPoint (d : LocalData) (s : Bool) :
    Continuous (fun b => sectionPoint d b s) := by
  cases s
  · exact d.contNeg.domRestrict.subtype_mk _
  · exact d.contPos.domRestrict.subtype_mk _

/-- The inverse chooses the actual continuous representative on each discrete sheet. -/
def inverse (d : LocalData) (z : d.V × Bool) : OrbitQuotient d :=
  Quotient.mk' (sectionPoint d z.1 z.2)

theorem continuous_inverse (d : LocalData) : Continuous (inverse d) :=
  continuous_prod_of_discrete_right.mpr fun s =>
    continuous_quotient_mk'.comp (continuous_sectionPoint d s)

/-- The section inverse returns exactly the requested admitted coordinate and sign. -/
theorem forward_inverse (d : LocalData) (z : d.V × Bool) :
    forward d (inverse d z) = z := by
  rcases z with ⟨b, s⟩
  change invariant d (sectionPoint d b s) = (b, s)
  apply Prod.ext
  · apply Subtype.ext
    cases s
    · exact d.chartNeg b.1 b.2
    · exact d.chartPos b.1 b.2
  · cases s
    · exact decide_eq_false_iff_not.mpr (not_lt.mpr (d.phiNeg b.1 b.2).le)
    · exact decide_eq_true_eq.mpr (d.phiPos b.1 b.2)

theorem forward_injective (d : LocalData) : Function.Injective (forward d) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro T S h
  exact Quotient.sound ((rel_iff_invariant_eq d T S).mpr h)

/-- Every quotient point is represented by the section orbit of its chart and sign. -/
theorem inverse_forward (d : LocalData) (q : OrbitQuotient d) :
    inverse d (forward d q) = q := (forward_injective d) (forward_inverse d (forward d q))

end
end Glennie.Compact.LocalOrbitQuotientR01
