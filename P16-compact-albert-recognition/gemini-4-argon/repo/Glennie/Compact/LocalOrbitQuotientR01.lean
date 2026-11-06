module
public import Glennie.Compact.NearbyOrbitsClosed
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Order.Compact

@[expose] public section
namespace Glennie.Compact.LocalOrbitQuotientR01
noncomputable section
open Glennie Glennie.Compact.Affine20 Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections Glennie.Compact.NearbyOrbits
open Glennie.Compact.FrameTopology Glennie.Compact.NativeQFamilyLedger
set_option autoImplicit false

abbrev ChartPoint := Fin 20 → ℝ

structure LocalData where
  V : Set ChartPoint
  openV : IsOpen V
  base : encode20 (ledger54 flatBase) ∈ V
  pos : ChartPoint → Triple
  neg : ChartPoint → Triple
  contPos : ContinuousOn pos V
  contNeg : ContinuousOn neg V
  framePos : ∀ b ∈ V, ∀ a : Fin 3, Frame (pos b a)
  frameNeg : ∀ b ∈ V, ∀ a : Fin 3, Frame (neg b a)
  chartPos : ∀ b ∈ V, encode20 (ledger54 (pos b)) = b
  chartNeg : ∀ b ∈ V, encode20 (ledger54 (neg b)) = b
  phiPos : ∀ b ∈ V, 0 < phiOf (pos b)
  phiNeg : ∀ b ∈ V, phiOf (neg b) < 0
  cover : ∀ b ∈ V, fibre54 b = autOrbit (neg b) ∪ autOrbit (pos b)

theorem exists_localData : Nonempty LocalData := by
  obtain ⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, _, _, hpp, hnn, hcover, _, _⟩ :=
    NearbyOrbitsClosed.nearby_fibres_two_orbits_unconditional
  exact ⟨⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, hpp, hnn, hcover⟩⟩

def localData : LocalData := Classical.choice exists_localData

abbrev Admitted (d : LocalData) :=
  {T : Triple // (∀ a : Fin 3, Frame (T a)) ∧ encode20 (ledger54 T) ∈ d.V}

def orbitSetoid (d : LocalData) : Setoid (Admitted d) where
  r T S := ∃ g : CompactAutomorphism, mapAtoms g T.1 = S.1
  iseqv := ⟨fun T => ⟨CompactAutomorphism.refl, mapAtoms_refl T.1⟩,
    fun ⟨g, hg⟩ => ⟨g.symm, by rw [← hg, mapAtoms_symm_mapAtoms]⟩,
    fun ⟨g, hg⟩ ⟨h, hh⟩ => ⟨h.comp g, by rw [← mapAtoms_comp, hg, hh]⟩⟩

abbrev OrbitQuotient (d : LocalData) := Quotient (orbitSetoid d)
instance (d : LocalData) : Setoid (Admitted d) := orbitSetoid d

theorem continuous_chart : Continuous (fun T : Triple => encode20 (ledger54 T)) :=
  NearbyOrbitsClosed.continuous_encode20.comp continuous_ledger54

def chart (d : LocalData) (T : Admitted d) : d.V := ⟨encode20 (ledger54 T.1), T.2.2⟩

theorem admitted_mem_fibre (d : LocalData) (T : Admitted d) : T.1 ∈ fibre54 (chart d T).1 :=
  ⟨T.2.1, NearbyOrbits.ledger54_eq_decode20 T.2.1 rfl⟩

def posSection (d : LocalData) (b : d.V) : Admitted d :=
  ⟨d.pos b.1, d.framePos b.1 b.2, by rw [d.chartPos b.1 b.2]; exact b.2⟩

def negSection (d : LocalData) (b : d.V) : Admitted d :=
  ⟨d.neg b.1, d.frameNeg b.1 b.2, by rw [d.chartNeg b.1 b.2]; exact b.2⟩

theorem chart_posSection (d : LocalData) (b : d.V) : chart d (posSection d b) = b :=
  Subtype.ext (d.chartPos b.1 b.2)

theorem chart_negSection (d : LocalData) (b : d.V) : chart d (negSection d b) = b :=
  Subtype.ext (d.chartNeg b.1 b.2)

theorem admitted_cover (d : LocalData) (T : Admitted d) :
    T.1 ∈ autOrbit (d.neg (chart d T).1) ∪ autOrbit (d.pos (chart d T).1) := by
  rw [← d.cover (chart d T).1 (chart d T).2]; exact admitted_mem_fibre d T

theorem phi_ne_zero (d : LocalData) (T : Admitted d) : phiOf T.1 ≠ 0 := by
  rcases admitted_cover d T with hn | hp
  · rw [phiOf_eq_of_mem_autOrbit hn]; exact ne_of_lt (d.phiNeg _ (chart d T).2)
  · rw [phiOf_eq_of_mem_autOrbit hp]; exact ne_of_gt (d.phiPos _ (chart d T).2)

theorem mem_pos_of_phi_pos (d : LocalData) (T : Admitted d)
    (h : 0 < phiOf T.1) : T.1 ∈ autOrbit (d.pos (chart d T).1) := by
  rcases admitted_cover d T with hn | hp
  · linarith [phiOf_eq_of_mem_autOrbit hn, d.phiNeg _ (chart d T).2]
  · exact hp

theorem mem_neg_of_phi_neg (d : LocalData) (T : Admitted d)
    (h : phiOf T.1 < 0) : T.1 ∈ autOrbit (d.neg (chart d T).1) := by
  rcases admitted_cover d T with hn | hp
  · exact hn
  · linarith [phiOf_eq_of_mem_autOrbit hp, d.phiPos _ (chart d T).2]

def sheet (d : LocalData) (T : Admitted d) : Bool := decide (0 < phiOf T.1)

theorem sheet_true_iff (d : LocalData) (T : Admitted d) :
    sheet d T = true ↔ 0 < phiOf T.1 := by simp [sheet]

theorem sheet_false_iff (d : LocalData) (T : Admitted d) :
    sheet d T = false ↔ phiOf T.1 < 0 := by
  simp only [sheet, decide_eq_false_iff_not]
  exact ⟨fun h => lt_of_le_of_ne (le_of_not_gt h) (phi_ne_zero d T), fun h => not_lt.mpr h.le⟩

theorem chart_eq_of_rel (d : LocalData) {T S : Admitted d}
    (h : (orbitSetoid d).r T S) : chart d T = chart d S := by
  obtain ⟨g, hg⟩ := h; apply Subtype.ext
  change encode20 (ledger54 T.1) = encode20 (ledger54 S.1); rw [← hg, ledger54_map]

theorem sheet_eq_of_rel (d : LocalData) {T S : Admitted d}
    (h : (orbitSetoid d).r T S) : sheet d T = sheet d S := by
  obtain ⟨g, hg⟩ := h; simp only [sheet, ← hg, phiOf_mapAtoms]

theorem rel_of_chart_sheet_eq (d : LocalData) {T S : Admitted d}
    (hc : chart d T = chart d S) (hs : sheet d T = sheet d S) :
    (orbitSetoid d).r T S := by
  by_cases hp : 0 < phiOf T.1
  · have hpS : 0 < phiOf S.1 := (sheet_true_iff d S).1 (hs.symm.trans ((sheet_true_iff d T).2 hp))
    change S.1 ∈ autOrbit T.1
    rw [autOrbit_eq_of_mem (mem_pos_of_phi_pos d T hp), hc]
    exact mem_pos_of_phi_pos d S hpS
  · have hsT : sheet d T = false := by simp [sheet, hp]
    have hnS : phiOf S.1 < 0 := (sheet_false_iff d S).1 (hs.symm.trans hsT)
    change S.1 ∈ autOrbit T.1
    rw [autOrbit_eq_of_mem (mem_neg_of_phi_neg d T ((sheet_false_iff d T).1 hsT)), hc]
    exact mem_neg_of_phi_neg d S hnS

theorem rel_iff_chart_sheet_eq (d : LocalData) (T S : Admitted d) :
    (orbitSetoid d).r T S ↔ chart d T = chart d S ∧ sheet d T = sheet d S :=
  ⟨fun h => ⟨chart_eq_of_rel d h, sheet_eq_of_rel d h⟩, fun ⟨hc, hs⟩ => rel_of_chart_sheet_eq d hc hs⟩

theorem continuous_sheet (d : LocalData) : Continuous (sheet d) := by
  rw [continuous_bool_rng true]
  have hc : Continuous (fun T : Admitted d => phiOf T.1) := continuous_phiOf.comp continuous_subtype_val
  have hpreeq : sheet d ⁻¹' ({true} : Set Bool) = {T : Admitted d | 0 < phiOf T.1} := by ext T; simp [sheet]
  have hcompeq : ({T : Admitted d | 0 < phiOf T.1} : Set (Admitted d))ᶜ = {T : Admitted d | phiOf T.1 < 0} := by
    ext T; simp [← sheet_true_iff d T, ← sheet_false_iff d T]
  rw [hpreeq]
  exact ⟨isOpen_compl_iff.mp (hcompeq.symm ▸ isOpen_lt hc continuous_const), isOpen_lt continuous_const hc⟩

def invariant (d : LocalData) (T : Admitted d) : d.V × Bool := (chart d T, sheet d T)

theorem invariant_eq_of_rel (d : LocalData) {T S : Admitted d}
    (h : (orbitSetoid d).r T S) : invariant d T = invariant d S :=
  Prod.ext (chart_eq_of_rel d h) (sheet_eq_of_rel d h)

theorem continuous_invariant (d : LocalData) : Continuous (invariant d) :=
  Continuous.prodMk ((continuous_chart.comp continuous_subtype_val).subtype_mk _) (continuous_sheet d)

def forward (d : LocalData) : OrbitQuotient d → d.V × Bool :=
  Quotient.lift (invariant d) (fun _ _ h => invariant_eq_of_rel d h)

theorem continuous_forward (d : LocalData) : Continuous (forward d) :=
  (continuous_invariant d).quotient_lift (fun _ _ h => invariant_eq_of_rel d h)

theorem continuous_posSection (d : LocalData) : Continuous (posSection d) :=
  d.contPos.domRestrict.subtype_mk _

theorem continuous_negSection (d : LocalData) : Continuous (negSection d) :=
  d.contNeg.domRestrict.subtype_mk _

def inverse (d : LocalData) (z : d.V × Bool) : OrbitQuotient d :=
  if z.2 then Quotient.mk' (posSection d z.1) else Quotient.mk' (negSection d z.1)

theorem continuous_inverse (d : LocalData) : Continuous (inverse d) := by
  have hp : Continuous (fun b : d.V => (Quotient.mk' (posSection d b) : OrbitQuotient d)) :=
    continuous_quotient_mk'.comp (continuous_posSection d)
  have hn : Continuous (fun b : d.V => (Quotient.mk' (negSection d b) : OrbitQuotient d)) :=
    continuous_quotient_mk'.comp (continuous_negSection d)
  apply continuous_prod_of_discrete_right.mpr
  rintro (_ | _)
  · simpa [inverse] using hn
  · simpa [inverse] using hp

theorem forward_inverse (d : LocalData) (z : d.V × Bool) :
    forward d (inverse d z) = z := by
  rcases z with ⟨b, _ | _⟩ <;> simp only [inverse, forward, ↓reduceIte]
  · exact Prod.ext (chart_negSection d b) ((sheet_false_iff d (negSection d b)).2 (d.phiNeg b.1 b.2))
  · exact Prod.ext (chart_posSection d b) ((sheet_true_iff d (posSection d b)).2 (d.phiPos b.1 b.2))

theorem inverse_forward (d : LocalData) (q : OrbitQuotient d) :
    inverse d (forward d q) = q := by
  refine Quotient.inductionOn q fun T => ?_
  by_cases hp : 0 < phiOf T.1
  · have hs : sheet d T = true := (sheet_true_iff d T).2 hp
    simp only [forward, inverse, Quotient.lift_mk, invariant, hs, ↓reduceIte]
    exact Quotient.sound (mem_pos_of_phi_pos d T hp)
  · have hs : sheet d T = false := by simp [sheet, hp]
    simp only [forward, inverse, Quotient.lift_mk, invariant, hs]
    exact Quotient.sound (mem_neg_of_phi_neg d T ((sheet_false_iff d T).1 hs))

def branchSection (d : LocalData) (b : d.V) (s : Bool) : Triple :=
  if s then d.pos b.1 else d.neg b.1

theorem continuous_section (d : LocalData) (s : Bool) :
    Continuous (fun b : d.V => branchSection d b s) := by
  cases s
  · exact d.contNeg.domRestrict
  · exact d.contPos.domRestrict

theorem mem_section_orbit (d : LocalData) (T : Admitted d) :
    T.1 ∈ autOrbit (branchSection d (chart d T) (sheet d T)) := by
  cases hs : sheet d T
  · simpa [branchSection, hs] using mem_neg_of_phi_neg d T ((sheet_false_iff d T).1 hs)
  · simpa [branchSection, hs] using mem_pos_of_phi_pos d T ((sheet_true_iff d T).1 hs)

theorem norm_mapAtoms_sub (g : CompactAutomorphism) (T S : Triple) :
    ‖mapAtoms g T - mapAtoms g S‖ = ‖T - S‖ := by
  have hnn (x : Albert) : ‖g.equiv x‖₊ = ‖x‖₊ := NNReal.eq (by
    change ‖g.equiv x‖ = ‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), native_norm_sq, native_norm_sq, g.inner_map])
  simp only [Pi.norm_def, Pi.nnnorm_def, mapAtoms, Pi.sub_apply, ← map_sub, hnn]

theorem compact_feasible_recovery (d : LocalData) (K : Set d.V) (hK : IsCompact K)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ η > 0, ∀ T : Admitted d, chart d T ∈ K → ∀ b : d.V, b ∈ K →
      dist (chart d T) b < η → ∃ g : CompactAutomorphism,
        ‖T.1 - mapAtoms g (branchSection d b (sheet d T))‖ < ζ := by
  obtain ⟨ηp, hηp, hp⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (continuous_section d true).continuousOn) ζ hζ
  obtain ⟨ηn, hηn, hn⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (continuous_section d false).continuousOn) ζ hζ
  refine ⟨min ηp ηn, lt_min hηp hηn, fun T hT b hb hdist => ?_⟩
  obtain ⟨g, hg⟩ := mem_section_orbit d T
  refine ⟨g, ?_⟩
  rw [← hg, norm_mapAtoms_sub]
  cases sheet d T
  · simpa only [dist_eq_norm] using hn _ hT b hb (lt_of_lt_of_le hdist (min_le_right _ _))
  · simpa only [dist_eq_norm] using hp _ hT b hb (lt_of_lt_of_le hdist (min_le_left _ _))

theorem compact_response_margin (d : LocalData) (K : Set d.V) (hK : IsCompact K) :
    ∃ m > 0, ∀ T : Admitted d, chart d T ∈ K → m ≤ |phiOf T.1| := by
  have hcPos := (continuous_phiOf.comp (continuous_section d true)).abs
  have hcNeg := (continuous_phiOf.comp (continuous_section d false)).abs
  obtain ⟨mp, hmp, hp⟩ := hK.exists_forall_le' hcPos.continuousOn
    (fun b _ => by simp only [Function.comp_apply, branchSection, ↓reduceIte]; exact abs_pos.mpr (ne_of_gt (d.phiPos b.1 b.2)))
  obtain ⟨mn, hmn, hn⟩ := hK.exists_forall_le' hcNeg.continuousOn
    (fun b _ => by simp only [Function.comp_apply, branchSection, Bool.false_eq_true, ↓reduceIte]; exact abs_pos.mpr (ne_of_lt (d.phiNeg b.1 b.2)))
  refine ⟨min mp mn, lt_min hmp hmn, fun T hT => ?_⟩
  rw [phiOf_eq_of_mem_autOrbit (mem_section_orbit d T)]
  cases hs : sheet d T
  · exact (min_le_right mp mn).trans (by simpa only [Function.comp_apply, hs] using hn (chart d T) hT)
  · exact (min_le_left mp mn).trans (by simpa only [Function.comp_apply, hs] using hp (chart d T) hT)

end
end Glennie.Compact.LocalOrbitQuotientR01
