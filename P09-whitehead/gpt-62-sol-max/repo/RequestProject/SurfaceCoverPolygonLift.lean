module

public import RequestProject.SurfaceCoverRelativeRigidity
public import RequestProject.FinsuppBasis
public import RequestProject.SurfaceFundamentalChain
public import RequestProject.OrderNerveDecoding

@[expose] public section

/-! The actual polygon disk lifted from each centre of a surface poset cover. -/
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis
open Comb Cell
variable {κ ι P : Type} {M : ℕ} [NeZero M] [PartialOrder P]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (f : P → SCell vc ec hc) (hf : IsPosetCover f)

/-- A lifted copy of the polygon before its boundary sides are identified.
Different boundary positions may represent different points of the cover. -/
structure CoveredPolygon (v : PolygonCoverPole hc f) where
  V : Fin M → P
  W : Fin M → P
  E : Fin M → P
  D : Fin M → P
  G : Fin M → P
  F : Fin M → P
  R : Fin M → P
  T1 : Fin M → P
  T2 : Fin M → P
  I : Fin M → P
  projV : ∀ p, f (V p) = cV hc p
  projW : ∀ p, f (W p) = cW hc p
  projE : ∀ p, f (E p) = cE hc p
  projD : ∀ p, f (D p) = cD hc p
  projG : ∀ p, f (G p) = cG hc p
  projF : ∀ p, f (F p) = cF hc p
  projR : ∀ p, f (R p) = cR hc p
  projT1 : ∀ p, f (T1 p) = cT1 hc p
  projT2 : ∀ p, f (T2 p) = cT2 hc p
  projI : ∀ p, f (I p) = cI hc p
  ve : ∀ p, V p ≤ E p
  v1e : ∀ p, V (p + 1) ≤ E p
  vd : ∀ p, V p ≤ D p
  wd : ∀ p, W p ≤ D p
  vg : ∀ p, V p ≤ G p
  w1g : ∀ p, W (p + 1) ≤ G p
  wf : ∀ p, W p ≤ F p
  w1f : ∀ p, W (p + 1) ≤ F p
  cr : ∀ p, v.1 ≤ R p
  wr : ∀ p, W p ≤ R p
  et1 : ∀ p, E p ≤ T1 p
  d1t1 : ∀ p, D (p + 1) ≤ T1 p
  gt1 : ∀ p, G p ≤ T1 p
  gt2 : ∀ p, G p ≤ T2 p
  ft2 : ∀ p, F p ≤ T2 p
  dt2 : ∀ p, D p ≤ T2 p
  ri : ∀ p, R p ≤ I p
  fi : ∀ p, F p ≤ I p
  r1i : ∀ p, R (p + 1) ≤ I p

include hf in
/-- Every actual pole determines an actual lifted disk.  Only the proved
unique upper/lower interval lifting of a poset cover is used. -/
theorem exists_coveredPolygon (v : PolygonCoverPole hc f) :
    Nonempty (CoveredPolygon hc f v) := by
  let Fiber (a : SCell vc ec hc) := {x // f x = a}
  let up {a b} (x : Fiber a) (h : a ≤ b) : {y : Fiber b // x.1 ≤ y.1} :=
    let y := hf.liftUp x.1 b (x.2.symm ▸ h)
    ⟨⟨y.1, y.2.2⟩, y.2.1⟩
  let down {a b} (x : Fiber b) (h : a ≤ b) : {y : Fiber a // y.1 ≤ x.1} :=
    let y := hf.dual.liftUp x.1 a (x.2.symm ▸ h)
    ⟨⟨y.1, y.2.2⟩, y.2.1⟩
  have above {a b} {x : Fiber a} {y : Fiber b} {z : P}
      (hx : z ≤ x.1) (hy : z ≤ y.1) (h : a ≤ b) : x.1 ≤ y.1 :=
    hf.le_of_le_above hx hy (x.2.symm ▸ y.2.symm ▸ h)
  have below {a b} {x : Fiber a} {y : Fiber b} {z : P}
      (hx : x.1 ≤ z) (hy : y.1 ≤ z) (h : a ≤ b) : x.1 ≤ y.1 :=
    hf.le_of_le_below hx hy (x.2.symm ▸ y.2.symm ▸ h)
  let R p := up v (cC_le_cR hc p)
  let I (p : Fin M) := up v (show cC hc ≤ cI hc p by tauto)
  have ri p := above (R p).2 (I p).2 (cR_le_cI hc p)
  have r1i p := above (R (p + 1)).2 (I p).2 (cR1_le_cI hc p)
  let W p := down (R p).1 (cW_le_cR hc p)
  let F p := down (I p).1 (cF_le_cI hc p)
  have wf p := below ((W p).2.trans (ri p)) (F p).2 (cW_le_cF hc p)
  have w1f p := below ((W (p + 1)).2.trans (r1i p)) (F p).2 (cW1_le_cF hc p)
  let T2 p := up (F p).1 (cF_le_cT2 hc p)
  let V p := down (T2 p).1 (cV_le_cT2 hc p)
  let D p := down (T2 p).1 (cD_le_cT2 hc p)
  let G p := down (T2 p).1 (cG_le_cT2 hc p)
  have vd p := below (V p).2 (D p).2 (cV_le_cD hc p)
  have wd p := below ((wf p).trans (T2 p).2) (D p).2 (cW_le_cD hc p)
  have vg p := below (V p).2 (G p).2 (cV_le_cG hc p)
  have w1g p := below ((w1f p).trans (T2 p).2) (G p).2 (cW1_le_cG hc p)
  let T1 p := up (G p).1 (cG_le_cT1 hc p)
  have d1t1 p := above (wd (p + 1)) ((w1g p).trans (T1 p).2) (cD1_le_cT1 hc p)
  let E p := down (T1 p).1 (cE_le_cT1 hc p)
  exact ⟨{
    V := fun p => (V p).1.1, W := fun p => (W p).1.1, E := fun p => (E p).1.1,
    D := fun p => (D p).1.1, G := fun p => (G p).1.1, F := fun p => (F p).1.1,
    R := fun p => (R p).1.1, T1 := fun p => (T1 p).1.1, T2 := fun p => (T2 p).1.1,
    I := fun p => (I p).1.1,
    projV := fun p => (V p).1.2, projW := fun p => (W p).1.2,
    projE := fun p => (E p).1.2, projD := fun p => (D p).1.2,
    projG := fun p => (G p).1.2, projF := fun p => (F p).1.2,
    projR := fun p => (R p).1.2, projT1 := fun p => (T1 p).1.2,
    projT2 := fun p => (T2 p).1.2, projI := fun p => (I p).1.2,
    ve := fun p => below ((vg p).trans (T1 p).2) (E p).2 (cV_le_cE hc p),
    v1e := fun p => below ((vd (p + 1)).trans (d1t1 p)) (E p).2 (cV1_le_cE hc p),
    vd := vd, wd := wd, vg := vg, w1g := w1g, wf := wf, w1f := w1f,
    cr := fun p => (R p).2, wr := fun p => (W p).2, et1 := fun p => (E p).2,
    d1t1 := d1t1, gt1 := fun p => (T1 p).2, gt2 := fun p => (G p).2,
    ft2 := fun p => (T2 p).2, dt2 := fun p => (D p).2, ri := ri, fi := fun p => (F p).2,
    r1i := r1i }⟩

noncomputable def coveredPolygon (v : PolygonCoverPole hc f) : CoveredPolygon hc f v :=
  Classical.choice (exists_coveredPolygon hc f hf v)

namespace CoveredPolygon
variable {hc f}
variable {v : PolygonCoverPole hc f} (D : CoveredPolygon hc f v)

noncomputable def sector (p : Fin M) : OrdTri P →₀ ℤ :=
  triangleFlagChain (D.ve p) (D.v1e p) (D.vd (p + 1)) (D.wd (p + 1))
    (D.w1g p) (D.vg p) (D.et1 p) (D.d1t1 p) (D.gt1 p) +
  triangleFlagChain (D.vg p) (D.w1g p) (D.w1f p) (D.wf p)
    (D.wd p) (D.vd p) (D.gt2 p) (D.ft2 p) (D.dt2 p) +
  triangleFlagChain (D.cr p) (D.wr p) (D.wf p) (D.w1f p)
    (D.wr (p + 1)) (D.cr (p + 1)) (D.ri p) (D.fi p) (D.r1i p)

noncomputable def fundamental : OrdTri P →₀ ℤ := ∑ p : Fin M, D.sector p

noncomputable def boundaryEdges : OrdEdge P →₀ ℤ := ∑ p : Fin M, flagEdge (D.ve p) (D.v1e p)

theorem sector_boundary (p : Fin M) :
    Comb.bdry2 (orderCx P) (D.sector p) =
      flagEdge (D.ve p) (D.v1e p) +
      flagEdge (D.vd (p + 1)) (D.wd (p + 1)) - flagEdge (D.vd p) (D.wd p) +
      flagEdge (D.cr p) (D.wr p) - flagEdge (D.cr (p + 1)) (D.wr (p + 1)) := by
  simp only [sector, map_add, bdry_triangleFlagChain, flagEdge]
  abel

/-- All lifted collar and radial terms cancel before any projection. -/
theorem fundamental_boundary : Comb.bdry2 (orderCx P) D.fundamental = D.boundaryEdges := by
  have shift (g : Fin M → OrdEdge P →₀ ℤ) : (∑ p : Fin M, g (p + 1)) = ∑ p : Fin M, g p :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  simp only [fundamental, boundaryEdges, map_sum, sector_boundary, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  erw [shift (fun p => flagEdge (D.vd p) (D.wd p)), shift (fun p => flagEdge (D.cr p) (D.wr p))]
  simp only [orderCx, OrdEdge]
  abel

noncomputable def cellularFundamental : StrictOrdTri P →₀ ℤ := normalizeOrdChain2 D.fundamental

theorem V_ne_E (p q : Fin M) : D.V p ≠ D.E q := by
  intro h
  have hh := (D.projV p).symm.trans ((congrArg f h).trans (D.projE q))
  cases hh

def boundaryEdgeLeft (p : Fin M) : StrictOrdEdge P :=
  ⟨(D.V p, D.E p), lt_of_le_of_ne (D.ve p) (D.V_ne_E p p)⟩

def boundaryEdgeRight (p : Fin M) : StrictOrdEdge P :=
  ⟨(D.V (p + 1), D.E p), lt_of_le_of_ne (D.v1e p) (D.V_ne_E (p + 1) p)⟩

/-- The boundary of the genuine normalized lifted filling consists exactly of
the lifted polygon sides, with their actual endpoints and coefficients. -/
theorem cellularFundamental_boundary : Comb.bdry2 (strictOrderCx P) D.cellularFundamental =
    ∑ p : Fin M, (Finsupp.single (D.boundaryEdgeLeft p) 1 -
      Finsupp.single (D.boundaryEdgeRight p) 1) := by
  erw [cellularFundamental, bdry2_normalizeOrdChain2, D.fundamental_boundary]
  simp [boundaryEdges, flagEdge, normalizeOrdEdge, D.V_ne_E,
    boundaryEdgeLeft, boundaryEdgeRight]

theorem cellularFundamental_relative : PolygonRelativeChain hc f D.cellularFundamental := by
  intro e he
  have hn  :=
    Finsupp.mem_support_iff.mp he
  have hleft (p : Fin M) :
      InPolygonBoundary hc (f (D.boundaryEdgeLeft p).1.1) ∧
        InPolygonBoundary hc (f (D.boundaryEdgeLeft p).1.2) := by
    change InPolygonBoundary hc (f (D.V p)) ∧ InPolygonBoundary hc (f (D.E p))
    erw [D.projV, D.projE]
    exact ⟨trivial, trivial⟩
  have hright (p : Fin M) :
      InPolygonBoundary hc (f (D.boundaryEdgeRight p).1.1) ∧
        InPolygonBoundary hc (f (D.boundaryEdgeRight p).1.2) := by
    change InPolygonBoundary hc (f (D.V (p + 1))) ∧ InPolygonBoundary hc (f (D.E p))
    erw [D.projV, D.projE]
    exact ⟨trivial, trivial⟩
  by_contra hb
  have hneL (p : Fin M) : D.boundaryEdgeLeft p ≠ e := by
    intro hh
    exact hb (hh ▸ hleft p)
  have hneR (p : Fin M) : D.boundaryEdgeRight p ≠ e := by
    intro hh
    exact hb (hh ▸ hright p)
  apply hn
  erw [D.cellularFundamental_boundary]
  simp [hneL, hneR]

variable (hc f)

/-- The chosen lift has coefficient one at its own pole and zero at every
other pole.  This computes the full lifted coefficients before any projection. -/
theorem cellularFundamental_pole_coefficient (hM : 2 ≤ M)
    (u : PolygonCoverPole hc f) :
    D.cellularFundamental (polygonCoverPoleFlag hc f hf u) = if v = u then 1 else 0 := by
  classical
  let t := polygonCoverPoleFlag hc f hf u
  have ht := polygonCoverPoleFlagPlus_projection hc f hf u.1 u.2 0
  change f t.1.1 = cC hc ∧ f t.1.2.1 = cR hc 0 ∧ f t.1.2.2 = cI hc 0 at ht
  have hV (p : Fin M) : D.V p ≠ t.1.1 :=
    fun h => by cases ((D.projV p).symm.trans ((congrArg f h).trans ht.1))
  have hW (p : Fin M) : D.W p ≠ t.1.1 :=
    fun h => by cases ((D.projW p).symm.trans ((congrArg f h).trans ht.1))
  have hI {p : Fin M} (h : D.I p = t.1.2.2) : p = 0 :=
    Cell.inn.inj ((D.projI p).symm.trans ((congrArg f h).trans ht.2.2))
  have hplus (p : Fin M) :
      (v.1 = t.1.1 ∧ D.R p = t.1.2.1 ∧ D.I p = t.1.2.2) ↔ v = u ∧ p = 0 := by
    constructor
    · exact fun h => ⟨Subtype.ext h.1, hI h.2.2⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, hf.up_inj (D.cr 0) t.2.1.le ((D.projR 0).trans ht.2.1.symm),
        hf.up_inj ((D.cr 0).trans (D.ri 0)) (t.2.1.trans t.2.2).le ((D.projI 0).trans ht.2.2.symm)⟩
  have hminus (p : Fin M) :
      ¬ (v.1 = t.1.1 ∧ D.R (p + 1) = t.1.2.1 ∧ D.I p = t.1.2.2) := by
    intro h
    have hp : p + 1 = 0 :=
      Cell.rad.inj ((D.projR (p + 1)).symm.trans ((congrArg f h.2.1).trans ht.2.1))
    exact fin_succ_ne_self hM p (hp.trans (hI h.2.2).symm)
  change D.cellularFundamental t = _
  erw [cellularFundamental, normalizeOrdChain2_apply]
  change D.fundamental ⟨(t.1.1, t.1.2.1, t.1.2.2), t.2.1.le, t.2.2.le⟩ = _
  simp only [fundamental, sector, triangleFlagChain, Finsupp.finsetSum_apply,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply, OrdTri, Subtype.mk.injEq,
    Prod.mk.injEq, hplus, hminus, hV, hW, false_and, if_false, sub_zero, zero_add, add_zero]
  by_cases h : v = u <;> simp [h]

theorem cellularFundamental_pole_coefficients (hM : 2 ≤ M) :
    polygonCoverPoleCoefficients hc f hf D.cellularFundamental = Finsupp.single v 1 := by
  classical
  ext u
  erw [polygonCoverPoleCoefficients_apply,
    CoveredPolygon.cellularFundamental_pole_coefficient hc f hf D hM u]
  grind

end CoveredPolygon

/-- The actual oriented polygon filling attached to one actual pole lift. -/
noncomputable def polygonCoverFilling (v : PolygonCoverPole hc f) : StrictOrdTri P →₀ ℤ :=
  (coveredPolygon hc f hf v).cellularFundamental

theorem polygonCoverFilling_relative (v : PolygonCoverPole hc f) :
    PolygonRelativeChain hc f (polygonCoverFilling hc f hf v) :=
  (coveredPolygon hc f hf v).cellularFundamental_relative

theorem polygonCoverFilling_pole_coefficients (hM : 2 ≤ M) (v : PolygonCoverPole hc f) :
    polygonCoverPoleCoefficients hc f hf (polygonCoverFilling hc f hf v) =
      Finsupp.single v 1 :=
  CoveredPolygon.cellularFundamental_pole_coefficients hc f hf
    (coveredPolygon hc f hf v) hM

/-- Reconstruct a finite relative two-chain from its actual polygon coefficients. -/
noncomputable def polygonCoverReconstruct :
    (PolygonCoverPole hc f →₀ ℤ) →ₗ[ℤ] (StrictOrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ (polygonCoverFilling hc f hf)

theorem polygonCoverReconstruct_relative (a : PolygonCoverPole hc f →₀ ℤ) :
    PolygonRelativeChain hc f (polygonCoverReconstruct hc f hf a) :=
  Finsupp.linearCombination_mem (T := polygonRelativeSubmodule hc f)
    (polygonCoverFilling_relative hc f hf) a

theorem polygonCoverReconstruct_coefficients (hM : 2 ≤ M)
    (a : PolygonCoverPole hc f →₀ ℤ) :
    polygonCoverPoleCoefficients hc f hf (polygonCoverReconstruct hc f hf a) = a := by
  finsupp_basis a
  intro v
  erw [polygonCoverReconstruct, Finsupp.linearCombination_single, map_smul,
    polygonCoverFilling_pole_coefficients hc f hf hM]
  aesop

/-- Every genuine relative two-chain in every actual surface cover is exactly
the finite sum of genuine lifted polygon fillings with its actual pole
coefficients.  All internal flags and the collar are included. -/
theorem polygonRelative_reconstruct (hd : PolygonData vc ec)
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c) :
    c = polygonCoverReconstruct hc f hf (polygonCoverPoleCoefficients hc f hf c) := by
  apply polygonRelative_ext hc hd f hf c _ hrel (polygonCoverReconstruct_relative hc f hf _)
  symm
  apply polygonCoverReconstruct_coefficients hc f hf
  have := hd.three_le
  omega






end FiniteChains.Davis
