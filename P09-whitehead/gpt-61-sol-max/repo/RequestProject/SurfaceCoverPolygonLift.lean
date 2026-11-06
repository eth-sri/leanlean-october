import Mathlib.Tactic

import RequestProject.SurfaceCoverRelativeRigidity
import RequestProject.SurfaceFundamentalChain
import RequestProject.OrderNerveDecoding

/-! The actual polygon disk lifted from each centre of a surface poset cover. -/
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open Comb Cell
variable {κ ι P : Type} {M : ℕ} [NeZero M] [PartialOrder P]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (f : P → SCell vc ec hc) (hf : IsPosetCover f)

/-- A lifted copy of the polygon before its boundary sides are identified.
Different boundary positions may represent different points of the cover. -/
structure CoveredPolygon (v : PolygonCoverPole hc f) where
  (V W E D G F R T1 T2 I : Fin M → P)
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

variable (v : PolygonCoverPole hc f)
include hf in
/-- Every actual pole determines an actual lifted disk.  Only the proved
unique upper/lower interval lifting of a poset cover is used. -/
theorem exists_coveredPolygon  :
    Nonempty (CoveredPolygon hc f v) := by
  classical
  have lup (a : P) (b : SCell vc ec hc) (h : f a ≤ b) := (hf.up a b h).exists
  have ldown (a : P) (b : SCell vc ec hc) (h : b ≤ f a) := (hf.down a b h).exists
  choose R hR hRp using fun p : Fin M => lup v.1 (cR hc p)
    (by simpa only [v.2] using cC_le_cR hc p)
  choose I hI hIp using fun p : Fin M => lup v.1 (cI hc p)
    (by simpa only [v.2] using cC_le_cI hc p)
  have hri (p : Fin M) :=
    hf.le_of_le_above (hR p) (hI p) (by simpa only [(hRp p), (hIp p)] using cR_le_cI hc p)
  have hr1i (p : Fin M) :=
    hf.le_of_le_above (hR (p + 1)) (hI p) (by simpa only [(hRp (p + 1)), (hIp p)] using cR1_le_cI hc p)
  choose W hW hWp using fun p : Fin M => ldown (R p) (cW hc p)
    (by simpa only [(hRp p)] using cW_le_cR hc p)
  choose F hF hFp using fun p : Fin M => ldown (I p) (cF hc p)
    (by simpa only [(hIp p)] using cF_le_cI hc p)
  have hwf (p : Fin M) :=
    hf.le_of_le_below ((hW p).trans (hri p)) (hF p) (by simpa only [(hWp p), (hFp p)] using cW_le_cF hc p)
  have hw1f (p : Fin M) :=
    hf.le_of_le_below ((hW (p + 1)).trans (hr1i p)) (hF p) (by simpa only [(hWp (p + 1)), (hFp p)] using cW1_le_cF hc p)
  choose T2 hT2 hT2p using fun p : Fin M => lup (F p) (cT2 hc p)
    (by simpa only [(hFp p)] using cF_le_cT2 hc p)
  choose V hV hVp using fun p : Fin M => ldown (T2 p) (cV hc p)
    (by simpa only [(hT2p p)] using cV_le_cT2 hc p)
  choose D hD hDp using fun p : Fin M => ldown (T2 p) (cD hc p)
    (by simpa only [(hT2p p)] using cD_le_cT2 hc p)
  choose G hG hGp using fun p : Fin M => ldown (T2 p) (cG hc p)
    (by simpa only [(hT2p p)] using cG_le_cT2 hc p)
  have hvd (p : Fin M) := hf.le_of_le_below (hV p) (hD p) (by simpa only [(hVp p), (hDp p)] using cV_le_cD hc p)
  have hwd (p : Fin M) := hf.le_of_le_below
    ((hwf p).trans (hT2 p)) (hD p) (by simpa only [(hWp p), (hDp p)] using cW_le_cD hc p)
  have hvg (p : Fin M) := hf.le_of_le_below (hV p) (hG p) (by simpa only [(hVp p), (hGp p)] using cV_le_cG hc p)
  have hw1g (p : Fin M) := hf.le_of_le_below
    ((hw1f p).trans (hT2 p)) (hG p) (by simpa only [(hWp (p + 1)), (hGp p)] using cW1_le_cG hc p)
  choose T1 hT1 hT1p using fun p : Fin M => lup (G p) (cT1 hc p)
    (by simpa only [(hGp p)] using cG_le_cT1 hc p)
  have hd1t1 (p : Fin M) := hf.le_of_le_above
    (hwd (p + 1)) ((hw1g p).trans (hT1 p)) (by simpa only [(hDp (p + 1)), (hT1p p)] using cD1_le_cT1 hc p)
  choose E hE hEp using fun p : Fin M => ldown (T1 p) (cE hc p)
    (by simpa only [(hT1p p)] using cE_le_cT1 hc p)
  have hve (p : Fin M) := hf.le_of_le_below
    ((hvg p).trans (hT1 p)) (hE p) (by simpa only [(hVp p), (hEp p)] using cV_le_cE hc p)
  have hv1e (p : Fin M) := hf.le_of_le_below
    ((hvd (p + 1)).trans (hd1t1 p)) (hE p) (by simpa only [(hVp (p + 1)), (hEp p)] using cV1_le_cE hc p)
  exact ⟨⟨V, W, E, D, G, F, R, T1, T2, I,
    hVp, hWp, hEp, hDp, hGp, hFp, hRp, hT1p, hT2p, hIp,
    hve, hv1e, hvd, hwd, hvg, hw1g, hwf, hw1f, hR, hW, hE,
    hd1t1, hT1, hG, hT2, hD, hri, hF, hr1i⟩⟩

noncomputable def coveredPolygon   :=
  Classical.choice (exists_coveredPolygon hc f hf v)

namespace CoveredPolygon
variable {hc f}
variable {v : PolygonCoverPole hc f} (D : CoveredPolygon hc f v)

  (p : Fin M)
def sector   :=
  triangleFlagChain (D.V p) (D.V (p + 1)) (D.W (p + 1))
    (D.E p) (D.D (p + 1)) (D.G p) (D.T1 p) +
  triangleFlagChain (D.V p) (D.W (p + 1)) (D.W p)
    (D.G p) (D.F p) (D.D p) (D.T2 p) +
  triangleFlagChain v.1 (D.W p) (D.W (p + 1))
    (D.R p) (D.F p) (D.R (p + 1)) (D.I p)

def fundamental  := ∑ p : Fin M, D.sector p

abbrev sector_mem_inc   :=
  AddSubgroup.add_mem (FiniteChains.Nerve.Inc P)
    (AddSubgroup.add_mem (FiniteChains.Nerve.Inc P)
      (FiniteChains.Davis.triangleFlagChain_mem_inc (D.ve p) (D.v1e p) (D.vd (p + 1)) (D.wd (p + 1)) (D.w1g p) (D.vg p)
        (D.et1 p) (D.d1t1 p) (D.gt1 p))
      (FiniteChains.Davis.triangleFlagChain_mem_inc (D.vg p) (D.w1g p) (D.w1f p) (D.wf p) (D.wd p) (D.vd p) (D.gt2 p)
        (D.ft2 p) (D.dt2 p)))
    (FiniteChains.Davis.triangleFlagChain_mem_inc (D.cr p) (D.wr p) (D.wf p) (D.w1f p) (D.wr (p + 1)) (D.cr (p + 1))
      (D.ri p) (D.fi p) (D.r1i p))

theorem fundamental_mem_inc : D.fundamental ∈ Nerve.Inc P :=
  (Nerve.Inc _).sum_mem (fun p _ => D.sector_mem_inc p)

theorem fundamental_degree : Nerve.lengthProjection 3 D.fundamental = D.fundamental := by
  simp [fundamental, sector, triangleFlagChain]

theorem sector_boundary  :
    Nerve.bdry (D.sector p) =
      flagEdge (D.V p) (D.V (p + 1)) (D.E p) +
      flagEdge (D.V (p + 1)) (D.W (p + 1)) (D.D (p + 1)) -
      flagEdge (D.V p) (D.W p) (D.D p) +
      flagEdge v.1 (D.W p) (D.R p) -
      flagEdge v.1 (D.W (p + 1)) (D.R (p + 1)) := by
  classical grind [FiniteChains.Davis.bdry_triangleFlagChain, sector, flagEdge]

/-- All lifted collar and radial terms cancel before any projection. -/
theorem fundamental_boundary :
    Nerve.bdry D.fundamental =
      ∑ p : Fin M, flagEdge (D.V p) (D.V (p + 1)) (D.E p) := by
  have hshift (g : Fin M → Nerve.Ch P) : (∑ p : Fin M, g (p + 1)) = ∑ p : Fin M, g p :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin M)) _ _ (fun _ => rfl)
  simp only [fundamental, map_sum, sector_boundary,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw  [hshift (fun p => flagEdge (D.V p) (D.W p) (D.D p)),
    hshift (fun p => flagEdge v.1 (D.W p) (D.R p))]
  abel

noncomputable def cellularFundamental  :=
  normalizeOrdChain2 (decodeOrdNerve2 D.fundamental)

theorem cellularFundamental_coefficient (t : StrictOrdTri P) :
    D.cellularFundamental t = ordTriangleCoefficient ((strictOrderIncl P).onF t)
      D.fundamental := by
  rw  [cellularFundamental, normalizeOrdChain2_apply, ← ordTriangleCoefficient_encode,
    ordNerveChain2_decode D.fundamental_mem_inc, D.fundamental_degree]

noncomputable def boundaryEdges : OrdEdge P →₀ ℤ :=
  ∑ p : Fin M,
    (Finsupp.single ⟨(D.V p, D.E p), D.ve p⟩ 1 -
      Finsupp.single ⟨(D.V (p + 1), D.E p), D.v1e p⟩ 1)

theorem boundaryEdges_encode : ordNerveChain1 D.boundaryEdges =
    ∑ p : Fin M, flagEdge (D.V p) (D.V (p + 1)) (D.E p) := by
  simp [boundaryEdges, ordNerveChain1, flagEdge]

theorem decodedFundamental_boundary :
    Comb.bdry2 (orderCx P) (decodeOrdNerve2 D.fundamental) = D.boundaryEdges := by
  apply ordNerveChain1_injective
  rw  [ordNerveChain1_bdry2, ordNerveChain2_decode D.fundamental_mem_inc,
    D.fundamental_degree, D.fundamental_boundary, D.boundaryEdges_encode]

theorem V_ne_E  : D.V p ≠ D.E p := by
  intro h
  have hh := congrArg f h
  rw  [D.projV, D.projE] at hh
  cases hh

theorem V1_ne_E  : D.V (p + 1) ≠ D.E p := by
  intro h
  have hh := congrArg f h
  rw  [D.projV, D.projE] at hh
  cases hh

def boundaryEdgeLeft  : StrictOrdEdge P :=
  ⟨(D.V p, D.E p), lt_of_le_of_ne (D.ve p) (D.V_ne_E p)⟩

def boundaryEdgeRight  : StrictOrdEdge P :=
  ⟨(D.V (p + 1), D.E p), lt_of_le_of_ne (D.v1e p) (D.V1_ne_E p)⟩

/-- The boundary of the genuine normalized lifted filling consists exactly of
the lifted polygon sides, with their actual endpoints and coefficients. -/
theorem cellularFundamental_boundary : Comb.bdry2 (strictOrderCx P) D.cellularFundamental =
    ∑ p : Fin M, (Finsupp.single (D.boundaryEdgeLeft p) 1 -
      Finsupp.single (D.boundaryEdgeRight p) 1) := by
  rw  [cellularFundamental, bdry2_normalizeOrdChain2, D.decodedFundamental_boundary]
  simp [boundaryEdges, normalizeOrdEdge, D.V_ne_E, D.V1_ne_E,
    boundaryEdgeLeft, boundaryEdgeRight]

theorem cellularFundamental_relative : PolygonRelativeChain hc f D.cellularFundamental := by
  intro e he
  have hn  :=
    Finsupp.mem_support_iff.mp he
  have hleft (p : Fin M) :
      InPolygonBoundary hc (f (D.boundaryEdgeLeft p).1.1) ∧
        InPolygonBoundary hc (f (D.boundaryEdgeLeft p).1.2) := by
    change InPolygonBoundary hc (f (D.V p)) ∧ InPolygonBoundary hc (f (D.E p))
    rw  [D.projV, D.projE]
    exact ⟨trivial, trivial⟩
  have hright (p : Fin M) :
      InPolygonBoundary hc (f (D.boundaryEdgeRight p).1.1) ∧
        InPolygonBoundary hc (f (D.boundaryEdgeRight p).1.2) := by
    change InPolygonBoundary hc (f (D.V (p + 1))) ∧ InPolygonBoundary hc (f (D.E p))
    rw  [D.projV, D.projE]
    exact ⟨trivial, trivial⟩
  by_contra hb
  have hneL (p : Fin M) : D.boundaryEdgeLeft p ≠ e := by
    intro hh
    exact hb (hh ▸ hleft p)
  have hneR (p : Fin M) : D.boundaryEdgeRight p ≠ e := by
    intro hh
    exact hb (hh ▸ hright p)
  apply hn
  rw  [D.cellularFundamental_boundary]
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
  have hv (p : Fin M) : D.V p ≠ t.1.1 := by
    intro h
    have hh := (D.projV p).symm.trans ((congrArg f h).trans ht.1)
    cases hh
  have hw (p : Fin M) : D.W p ≠ t.1.1 := by
    intro h
    have hh := (D.projW p).symm.trans ((congrArg f h).trans ht.1)
    cases hh
  have hplus (p : Fin M) :
      [v.1, D.R p, D.I p] = [t.1.1, t.1.2.1, t.1.2.2] ↔ v = u ∧ p = 0 := by
    constructor
    · intro h
      simp only [List.cons.injEq, and_true] at h
      have hpu : p = 0 := by
        have hh := (D.projI p).symm.trans ((congrArg f h.2.2).trans ht.2.2)
        exact Cell.inn.inj hh
      exact ⟨Subtype.ext h.1, hpu⟩
    · rintro ⟨rfl, rfl⟩
      have hr  := hf.up_inj (D.cr 0) t.2.1.le
        ((D.projR 0).trans ht.2.1.symm)
      have hi  := hf.up_inj ((D.cr 0).trans (D.ri 0))
        (t.2.1.trans t.2.2).le ((D.projI 0).trans ht.2.2.symm)
      simp only [hr, hi]
      rfl
  have hminus (p : Fin M) :
      [v.1, D.R (p + 1), D.I p] ≠ [t.1.1, t.1.2.1, t.1.2.2] := by
    intro h
    simp only [List.cons.injEq, and_true] at h
    have hp : p = 0 := by
      have hh := (D.projI p).symm.trans ((congrArg f h.2.2).trans ht.2.2)
      exact Cell.inn.inj hh
    have hp' : p + 1 = 0 := by
      have hh := (D.projR (p + 1)).symm.trans ((congrArg f h.2.1).trans ht.2.1)
      exact Cell.rad.inj hh
    exact fin_succ_ne_self hM p (hp'.trans hp.symm)
  change D.cellularFundamental t = _
  rw  [D.cellularFundamental_coefficient]
  simp only [fundamental, sector, triangleFlagChain, map_sum, map_add, map_sub,
    ordTriangleCoefficient, FreeAbelianGroup.lift_apply_of, strictOrderIncl]
  simp only [hplus, hminus, if_false]
  simp only [List.cons.injEq, and_true, hv, hw, false_and, if_false,
    sub_zero, zero_add, add_zero]
  by_cases h : v = u <;> simp [h]

theorem cellularFundamental_pole_coefficients (hM : 2 ≤ M) :
    polygonCoverPoleCoefficients hc f hf D.cellularFundamental = Finsupp.single v 1 := by
  classical aesop (add simp [FiniteChains.Davis.polygonCoverPoleCoefficients_apply, FiniteChains.Davis.CoveredPolygon.cellularFundamental_pole_coefficient, Finsupp.single_apply])

end CoveredPolygon

/-- The actual oriented polygon filling attached to one actual pole lift. -/
noncomputable def polygonCoverFilling   :=
  (coveredPolygon hc f hf v).cellularFundamental

theorem polygonCoverFilling_relative  :
    PolygonRelativeChain hc f (polygonCoverFilling hc f hf v) :=
  (coveredPolygon hc f hf v).cellularFundamental_relative

theorem polygonCoverFilling_pole_coefficients (hM : 2 ≤ M) (v : PolygonCoverPole hc f) :
    polygonCoverPoleCoefficients hc f hf (polygonCoverFilling hc f hf v) =
      Finsupp.single v 1 :=
  CoveredPolygon.cellularFundamental_pole_coefficients hc f hf
    (coveredPolygon hc f hf v) hM

/-- Reconstruct a finite relative two-chain from its actual polygon coefficients. -/
noncomputable def polygonCoverReconstruct  :=
  Finsupp.linearCombination ℤ (polygonCoverFilling hc f hf)

theorem polygonCoverReconstruct_relative (a : PolygonCoverPole hc f →₀ ℤ) :
    PolygonRelativeChain hc f (polygonCoverReconstruct hc f hf a) := by
  induction a using Finsupp.induction_linear with
  | zero => simp_all [FiniteChains.Davis.PolygonRelativeChain.zero]
  | add a b ha hb =>
    simp_all [FiniteChains.Davis.PolygonRelativeChain.add]
  | single v n =>
    simp_all [FiniteChains.Davis.PolygonRelativeChain.smul, FiniteChains.Davis.polygonCoverFilling_relative, polygonCoverReconstruct]

theorem polygonCoverReconstruct_coefficients (hM : 2 ≤ M)
    (a : PolygonCoverPole hc f →₀ ℤ) :
    polygonCoverPoleCoefficients hc f hf (polygonCoverReconstruct hc f hf a) = a := by
  induction a using Finsupp.induction_linear <;> simp_all [polygonCoverReconstruct, polygonCoverFilling_pole_coefficients]

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
