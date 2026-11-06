module

public import RequestProject.SurfaceCoverRelativeRigidity
public import RequestProject.SurfaceFundamentalChain
public import RequestProject.OrderNerveDecoding

@[expose] public section

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis
open Comb Cell
variable {κ ι P : Type} {M : ℕ} [NeZero M] [PartialOrder P]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (f : P → SCell vc ec hc) (hf : IsPosetCover f)

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

def coveredPolygon (v : PolygonCoverPole hc f) : CoveredPolygon hc f v :=
  Classical.choice <| by
    have lup (a : P) (b : SCell vc ec hc) (h : f a ≤ b) := (hf.up a b h).exists
    have ldown (a : P) (b : SCell vc ec hc) (h : b ≤ f a) := (hf.down a b h).exists
    choose R hR1 hR2 using fun p => lup v.1 (cR hc p) (by erw [v.2]; exact cC_le_cR hc p)
    choose I hI1 hI2 using fun p => lup v.1 (cI hc p) (by erw [v.2]; exact (ctr_lt_inn hc p).le)
    have hri (p) := hf.le_of_le_above (hR1 p) (hI1 p) (by erw [hR2, hI2]; exact cR_le_cI hc p)
    have hr1i (p) := hf.le_of_le_above (hR1 (p + 1)) (hI1 p) (by erw [hR2, hI2]; exact cR1_le_cI hc p)
    choose W hW1 hW2 using fun p => ldown (R p) (cW hc p) (by erw [hR2]; exact cW_le_cR hc p)
    choose F hF1 hF2 using fun p => ldown (I p) (cF hc p) (by erw [hI2]; exact cF_le_cI hc p)
    have hwf (p) := hf.le_of_le_below ((hW1 p).trans (hri p)) (hF1 p) (by erw [hW2, hF2]; exact cW_le_cF hc p)
    have hw1f (p) := hf.le_of_le_below ((hW1 (p + 1)).trans (hr1i p)) (hF1 p) (by erw [hW2, hF2]; exact cW1_le_cF hc p)
    choose T2 hT21 hT22 using fun p => lup (F p) (cT2 hc p) (by erw [hF2]; exact cF_le_cT2 hc p)
    choose V hV1 hV2 using fun p => ldown (T2 p) (cV hc p) (by erw [hT22]; exact cV_le_cT2 hc p)
    choose D hD1 hD2 using fun p => ldown (T2 p) (cD hc p) (by erw [hT22]; exact cD_le_cT2 hc p)
    choose G hG1 hG2 using fun p => ldown (T2 p) (cG hc p) (by erw [hT22]; exact cG_le_cT2 hc p)
    have hvd (p) := hf.le_of_le_below (hV1 p) (hD1 p) (by erw [hV2, hD2]; exact cV_le_cD hc p)
    have hwd (p) := hf.le_of_le_below ((hwf p).trans (hT21 p)) (hD1 p) (by erw [hW2, hD2]; exact cW_le_cD hc p)
    have hvg (p) := hf.le_of_le_below (hV1 p) (hG1 p) (by erw [hV2, hG2]; exact cV_le_cG hc p)
    have hw1g (p) := hf.le_of_le_below ((hw1f p).trans (hT21 p)) (hG1 p) (by erw [hW2, hG2]; exact cW1_le_cG hc p)
    choose T1 hT11 hT12 using fun p => lup (G p) (cT1 hc p) (by erw [hG2]; exact cG_le_cT1 hc p)
    have hd1t1 (p) := hf.le_of_le_above (hwd (p + 1)) ((hw1g p).trans (hT11 p)) (by erw [hD2, hT12]; exact cD1_le_cT1 hc p)
    choose E hE1 hE2 using fun p => ldown (T1 p) (cE hc p) (by erw [hT12]; exact cE_le_cT1 hc p)
    have hve (p) := hf.le_of_le_below ((hvg p).trans (hT11 p)) (hE1 p) (by erw [hV2, hE2]; exact cV_le_cE hc p)
    have hv1e (p) := hf.le_of_le_below ((hvd (p + 1)).trans (hd1t1 p)) (hE1 p) (by erw [hV2, hE2]; exact cV1_le_cE hc p)
    exact ⟨⟨V, W, E, D, G, F, R, T1, T2, I, hV2, hW2, hE2, hD2, hG2, hF2, hR2, hT12, hT22, hI2,
      hve, hv1e, hvd, hwd, hvg, hw1g, hwf, hw1f, hR1, hW1, hE1, hd1t1, hT11, hG1, hT21, hD1, hri, hF1, hr1i⟩⟩

namespace CoveredPolygon
variable {hc f} {v : PolygonCoverPole hc f} (D : CoveredPolygon hc f v)

def sector (p : Fin M) : Nerve.Ch P :=
  triangleFlagChain (D.V p) (D.V (p + 1)) (D.W (p + 1))
    (D.E p) (D.D (p + 1)) (D.G p) (D.T1 p) +
  triangleFlagChain (D.V p) (D.W (p + 1)) (D.W p)
    (D.G p) (D.F p) (D.D p) (D.T2 p) +
  triangleFlagChain v.1 (D.W p) (D.W (p + 1))
    (D.R p) (D.F p) (D.R (p + 1)) (D.I p)

def fundamental : Nerve.Ch P := ∑ p : Fin M, D.sector p

theorem fundamental_mem_inc : D.fundamental ∈ Nerve.Inc P :=
  (Nerve.Inc _).sum_mem fun p _ => (Nerve.Inc _).add_mem ((Nerve.Inc _).add_mem
    (triangleFlagChain_mem_inc (D.ve p) (D.v1e p) (D.vd (p + 1)) (D.wd (p + 1))
      (D.w1g p) (D.vg p) (D.et1 p) (D.d1t1 p) (D.gt1 p))
    (triangleFlagChain_mem_inc (D.vg p) (D.w1g p) (D.w1f p) (D.wf p)
      (D.wd p) (D.vd p) (D.gt2 p) (D.ft2 p) (D.dt2 p)))
    (triangleFlagChain_mem_inc (D.cr p) (D.wr p) (D.wf p) (D.w1f p)
      (D.wr (p + 1)) (D.cr (p + 1)) (D.ri p) (D.fi p) (D.r1i p))

theorem fundamental_degree : Nerve.lengthProjection 3 D.fundamental = D.fundamental := by
  simp [fundamental, sector, triangleFlagChain]

def cellularFundamental : StrictOrdTri P →₀ ℤ :=
  normalizeOrdChain2 (decodeOrdNerve2 D.fundamental)

def boundaryEdges : OrdEdge P →₀ ℤ :=
  ∑ p : Fin M, (Finsupp.single ⟨(D.V p, D.E p), D.ve p⟩ 1 -
    Finsupp.single ⟨(D.V (p + 1), D.E p), D.v1e p⟩ 1)

theorem decodedFundamental_boundary :
    Comb.bdry2 (orderCx P) (decodeOrdNerve2 D.fundamental) = D.boundaryEdges := by
  have hshift (g : Fin M → Nerve.Ch P) : (∑ p : Fin M, g (p + 1)) = ∑ p : Fin M, g p :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin M)) _ _ fun _ => rfl
  have hsec (p : Fin M) : Nerve.bdry (D.sector p) =
      flagEdge (D.V p) (D.V (p + 1)) (D.E p) + flagEdge (D.V (p + 1)) (D.W (p + 1)) (D.D (p + 1)) -
      flagEdge (D.V p) (D.W p) (D.D p) + flagEdge v.1 (D.W p) (D.R p) -
      flagEdge v.1 (D.W (p + 1)) (D.R (p + 1)) := by
    simp only [sector, map_add, bdry_triangleFlagChain, flagEdge]; abel
  apply ordNerveChain1_injective
  erw [ordNerveChain1_bdry2, ordNerveChain2_decode D.fundamental_mem_inc, D.fundamental_degree]
  simp only [fundamental, map_sum, hsec, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  erw [hshift fun p => flagEdge (D.V p) (D.W p) (D.D p),
    hshift fun p => flagEdge v.1 (D.W p) (D.R p)]
  simp [boundaryEdges, ordNerveChain1, flagEdge]

theorem cellularFundamental_relative : PolygonRelativeChain hc f D.cellularFundamental := by
  have hVE (q p : Fin M) : D.V q ≠ D.E p := fun h => by
    have hh := congrArg f h; erw [D.projV, D.projE] at hh; cases hh
  let bL (p : Fin M) : StrictOrdEdge P := ⟨(D.V p, D.E p), lt_of_le_of_ne (D.ve p) (hVE p p)⟩
  let bR (p : Fin M) : StrictOrdEdge P := ⟨(D.V (p + 1), D.E p), lt_of_le_of_ne (D.v1e p) (hVE (p + 1) p)⟩
  have hbdry : Comb.bdry2 (strictOrderCx P) D.cellularFundamental =
      ∑ p : Fin M, (Finsupp.single (bL p) 1 - Finsupp.single (bR p) 1) := by
    erw [cellularFundamental, bdry2_normalizeOrdChain2, D.decodedFundamental_boundary]
    simp [boundaryEdges, normalizeOrdEdge, hVE, bL, bR]
  intro e he
  by_contra hb
  have hneL (p : Fin M) : bL p ≠ e := fun hh =>
    hb (hh ▸ by change InPolygonBoundary hc (f (D.V p)) ∧ InPolygonBoundary hc (f (D.E p)); erw [D.projV, D.projE]; exact ⟨trivial, trivial⟩)
  have hneR (p : Fin M) : bR p ≠ e := fun hh =>
    hb (hh ▸ by change InPolygonBoundary hc (f (D.V (p + 1))) ∧ InPolygonBoundary hc (f (D.E p)); erw [D.projV, D.projE]; exact ⟨trivial, trivial⟩)
  refine Finsupp.mem_support_iff.mp he ?_
  erw [hbdry]; simp [hneL, hneR]

variable (hc f)

theorem cellularFundamental_pole_coefficients (hM : 2 ≤ M) :
    polygonCoverPoleCoefficients hc f hf D.cellularFundamental = Finsupp.single v 1 := by
  ext u
  erw [polygonCoverPoleCoefficients_apply]
  set t := polygonCoverPoleFlag hc f hf u
  have ht : f t.1.1 = cC hc ∧ f t.1.2.1 = cR hc 0 ∧ f t.1.2.2 = cI hc 0 :=
    polygonCoverPoleFlagPlus_projection hc f hf u.1 u.2 0
  have hv (p : Fin M) : D.V p ≠ t.1.1 := fun h => nomatch (D.projV p).symm.trans ((congrArg f h).trans ht.1)
  have hw (p : Fin M) : D.W p ≠ t.1.1 := fun h => nomatch (D.projW p).symm.trans ((congrArg f h).trans ht.1)
  have hplus (p : Fin M) :
      [v.1, D.R p, D.I p] = [t.1.1, t.1.2.1, t.1.2.2] ↔ v = u ∧ p = 0 :=
    ⟨fun h => by
      simp only [List.cons.injEq, and_true] at h
      exact ⟨Subtype.ext h.1, Cell.inn.inj ((D.projI p).symm.trans ((congrArg f h.2.2).trans ht.2.2))⟩,
     by rintro ⟨rfl, rfl⟩
        rw [hf.up_inj (D.cr 0) t.2.1.le ((D.projR 0).trans ht.2.1.symm),
          hf.up_inj ((D.cr 0).trans (D.ri 0)) (t.2.1.trans t.2.2).le ((D.projI 0).trans ht.2.2.symm)]; rfl⟩
  have hminus (p : Fin M) : [v.1, D.R (p + 1), D.I p] ≠ [t.1.1, t.1.2.1, t.1.2.2] := fun h => by
    simp only [List.cons.injEq, and_true] at h
    exact fin_succ_ne_self hM p
      ((Cell.rad.inj ((D.projR (p + 1)).symm.trans ((congrArg f h.2.1).trans ht.2.1))).trans
        (Cell.inn.inj ((D.projI p).symm.trans ((congrArg f h.2.2).trans ht.2.2))).symm)
  erw [cellularFundamental, normalizeOrdChain2_apply,
    ← ordTriangleCoefficient_encode, ordNerveChain2_decode D.fundamental_mem_inc, D.fundamental_degree]
  simp only [fundamental, sector, triangleFlagChain, map_sum, map_add, map_sub,
    ordTriangleCoefficient, FreeAbelianGroup.lift_apply_of, strictOrderIncl,
    hplus, hminus, if_false, List.cons.injEq, and_true, hv, hw, false_and,
    sub_zero, zero_add, add_zero, Finsupp.single_apply]
  by_cases h : v = u <;> simp [h]

end CoveredPolygon

def polygonCoverFilling (v : PolygonCoverPole hc f) : StrictOrdTri P →₀ ℤ :=
  (coveredPolygon hc f hf v).cellularFundamental

def polygonCoverReconstruct :
    (PolygonCoverPole hc f →₀ ℤ) →ₗ[ℤ] (StrictOrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ (polygonCoverFilling hc f hf)

theorem polygonRelative_reconstruct (hd : PolygonData vc ec)
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c) :
    c = polygonCoverReconstruct hc f hf (polygonCoverPoleCoefficients hc f hf c) := by
  have hrel' (a : PolygonCoverPole hc f →₀ ℤ) :
      PolygonRelativeChain hc f (polygonCoverReconstruct hc f hf a) := by
    induction a using Finsupp.induction_linear with
    | zero => erw [map_zero]; exact PolygonRelativeChain.zero hc f
    | add _ _ ha hb => erw [map_add]; exact PolygonRelativeChain.add hc f ha hb
    | single v n =>
      erw [polygonCoverReconstruct, Finsupp.linearCombination_single]
      exact PolygonRelativeChain.smul hc f (coveredPolygon hc f hf v).cellularFundamental_relative n
  refine polygonRelative_ext hc hd f hf c _ hrel (hrel' _) ?_
  have hM : 2 ≤ M := by have := hd.three_le; omega
  generalize polygonCoverPoleCoefficients hc f hf c = a
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add _ _ ha hb => erw [map_add, map_add, ← ha, ← hb]
  | single v n =>
    erw [polygonCoverReconstruct, Finsupp.linearCombination_single, map_smul,
      CoveredPolygon.cellularFundamental_pole_coefficients hc f hf (coveredPolygon hc f hf v) hM]
    simp [Finsupp.smul_single]
