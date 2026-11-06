module

public import RequestProject.StrictBottomLinkChains
public import RequestProject.SurfaceLink
public import RequestProject.GenusSurface
public import RequestProject.SurfaceFundamentalChain
public import RequestProject.OrderNerveDecoding
public import RequestProject.StrictChainCoefficients
public import RequestProject.CellularChainMapZero

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Classical

namespace FiniteChains.Davis
open Comb Cell
universe u
variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

abbrev PolygonPoleLink := StrictAbove (cC hc)

def polygonPoleRadius (p : Fin M) : PolygonPoleLink hc :=
  ⟨cR hc p, ctr_lt_rad hc p⟩

def polygonPoleTriangle (p : Fin M) : PolygonPoleLink hc :=
  ⟨cI hc p, ctr_lt_inn hc p⟩

def polygonPoleEdgePlus (p : Fin M) : StrictOrdEdge (PolygonPoleLink hc) :=
  ⟨(polygonPoleRadius hc p, polygonPoleTriangle hc p),
    (lt_inn_iff hc).2 (.inr (.inl rfl))⟩

def polygonPoleEdgeMinus (p : Fin M) : StrictOrdEdge (PolygonPoleLink hc) :=
  ⟨(polygonPoleRadius hc (p + 1), polygonPoleTriangle hc p),
    (lt_inn_iff hc).2 (.inr (.inr (.inl rfl)))⟩

theorem polygonPoleLink_edge_cases (e : StrictOrdEdge (PolygonPoleLink hc)) :
    ∃ p : Fin M, e = polygonPoleEdgePlus hc p ∨ e = polygonPoleEdgeMinus hc p := by
  rcases e with ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩
  change toS vc ec hc ctr < toS vc ec hc a at ha
  change toS vc ec hc a < toS vc ec hc b at hab
  obtain ⟨p, rfl | rfl⟩ := (ctr_lt_iff hc).mp ha
  · rcases (rad_lt_iff hc).mp hab with rfl | rfl
    · exact ⟨p, .inl rfl⟩
    · refine ⟨fpred p, .inr (Subtype.ext (Prod.ext (Subtype.ext ?_) rfl))⟩
      simp only [polygonPoleEdgeMinus, polygonPoleRadius, cR, toS, fpred_add_one]
  · have hh := (lt_iff_plt hc).mp hab
    cases b <;> simp [plt] at hh

@[simp] theorem polygonPoleRadius_eq_iff (p r : Fin M) :
    polygonPoleRadius hc p = polygonPoleRadius hc r ↔ p = r :=
  ⟨fun h => Cell.rad.inj (congrArg Subtype.val h), fun h => h ▸ rfl⟩

@[simp] theorem polygonPoleTriangle_eq_iff (p r : Fin M) :
    polygonPoleTriangle hc p = polygonPoleTriangle hc r ↔ p = r :=
  ⟨fun h => Cell.inn.inj (congrArg Subtype.val h), fun h => h ▸ rfl⟩

@[simp] theorem polygonPoleRadius_ne_triangle (p r : Fin M) :
    polygonPoleRadius hc p ≠ polygonPoleTriangle hc r :=
  fun he => nomatch congrArg Subtype.val he

@[simp] theorem polygonPoleTriangle_ne_radius (p r : Fin M) :
    polygonPoleTriangle hc p ≠ polygonPoleRadius hc r :=
  (polygonPoleRadius_ne_triangle hc r p).symm

@[simp] theorem polygonPoleEdgePlus_eq_iff (p r : Fin M) :
    polygonPoleEdgePlus hc p = polygonPoleEdgePlus hc r ↔ p = r :=
  ⟨fun he => (polygonPoleTriangle_eq_iff hc p r).mp (congrArg (·.1.2) he), fun h => h ▸ rfl⟩

@[simp] theorem polygonPoleEdgeMinus_eq_iff (p r : Fin M) :
    polygonPoleEdgeMinus hc p = polygonPoleEdgeMinus hc r ↔ p = r :=
  ⟨fun he => (polygonPoleTriangle_eq_iff hc p r).mp (congrArg (·.1.2) he), fun h => h ▸ rfl⟩

theorem polygonPoleEdgePlus_ne_minus (hM : 2 ≤ M) (p r : Fin M) :
    polygonPoleEdgePlus hc p ≠ polygonPoleEdgeMinus hc r := fun he => by
  have hpr : p = r := (polygonPoleTriangle_eq_iff hc p r).mp (congrArg (·.1.2) he)
  subst r
  exact fin_succ_ne_self hM p ((polygonPoleRadius_eq_iff hc p (p + 1)).mp (congrArg (·.1.1) he)).symm

theorem polygonPole_boundary_triangle (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ) (p : Fin M) :
    Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d (polygonPoleTriangle hc p) =
      d (polygonPoleEdgePlus hc p) + d (polygonPoleEdgeMinus hc p) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp only [map_add, Finsupp.add_apply, hd, he]; ring
  | single e n =>
    have hne := fun r p => (polygonPoleEdgePlus_ne_minus hc hM p r).symm
    erw [Comb.bdry1_single]
    obtain ⟨r, rfl | rfl⟩ := polygonPoleLink_edge_cases hc e
    · change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc r) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, polygonPoleEdgePlus_ne_minus hc hM]
    · change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc (r + 1)) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, hne]

theorem polygonPole_boundary_radius (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ) (p : Fin M) :
    Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d (polygonPoleRadius hc (p + 1)) =
      -d (polygonPoleEdgePlus hc (p + 1)) - d (polygonPoleEdgeMinus hc p) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp only [map_add, Finsupp.add_apply, hd, he]; ring
  | single e n =>
    have hne := fun r p => (polygonPoleEdgePlus_ne_minus hc hM p r).symm
    erw [Comb.bdry1_single]
    obtain ⟨r, rfl | rfl⟩ := polygonPoleLink_edge_cases hc e
    · change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc r) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, polygonPoleEdgePlus_ne_minus hc hM]
    · change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc (r + 1)) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, hne]

theorem polygonPole_cycle_ext (hM : 2 ≤ M)
    (c d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ)
    (hc' : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) c = 0)
    (hd : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d = 0)
    (he : c (polygonPoleEdgePlus hc 0) = d (polygonPoleEdgePlus hc 0)) : c = d := by
  have hcoeff (z : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ)
      (hz : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) z = 0) (p : Fin M) :
      z (polygonPoleEdgePlus hc p) = z (polygonPoleEdgePlus hc 0) ∧
        z (polygonPoleEdgeMinus hc p) = -z (polygonPoleEdgePlus hc 0) := by
    have hlocal (r : Fin M) :
        z (polygonPoleEdgeMinus hc r) = -z (polygonPoleEdgePlus hc r) ∧
        z (polygonPoleEdgePlus hc (r + 1)) = z (polygonPoleEdgePlus hc r) := by
      have ht := polygonPole_boundary_triangle hc hM z r
      have hr := polygonPole_boundary_radius hc hM z r
      erw [hz, Finsupp.zero_apply] at ht hr; omega
    have hall : ∀ n (hn : n < M), z (polygonPoleEdgePlus hc ⟨n, hn⟩) = z (polygonPoleEdgePlus hc 0) := by
      intro n; induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        have hp : n < M := by omega
        have hs : (⟨n, hp⟩ : Fin M) + 1 = ⟨n + 1, hn⟩ :=
          Fin.ext ((fin_succ_val _).trans (Nat.mod_eq_of_lt hn))
        erw [← hs, (hlocal ⟨n, hp⟩).2]; exact ih hp
    have heq := hall p.val p.isLt
    exact ⟨heq, (hlocal p).1.trans (congrArg Neg.neg heq)⟩
  ext e
  obtain ⟨p, rfl | rfl⟩ := polygonPoleLink_edge_cases hc e
  · exact (hcoeff c hc' p).1.trans (he.trans (hcoeff d hd p).1.symm)
  · exact (hcoeff c hc' p).2.trans ((congrArg Neg.neg he).trans (hcoeff d hd p).2.symm)

section
variable {P : Type u} [PartialOrder P] (f : P → SCell vc ec hc) (hf : IsPosetCover f)

def polygonCoverPoleOrderIso (v : P) (hv : f v = cC hc) :
    StrictAbove v ≃o PolygonPoleLink hc :=
  (hf.upperIntervalOrderIso v).trans (strictAboveCongr hv)

def polygonCoverPoleHom (v : P) (hv : f v = cC hc) :
    Hom (strictOrderCx (StrictAbove v)) (strictOrderCx (PolygonPoleLink hc)) :=
  strictOrderCxMap (polygonCoverPoleOrderIso hc f hf v hv)
    (polygonCoverPoleOrderIso hc f hf v hv).strictMono

def polygonCoverPoleLink (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ) : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ :=
  chain1 (polygonCoverPoleHom hc f hf v hv) (strictBottomLinkChain v c)

theorem polygonCoverPoleLink_apply (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ) (e : StrictOrdEdge (StrictAbove v)) :
    polygonCoverPoleLink hc f hf v hv c
      ((polygonCoverPoleHom hc f hf v hv).onE e) =
        c (strictBottomConeTriangle v e) :=
  (strictOrderCxMap_chain1_apply
    (polygonCoverPoleOrderIso hc f hf v hv)
    (polygonCoverPoleOrderIso hc f hf v hv).strictMono
    (polygonCoverPoleOrderIso hc f hf v hv).injective
    (strictBottomLinkChain v c) e).trans (strictBottomLinkChain_apply v c e)

def polygonCoverPoleFlagPlus (v : P) (hv : f v = cC hc) (p : Fin M) : StrictOrdTri P :=
  strictBottomConeTriangle v
    ((strictOrderEdgeEquiv (polygonCoverPoleOrderIso hc f hf v hv)).symm
      (polygonPoleEdgePlus hc p))

theorem polygonCoverPoleFlagPlus_projection (v : P) (hv : f v = cC hc) (p : Fin M) :
    f (polygonCoverPoleFlagPlus hc f hf v hv p).1.1 = cC hc ∧
    f (polygonCoverPoleFlagPlus hc f hf v hv p).1.2.1 = cR hc p ∧
    f (polygonCoverPoleFlagPlus hc f hf v hv p).1.2.2 = cI hc p := by
  let iso := polygonCoverPoleOrderIso hc f hf v hv
  let eqv := strictOrderEdgeEquiv iso
  let e := eqv.symm (polygonPoleEdgePlus hc p)
  have he : eqv e = polygonPoleEdgePlus hc p := eqv.apply_symm_apply _
  have h₁ : (iso e.1.1).val = cR hc p := congrArg (fun z : StrictOrdEdge (PolygonPoleLink hc) => z.1.1.val) he
  have h₂ : (iso e.1.2).val = cI hc p := congrArg (fun z : StrictOrdEdge (PolygonPoleLink hc) => z.1.2.val) he
  have hap (x : StrictAbove v) : (iso x).val = f x.val := by
    change (strictAboveCongr hv (hf.upperIntervalOrderIso v x)).val = f x.val
    erw [strictAboveCongr_val]; rfl
  rw [hap] at h₁ h₂
  exact ⟨hv, h₁, h₂⟩

abbrev PolygonCoverPole := {v : P // f v = cC hc}

def polygonCoverPoleFlag (v : PolygonCoverPole hc f) : StrictOrdTri P :=
  polygonCoverPoleFlagPlus hc f hf v.1 v.2 0

def polygonCoverPoleCoefficients :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (PolygonCoverPole hc f →₀ ℤ) :=
  (Finsupp.comapDomain.addMonoidHom (f := polygonCoverPoleFlag hc f hf)
    fun _ _ h => Subtype.ext (congrArg (·.1.1) h)).toIntLinearMap

theorem polygonCoverPoleCoefficients_apply (c : StrictOrdTri P →₀ ℤ)
    (v : PolygonCoverPole hc f) :
    polygonCoverPoleCoefficients hc f hf c v = c (polygonCoverPoleFlag hc f hf v) := rfl

theorem polygonCoverPole_relative_ext (hM : 2 ≤ M)
    (c d : StrictOrdTri P →₀ ℤ)
    (hc' : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0)
    (hd : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) d e = 0)
    (he : polygonCoverPoleCoefficients hc f hf c = polygonCoverPoleCoefficients hc f hf d)
    (t : StrictOrdTri P) (ht : f t.1.1 = cC hc) : c t = d t := by
  let v : PolygonCoverPole hc f := ⟨t.1.1, ht⟩
  have hmin (a : P) (ha : a ≤ v.1) : a = v.1 := by
    have hfa : f a ≤ cC hc := v.2 ▸ hf.mono ha
    have hc0 : f a = cC hc := by
      rcases (show f a = cC hc ∨ plt vc ec (f a) ctr from hfa) with h | h
      · exact h
      · cases f a <;> simp [plt] at h
    exact hf.down_inj ha le_rfl (hc0.trans v.2.symm)
  have hcyc (z : StrictOrdTri P →₀ ℤ)
      (hz : ∀ e : StrictOrdEdge P, f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) z e = 0) :
      Comb.bdry1 (strictOrderCx (PolygonPoleLink hc))
        (polygonCoverPoleLink hc f hf v.1 v.2 z) = 0 := by
    change Comb.bdry1 _ (chain1 (polygonCoverPoleHom hc f hf v.1 v.2)
      (strictBottomLinkChain v.1 z)) = 0
    erw [bdry1_chain1, strictBottomLink_relative_cycle v.1 hmin z fun e he => hz e (he.symm ▸ v.2),
      map_zero]
  have hplus (z : StrictOrdTri P →₀ ℤ) :
      polygonCoverPoleLink hc f hf v.1 v.2 z (polygonPoleEdgePlus hc 0) =
        z (polygonCoverPoleFlag hc f hf v) := by
    let eqv := strictOrderEdgeEquiv (polygonCoverPoleOrderIso hc f hf v.1 v.2)
    have hh := polygonCoverPoleLink_apply hc f hf v.1 v.2 z (eqv.symm (polygonPoleEdgePlus hc 0))
    change polygonCoverPoleLink hc f hf v.1 v.2 z (eqv (eqv.symm (polygonPoleEdgePlus hc 0))) = _ at hh
    erw [eqv.apply_symm_apply] at hh
    exact hh
  have hlink := polygonPole_cycle_ext hc hM
    (polygonCoverPoleLink hc f hf v.1 v.2 c) (polygonCoverPoleLink hc f hf v.1 v.2 d)
    (hcyc c hc') (hcyc d hd) (by rw [hplus, hplus]; exact congrArg (· v) he)
  let e : StrictOrdEdge (StrictAbove v.1) :=
    ⟨(⟨t.1.2.1, t.2.1⟩, ⟨t.1.2.2, t.2.1.trans t.2.2⟩), t.2.2⟩
  have hh := congrArg (· ((polygonCoverPoleHom hc f hf v.1 v.2).onE e)) hlink
  convert hh using 1 <;> simp only [polygonCoverPoleLink_apply] <;> rfl

def polygonCoverGroupCoefficient {G : Type u} [Group G]
    (e : PolygonCoverPole hc f ≃ G) (c : StrictOrdTri P →₀ ℤ) : MonoidAlgebra ℤ G :=
  MonoidAlgebra.ofCoeff (Finsupp.mapDomain e (polygonCoverPoleCoefficients hc f hf c))

end

def InPolygonBoundary : SCell vc ec hc → Prop
  | .vtx _ | .bed _ => True
  | _ => False

variable {P : Type u} [PartialOrder P] (f : P → SCell vc ec hc) (hf : IsPosetCover f)

theorem polygonCover_boundary_vanishes_at_poles
    (c : StrictOrdTri P →₀ ℤ)
    (hboundary : ∀ e ∈ (Comb.bdry2 (strictOrderCx P) c).support,
      InPolygonBoundary hc (f e.1.1)) :
    ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0 := fun e he => by
  by_contra hn
  have hh := hboundary e (Finsupp.mem_support_iff.mpr hn)
  erw [he] at hh; exact hh
