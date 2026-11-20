module

public import RequestProject.StrictBottomLinkChains
public import RequestProject.SurfaceRegular
public import RequestProject.GenusSurface
public import RequestProject.SurfaceFundamentalChain
public import RequestProject.OrderNerveDecoding
public import RequestProject.StrictChainCoefficients
public import RequestProject.CellularChainMapZero
public import RequestProject.CellularBoundaryCoefficients

@[expose] public section

/-! Pole coefficients in genuine covers of the polygon surface.

The coefficients here are indexed by actual lifts of the polygon centre.  No
augmentation, connected-cover premise, or faithfulness of a group receiver is
used.  The input is a relative two-chain: its boundary vanishes on edges over
the polygon centre, as it does when supported on the marked boundary graph.

This file extracts and reconstructs the part incident to the centre.  Extension
of this rigidity through the six flags of each inner triangle and through the
collar, and its transport from the attaching barycentric cover, remain separate
dependencies of the full B2 proof.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
    (lt_inn_iff hc).2 (Or.inr (Or.inl rfl))⟩

def polygonPoleEdgeMinus (p : Fin M) : StrictOrdEdge (PolygonPoleLink hc) :=
  ⟨(polygonPoleRadius hc (p + 1), polygonPoleTriangle hc p),
    (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))⟩

/-- All edges of the actual upper link are the two radial incidences of an
actual inner triangle; no presentation of the link is assumed. -/
theorem polygonPoleLink_edge_cases (e : StrictOrdEdge (PolygonPoleLink hc)) :
    ∃ p : Fin M, e = polygonPoleEdgePlus hc p ∨ e = polygonPoleEdgeMinus hc p := by
  rcases e with ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩
  change toS vc ec hc ctr < toS vc ec hc a at ha
  change toS vc ec hc a < toS vc ec hc b at hab
  obtain ⟨p, hp | hp⟩ := (ctr_lt_iff hc).mp ha
  · subst a
    rcases (rad_lt_iff hc).mp hab with hb' | hb'
    · aesop
    · subst b
      refine ⟨fpred p, Or.inr ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        simp only [polygonPoleEdgeMinus, polygonPoleRadius, cR, toS, fpred_add_one]
      · rfl
  · subst a
    have hh := (lt_iff_plt hc).mp hab
    trivial

@[simp] theorem polygonPoleRadius_eq_iff (p r : Fin M) :
    polygonPoleRadius hc p = polygonPoleRadius hc r ↔ p = r := by
  constructor
  · intro h
    exact Cell.rad.inj (congrArg (·.val) h)
  · aesop

@[simp] theorem polygonPoleTriangle_eq_iff (p r : Fin M) :
    polygonPoleTriangle hc p = polygonPoleTriangle hc r ↔ p = r := by
  constructor
  · intro h
    exact Cell.inn.inj (congrArg (·.val) h)
  · aesop

@[simp] theorem polygonPoleRadius_ne_triangle (p r : Fin M) :
    polygonPoleRadius hc p ≠ polygonPoleTriangle hc r := by
  intro he
  have hh := congrArg Subtype.val he
  cases hh

@[simp] theorem polygonPoleTriangle_ne_radius (p r : Fin M) :
    polygonPoleTriangle hc p ≠ polygonPoleRadius hc r :=
  (polygonPoleRadius_ne_triangle hc r p).symm



theorem polygonPoleEdgePlus_ne_minus (hM : 2 ≤ M) (p r : Fin M) :
    polygonPoleEdgePlus hc p ≠ polygonPoleEdgeMinus hc r := by
  intro he
  have hpr  := (polygonPoleTriangle_eq_iff hc p r).mp
    (congrArg (·.1.2) he)
  subst r
  have hr  := (polygonPoleRadius_eq_iff hc p (p + 1)).mp
    (congrArg (·.1.1) he)
  exact fin_succ_ne_self hM p hr.symm

/-- The two actual incidences at an inner-triangle vertex have their genuine
positive boundary signs. -/
theorem polygonPole_boundary_triangle (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ) (p : Fin M) :
    Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d (polygonPoleTriangle hc p) =
      d (polygonPoleEdgePlus hc p) + d (polygonPoleEdgeMinus hc p) := by
  refine bdry1_pair_target (X := strictOrderCx (PolygonPoleLink hc))
    (polygonPoleEdgePlus_ne_minus hc hM p p) ?_ ?_ d <;> intro e <;>
    obtain ⟨r, rfl | rfl⟩ := polygonPoleLink_edge_cases hc e <;>
    simp [strictOrderCx, polygonPoleEdgePlus, polygonPoleEdgeMinus]

/-- At a radius, the two actual incidences have their genuine negative signs. -/
theorem polygonPole_boundary_radius (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ) (p : Fin M) :
    Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d (polygonPoleRadius hc (p + 1)) =
      -d (polygonPoleEdgePlus hc (p + 1)) - d (polygonPoleEdgeMinus hc p) := by
  refine bdry1_pair_source (X := strictOrderCx (PolygonPoleLink hc))
    (polygonPoleEdgePlus_ne_minus hc hM (p + 1) p) ?_ ?_ d <;> intro e <;>
    obtain ⟨r, rfl | rfl⟩ := polygonPoleLink_edge_cases hc e <;>
    simp [strictOrderCx, polygonPoleEdgePlus, polygonPoleEdgeMinus] <;> tauto

/-- Every integral one-cycle of the actual polygon-centre link has a single
coefficient.  This is the local coefficient rigidity used at each cover pole. -/
theorem polygonPole_cycle_coefficients (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ)
    (hd : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d = 0) (p : Fin M) :
    d (polygonPoleEdgePlus hc p) = d (polygonPoleEdgePlus hc 0) ∧
      d (polygonPoleEdgeMinus hc p) = -d (polygonPoleEdgePlus hc 0) := by
  have hlocal (r : Fin M) :
      d (polygonPoleEdgeMinus hc r) = -d (polygonPoleEdgePlus hc r) ∧
      d (polygonPoleEdgePlus hc (r + 1)) = d (polygonPoleEdgePlus hc r) := by
    have ht := polygonPole_boundary_triangle hc hM d r
    have hr := polygonPole_boundary_radius hc hM d r
    erw [hd, Finsupp.zero_apply] at ht hr
    omega
  have hall : ∀ n (hn : n < M),
      d (polygonPoleEdgePlus hc ⟨n, hn⟩) = d (polygonPoleEdgePlus hc 0) := by
    intro n
    induction n with
    | zero => aesop
    | succ n ih =>
      intro hn
      have hp : n < M := by omega
      have hs : (⟨n, hp⟩ : Fin M) + 1 = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        erw [fin_succ_val]
        exact Nat.mod_eq_of_lt hn
      erw [← hs, (hlocal ⟨n, hp⟩).2]
      exact ih hp
  simp_all

/-- Agreement at one actual radial incidence determines the entire pole link. -/
theorem polygonPole_cycle_ext (hM : 2 ≤ M)
    (c d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ)
    (hc' : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) c = 0)
    (hd : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d = 0)
    (he : c (polygonPoleEdgePlus hc 0) = d (polygonPoleEdgePlus hc 0)) : c = d := by
  ext e
  obtain ⟨p, hp | hp⟩ := polygonPoleLink_edge_cases hc e
  · subst e
    exact (polygonPole_cycle_coefficients hc hM c hc' p).1.trans
      (he.trans (polygonPole_cycle_coefficients hc hM d hd p).1.symm)
  · subst e
    exact (polygonPole_cycle_coefficients hc hM c hc' p).2.trans
      ((congrArg Neg.neg he).trans (polygonPole_cycle_coefficients hc hM d hd p).2.symm)

section Cover
variable {P : Type u} [PartialOrder P] (f : P → SCell vc ec hc)
  (hf : IsPosetCover f)

theorem polygonCentre_minimal (a : SCell vc ec hc) (ha : a ≤ cC hc) : a = cC hc := by
  change a = cC hc ∨ plt vc ec a ctr at ha
  simp_all [plt]

include hf in
theorem polygonCoverPole_minimal (v : P) (hv : f v = cC hc) :
    ∀ a, a ≤ v → a = v := by
  intro a ha
  have hfa := hf.mono ha
  erw [hv] at hfa
  exact hf.down_inj ha (le_refl v) ((polygonCentre_minimal hc (f a) hfa).trans hv.symm)

/-- The actual upper link at each genuine lifted polygon centre. -/
noncomputable def polygonCoverPoleOrderIso (v : P) (hv : f v = cC hc) :
    StrictAbove v ≃o PolygonPoleLink hc :=
  (hf.upperIntervalOrderIso v).trans (strictAboveCongr hv)

theorem polygonCoverPoleOrderIso_apply_val (v : P) (hv : f v = cC hc)
    (x : StrictAbove v) :
    (polygonCoverPoleOrderIso hc f hf v hv x).val = f x.val := by
  erw [strictAboveCongr_val]
  rfl

noncomputable def polygonCoverPoleHom (v : P) (hv : f v = cC hc) :
    Hom (strictOrderCx (StrictAbove v)) (strictOrderCx (PolygonPoleLink hc)) :=
  strictOrderCxMap (polygonCoverPoleOrderIso hc f hf v hv)
    (polygonCoverPoleOrderIso hc f hf v hv).strictMono

noncomputable def polygonCoverPoleLink (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ) : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ :=
  chain1 (polygonCoverPoleHom hc f hf v hv) (strictBottomLinkChain v c)

/-- A relative chain with boundary on the marked boundary graph gives a cycle
at each lifted pole.  The two-chain itself is not assumed closed. -/
theorem polygonCoverPoleLink_cycle (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ)
    (hrel : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0) :
    Comb.bdry1 (strictOrderCx (PolygonPoleLink hc))
      (polygonCoverPoleLink hc f hf v hv c) = 0 := by
  change Comb.bdry1 _ (chain1 (polygonCoverPoleHom hc f hf v hv)
    (strictBottomLinkChain v c)) = 0
  erw [bdry1_chain1]
  have hlink := strictBottomLink_relative_cycle v
    (polygonCoverPole_minimal hc f hf v hv) c (fun e he => hrel e (he.symm ▸ hv))
  erw [hlink, map_zero]

/-- Projection within one lifted upper interval keeps every actual coefficient. -/
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

noncomputable def polygonCoverPoleFlagPlus (v : P) (hv : f v = cC hc)
    (p : Fin M) : StrictOrdTri P :=
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
  have h₁ := congrArg (·.1.1.val) he
  have h₂ := congrArg (·.1.2.val) he
  change (iso e.1.1).val = cR hc p at h₁
  change (iso e.1.2).val = cI hc p at h₂
  erw [polygonCoverPoleOrderIso_apply_val] at h₁ h₂
  tauto

theorem polygonCoverPoleLink_plus (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ) (p : Fin M) :
    polygonCoverPoleLink hc f hf v hv c (polygonPoleEdgePlus hc p) =
      c (polygonCoverPoleFlagPlus hc f hf v hv p) := by
  let e := strictOrderEdgeEquiv (polygonCoverPoleOrderIso hc f hf v hv)
  have hh := polygonCoverPoleLink_apply hc f hf v hv c
    (e.symm (polygonPoleEdgePlus hc p))
  change polygonCoverPoleLink hc f hf v hv c
    (e (e.symm (polygonPoleEdgePlus hc p))) = _ at hh
  erw [e.apply_symm_apply] at hh
  exact hh

/-- The actual finite set of nonzero coefficients is indexed by actual pole
lifts, even for disconnected covers with arbitrarily many sheets. -/
abbrev PolygonCoverPole := {v : P // f v = cC hc}

noncomputable def polygonCoverPoleFlag (v : PolygonCoverPole hc f) : StrictOrdTri P :=
  polygonCoverPoleFlagPlus hc f hf v.1 v.2 0

theorem polygonCoverPoleFlag_injective :
    Function.Injective (polygonCoverPoleFlag hc f hf) := by
  intro v w h
  apply Subtype.ext
  exact congrArg (·.1.1) h

noncomputable def polygonCoverPoleCoefficients :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (PolygonCoverPole hc f →₀ ℤ) :=
  (Finsupp.comapDomain.addMonoidHom (polygonCoverPoleFlag_injective hc f hf)).toIntLinearMap

theorem polygonCoverPoleCoefficients_apply (c : StrictOrdTri P →₀ ℤ)
    (v : PolygonCoverPole hc f) :
    polygonCoverPoleCoefficients hc f hf c v = c (polygonCoverPoleFlag hc f hf v) := rfl

/-- Equality of the finitely supported pole coefficients forces equality on
every actual triangle incident to a pole.  This is relative coefficient
rigidity in a genuine cover, rather than an augmented statement on the base. -/
theorem polygonCoverPole_relative_ext (hM : 2 ≤ M)
    (c d : StrictOrdTri P →₀ ℤ)
    (hc' : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0)
    (hd : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) d e = 0)
    (he : polygonCoverPoleCoefficients hc f hf c = polygonCoverPoleCoefficients hc f hf d)
    (t : StrictOrdTri P) (ht : f t.1.1 = cC hc) : c t = d t := by
  let v : PolygonCoverPole hc f := ⟨t.1.1, ht⟩
  have hp : c (polygonCoverPoleFlag hc f hf v) = d (polygonCoverPoleFlag hc f hf v) :=
    congrArg (fun z => z v) he
  have hlink := polygonPole_cycle_ext hc hM
    (polygonCoverPoleLink hc f hf v.1 v.2 c)
    (polygonCoverPoleLink hc f hf v.1 v.2 d)
    (polygonCoverPoleLink_cycle hc f hf v.1 v.2 c hc')
    (polygonCoverPoleLink_cycle hc f hf v.1 v.2 d hd)
    (by simpa only [polygonCoverPoleLink_plus, polygonCoverPoleFlag] using hp)
  let e : StrictOrdEdge (StrictAbove v.1) :=
    ⟨(⟨t.1.2.1, t.2.1⟩, ⟨t.1.2.2, t.2.1.trans t.2.2⟩), t.2.2⟩
  have hh := congrArg (fun z => z ((polygonCoverPoleHom hc f hf v.1 v.2).onE e)) hlink
  convert hh using 1 <;> simp only [polygonCoverPoleLink_apply] <;> rfl

/-- Reindexing the genuine pole lifts by a group gives a full group-ring
coefficient.  The next formula shows explicitly that no sheet is summed away. -/
noncomputable def polygonCoverGroupCoefficient {G : Type u} [Group G]
    (e : PolygonCoverPole hc f ≃ G) (c : StrictOrdTri P →₀ ℤ) : MonoidAlgebra ℤ G :=
  MonoidAlgebra.ofCoeff (Finsupp.mapDomain e (polygonCoverPoleCoefficients hc f hf c))

end Cover

/-- The one-dimensional identified boundary of the polygon. -/
def InPolygonBoundary : SCell vc ec hc → Prop
  | .vtx _ => True
  | .bed _ => True
  | _ => False

section BoundarySupport
variable {P : Type u} [PartialOrder P] (f : P → SCell vc ec hc)
  (hf : IsPosetCover f)

/-- The relative hypothesis used above follows directly from actual boundary
support on the polygon marking, without a homology or cycle assumption. -/
theorem polygonCover_boundary_vanishes_at_poles
    (c : StrictOrdTri P →₀ ℤ)
    (hboundary : ∀ e ∈ (Comb.bdry2 (strictOrderCx P) c).support,
      InPolygonBoundary hc (f e.1.1)) :
    ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0 := by
  intro e he
  by_contra hn
  have hh := hboundary e (Finsupp.mem_support_iff.mpr hn)
  erw [he] at hh
  exact hh

end BoundarySupport








end FiniteChains.Davis
