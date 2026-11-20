module

public import RequestProject.ChamberZChain
public import RequestProject.ChamberZPi1
public import RequestProject.OrderComplexPi1Transfer
public import RequestProject.CombCoveringLift

@[expose] public section

/-!
# A copy of the base is injective in `π₁(Z)` — with no extension over the cone

`RequestProject/ChamberZPi1.lean` splits a copy of the base off `π₁(Z)` under the extra
hypothesis that the attaching map extends monotonically over the cone point of a chamber.  That
hypothesis is dropped here.

The argument is the van Kampen retraction on path classes of
`RequestProject/OrderComplexRetraction.lean`, applied to the chamber filtration of the actual
complex `Z` of `RequestProject/ChamberZPoset.lean`:

* the attaching intersection of a chamber of `Z` is `J_w`, which is nonempty, connected and
  simply connected (`FiniteChains.Davis.connectedIn_zJSet`,
  `FiniteChains.Davis.simplyConnectedIn_zJSet`);
* chains of `Z` are unmixed because chambers are upward closed, and the intersection of a
  chamber with the earlier ones is exactly `J_w` (`mem_earlier_zchamber_iff`);
* the modified chamber retracts monotonically onto its copy of the base, which gives the
  initial step (`FiniteChains.Davis.injIn_zchamber_base`); no extension over the cone is used,
  because the retraction is only used inside one chamber;
* the filtration by word length is exhausted step by step
  (`FiniteChains.Davis.injIn_zupto`), and a null-homotopy, being a finite derivation, lies in
  some initial union (`FiniteChains.Davis.injIn_zpos`).

The conclusion is `FiniteChains.Davis.pi1Map_zNew_injective_uncond`: for every marked chamber
`w` the inclusion of the copy of the base induces an **injective** map
`π₁(X) → π₁(Z)`; the hypotheses contain neither an extension over the cone nor the desired
injectivity itself.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V} {X : Type u} [Preorder X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-! ### The copy of the base attached at a marked chamber -/

/-- The copy of the base poset glued into the modified chamber of `w`. -/
def InZBaseAt (w : CayGroup A) : Zpos A X M att → Prop
  | Sum.inl _ => False
  | Sum.inr wx => wx.1.1 = w

omit [Fintype V] in
theorem inZBaseAt_imp_inZChamber {w : CayGroup A} {z : Zpos A X M att}
    (h : InZBaseAt w z) : InZChamber w z := by
  cases z with
  | inl p => exact h.elim
  | inr wx => exact h

omit [Fintype V] in
@[simp] theorem inZBaseAt_zNew (w : {w : CayGroup A // M w}) (x : X) :
    InZBaseAt (att := att) w.1 (zNew w x) := rfl

/-- The retraction of the copy of the base onto the base poset itself. -/
def zBaseRetr (w : CayGroup A) : {z : Zpos A X M att // InZBaseAt w z} → X
  | ⟨Sum.inl _, h⟩ => h.elim
  | ⟨Sum.inr wx, _⟩ => wx.2

omit [Fintype V] in
@[simp] theorem zBaseRetr_zNew (w : {w : CayGroup A // M w}) (x : X) :
    zBaseRetr (att := att) w.1 ⟨zNew w x, inZBaseAt_zNew w x⟩ = x := rfl

omit [Fintype V] in
theorem zBaseRetr_monotone (w : CayGroup A) :
    Monotone (zBaseRetr (A := A) (X := X) (M := M) (att := att) w) := by
  rintro ⟨p | ⟨u, x⟩, hz⟩ ⟨q | ⟨v, y⟩, hz'⟩ h
  · exact hz.elim
  · exact hz.elim
  · exact hz'.elim
  · exact h.2

/-! ### The attaching intersection of a chamber of `Z` -/

/-- `J_w` inside `Z` is connected. -/
theorem connectedIn_zJSet {w : CayGroup A} (hw : w ≠ 1) :
    ConnectedIn (ZJSet (A := A) (X := X) (M := M) (att := att) w) :=
  connectedIn_of_isConnected
    (isConnected_orderCx_of_orderIso (zJSetOrderIso (X := X) (att := att) w)
      (chamberInter_isConnected hw))

/-- `J_w` inside `Z` is simply connected. -/
theorem simplyConnectedIn_zJSet {w : CayGroup A} (hw : w ≠ 1) :
    SimplyConnectedIn (ZJSet (A := A) (X := X) (M := M) (att := att) w) :=
  simplyConnectedIn_of_simplyConnected
    (simplyConnected_orderCx_of_orderIso (zJSetOrderIso (X := X) (att := att) w)
      (chamberInter_simplyConnected hw))

/-- `J_w` inside `Z` is nonempty. -/
theorem exists_zJSet {w : CayGroup A} (hw : w ≠ 1) :
    ∃ z : Zpos A X M att, ZJSet w z :=
  ⟨((zJSetOrderIso (X := X) (att := att) w).symm (interTop hw)).1,
    ((zJSetOrderIso (X := X) (att := att) w).symm (interTop hw)).2⟩

/-! ### The initial step: the modified chamber retracts onto its copy of the base -/

omit [Fintype V] in
/-- **Inside a modified chamber, the copy of the base is injective on path classes.**  This is
the monotone retraction of the mapping cylinder; it involves no extension of the attaching map
over the cone point. -/
theorem injIn_zchamber_base {w : CayGroup A} (hw : M w) :
    InjIn (InZChamber (A := A) (X := X) (M := M) (att := att) w) (InZBaseAt w) := by
  refine injIn_of_monotone_retraction (fun z hz => inZBaseAt_imp_inZChamber hz)
    (fun z => (zChamberRetr hw z).1)
    (fun z z' h => zChamberRetr_monotone hw h) ?_ ?_
  · intro z
    obtain ⟨x, hx⟩ := zChamberRetr_mem hw z
    show InZBaseAt w (zChamberRetr hw z).1
    rw [hx]
    exact rfl
  · rintro ⟨p | ⟨u, x⟩, hz⟩ hb
    · exact hb.elim
    · rfl

/-! ### The filtration by word length -/


/-- A copy of the base is injective on path classes inside every initial union of chambers. -/
theorem injIn_zupto {w0 : CayGroup A} (hw0 : M w0) :
    ∀ n : ℕ, RACG.clen A w0 ≤ n →
      InjIn (ZUpto (A := A) (X := X) (M := M) (att := att) n) (InZBaseAt w0) := by
  apply chamberInduction A (fun S => w0 ∈ S → InjIn (chamberUnion InZChamber S) (InZBaseAt w0))
  · intro h
    have hw  := Set.mem_singleton_iff.mp h
    subst w0
    simpa only [chamberUnion_singleton] using injIn_zchamber_base hw0
  · intro n S x hx hl hs hne ih hw
    rw [chamberUnion_insert]
    let Prev : Zpos A X M att → Prop := chamberUnion InZChamber (chamberBall A n ∪ S)
    have hup : IsUpperSet (Prev : Set (Zpos A X M att)) := chamberUnion_up (C := InZChamber) (fun _ _ _ h => inZChamber_of_le h)
    obtain ⟨j, hj⟩ := exists_zJSet (X := X) (M := M) (att := att) hne
    have hconn := connectedIn_zJSet (X := X) (M := M) (att := att) hne
    have hsc := simplyConnectedIn_zJSet (X := X) (M := M) (att := att) hne
    have hov (z : Zpos A X M att)  := (zUpto_overlap hx hl hs z).symm
    rcases Set.mem_insert_iff.mp hw with hw | hw
    · subst w0
      exact injIn_trans (fun _ hz => inZBaseAt_imp_inZChamber hz)
        (injIn_union_of_unmixed (B := Prev) (fun _ _ h hp _ =>
          unmixed_of_upper (B := InZChamber x) (fun _ _ h => inZChamber_of_le h) hup h (or_comm.mp hp))
          (fun z => (hov z).trans and_comm) hconn hsc hj) (injIn_zchamber_base hw0)
    · exact injIn_trans (fun z hz => ⟨w0, hw, inZBaseAt_imp_inZChamber hz⟩)
        (injIn_union_of_unmixed (B := InZChamber x) (fun _ _ h hp _ =>
          unmixed_of_upper (C := InZChamber x) hup (fun _ _ hz => inZChamber_of_le hz) h hp) hov hconn hsc hj) (ih hw)

/-- **A copy of the base is injective on path classes inside the whole of `Z`.**  A homotopy is a
finite derivation, so it involves only finitely many cells and therefore lies in some initial
union of chambers. -/
theorem injIn_zpos {w0 : CayGroup A} (hw0 : M w0) :
    InjIn (fun _ : Zpos A X M att => True) (InZBaseAt w0) := by
  intro v l hv hp hl hnull
  obtain ⟨n, hn⟩ := exists_htpyIn_of_htpy
    (D := (ZUpto (A := A) (X := X) (M := M) (att := att)))
    (fun m n hmn z hz => by
      obtain ⟨y, hy, hyz⟩ := hz
      exact ⟨y, le_trans hy hmn, hyz⟩)
    (fun z => ⟨zlen z, zUpto_zlen z⟩) (htpyIn_true_iff.mp hnull)
  refine injIn_zupto hw0 (max n (RACG.clen A w0)) (le_max_right _ _) v l hv hp hl ?_
  refine HtpyIn.mono (fun z hz => ?_) hn
  obtain ⟨y, hy, hyz⟩ := hz
  exact ⟨y, le_trans hy (le_max_left _ _), hyz⟩

/-! ### The conclusion for the fundamental group -/

/-- **Unconditional injectivity of a copy of the base in `π₁(Z)`.**  For every marked chamber
`w` of the model `Z` of modified chambers, and for every base point of the base poset `X`, the
inclusion of the copy of `X` glued into the chamber of `w` induces an injective homomorphism
`π₁(X) → π₁(Z)`.

No extension of the attaching map over the cone point of a chamber is assumed: the attaching map
`att` is the given monotone map on nonempty simplices only. -/
theorem pi1Map_zNew_injective_uncond (w : {w : CayGroup A // M w}) (x : X) :
    Function.Injective
      (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := M) (att := att) w)
        (zNew_monotone w)) x) :=
  pi1Map_injective_of_injIn (Bp := InZBaseAt w.1) (injIn_zpos w.2)
    (zNew_monotone w) (inZBaseAt_zNew w)
    (zBaseRetr_monotone (A := A) (X := X) (M := M) (att := att) w.1)
    (zBaseRetr_zNew w) x

/-- **Composing with a covering.**  If `Z` covers a complex `W`, the copy of the base is still
injective on fundamental groups after pushing down to `W`, because a covering is injective on
fundamental groups.  This is the covering step of the comparison with the article's complex; the
identification of `W` with the presentation complex of the substituted presentation is a
separate statement, and is not proved here. -/
theorem pi1Map_zNew_covering_injective {W : Comb.Complex2}
    (q : Comb.Hom (orderCx (Zpos A X M att)) W) (hq : Comb.IsCovering q)
    (w : {w : CayGroup A // M w}) (x : X) :
    Function.Injective
      ((Comb.pi1Map q (zNew (A := A) (X := X) (M := M) (att := att) w x)).comp
        (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := M) (att := att) w)
          (zNew_monotone w)) x)) :=
  (Comb.pi1Map_injective_of_isCovering hq _).comp (pi1Map_zNew_injective_uncond w x)

end Davis
end FiniteChains
