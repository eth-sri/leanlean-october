module

public import RequestProject.CombUniversalCover
public import RequestProject.UnivCoverIncl

@[expose] public section

/-!
# `π₂` of a combinatorial two-complex, the Hurewicz map and the Cockcroft property

With the universal cover of `RequestProject/CombUniversalCover.lean` at hand, the second
homotopy module of a two-complex is available in the usual combinatorial form: a two-complex
has no three-cells, so

  `π₂(X) = H₂(X̃) = ker ∂₂(X̃)`.

This file introduces that module, the Hurewicz map (push a two-cycle of the cover down to the
complex), the **Cockcroft** property ("the Hurewicz map is zero"), the functorial lift of a
cellular map to the universal covers, and the property "the map is zero on `π₂`" used in
condition (1) of Theorem A.

* `FiniteChains.Comb.univLift` — the lift of a cellular map to the universal covers;
* `FiniteChains.Comb.Pi2` — the second homotopy module, as the two-cycles of the cover;
* `FiniteChains.Comb.bdry2_hurewicz` — the Hurewicz image of a two-cycle of the cover is a
  two-cycle of `X`, that is, an element of `H₂(X)`;
* `FiniteChains.Comb.IsCockcroft` — the Cockcroft property: the Hurewicz map is zero;
* `FiniteChains.Comb.ZeroPi2` — a cellular map is zero on `π₂`.
-/

noncomputable section

namespace FiniteChains
namespace Comb

universe u

variable {X Y Z : Complex2.{u}}

/-! ### Functoriality of the universal cover -/

theorem endpt_mapPath (h : Hom X Y) : ∀ (q : List _) (a : X.V),
    endpt Y (h.onV a) (mapPath h q) = h.onV (endpt X a q) := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro a
      show endpt Y _ (mapPath h t) = _
      simp_all [germTgt_onE]

variable (x₀ : X.V)

variable (h : Hom X Y)

variable (p : PathFrom X x₀)

/-- The image of a path from `x₀` under a cellular map. -/
def mapPathFrom : PathFrom Y (h.onV x₀) :=
  ⟨mapPath h p.1, by
    grind [endpt_mapPath, isPath_mapPath]⟩

theorem endpt_mapPathFrom :
    endpt Y (h.onV x₀) (mapPathFrom x₀ h p).1 = h.onV (endpt X x₀ p.1) :=
  by apply endpt_mapPath

/-- The map of universal covers induced by a cellular map, on vertices. -/
def univLiftV (c : UV X x₀) : UV Y (h.onV x₀) :=
  Quotient.map (mapPathFrom x₀ h) (by
    intro p q hpq
    show Htpy Y (h.onV x₀) (endpt Y (h.onV x₀) (mapPathFrom x₀ h p).1)
      (mapPathFrom x₀ h p).1 (mapPathFrom x₀ h q).1
    rw [endpt_mapPathFrom]
    exact mapPath_htpy h hpq) c

@[simp] theorem univLiftV_mk (p : PathFrom X x₀) :
    univLiftV x₀ h (UV.mk p) = UV.mk (mapPathFrom x₀ h p) := rfl

@[simp] theorem endV_univLiftV (c : UV X x₀) :
    endV (univLiftV x₀ h c) = h.onV (endV c) := by
  induction c using UV.ind with
  | h p => exact endpt_mapPathFrom x₀ h p

/-- On germs issued from the endpoint, the lift commutes with extension of classes. -/
theorem univLiftV_extend {eb : X.E × Bool} {c : UV X x₀}
    (hc : endV c = germSrc X.src X.tgt eb) :
    univLiftV x₀ h (extend eb c) = extend (h.onE eb.1, eb.2) (univLiftV x₀ h c) := by
  induction c using UV.ind with
  | h p =>
      have hpos : endpt X x₀ p.1 = germSrc X.src X.tgt eb := hc
      have hpos' : endpt Y (h.onV x₀) (mapPathFrom x₀ h p).1
          = germSrc Y.src Y.tgt (h.onE eb.1, eb.2) := by
        rw [endpt_mapPathFrom, (germSrc_onE h eb), hpos]
      have hl : (mapPathFrom x₀ h (extendP eb p)).1
          = (extendP (h.onE eb.1, eb.2) (mapPathFrom x₀ h p)).1 := by
        rw [extendP_pos hpos']
        show mapPath h _ = mapPath h p.1 ++ [(h.onE eb.1, eb.2)]
        simp_all [extendP_pos, mapPath]
      refine Quotient.sound ?_
      show Htpy Y _ _
        _ _
      rw [hl]
      exact Htpy.refl _

/-- The map of universal covers induced by a cellular map, on edges. -/
def univLiftE (E : UE X x₀) : UE Y (h.onV x₀) :=
  ⟨(univLiftV x₀ h E.1.1, h.onE E.1.2), by
    simp [endV_univLiftV, E.2, h.src_onE]⟩

/-- The map of universal covers induced by a cellular map, on two-cells. -/
def univLiftF (F : UF X x₀) : UF Y (h.onV x₀) :=
  ⟨(univLiftV x₀ h F.1.1, h.onF F.1.2), by
    simp [endV_univLiftV, F.2, h.base_onF]⟩

theorem univLiftV_liftGerm {c : UV X x₀} {eb : X.E × Bool}
    (hc : endV c = germSrc X.src X.tgt eb)
    (hc' : endV _ = germSrc Y.src Y.tgt _) :
    liftGerm (univLiftV x₀ h c) (h.onE eb.1, eb.2) hc'
      = (univLiftE x₀ h (liftGerm c eb hc).1, (liftGerm c eb hc).2) := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => rfl
  | false =>
      refine Prod.ext ?_ rfl
      refine Subtype.ext (Prod.ext ?_ rfl)
      exact (univLiftV_extend x₀ h hc).symm

theorem uLiftPath_univLiftV : ∀ (q : List _) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w →
      uLiftPath (mapPath h q) (univLiftV x₀ h c)
        = (uLiftPath q c).map (fun Eb => (univLiftE x₀ h Eb.1, Eb.2)) := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro c w hq
      have hc := hq.1
      have hc' : endV (univLiftV x₀ h c) = germSrc Y.src Y.tgt (h.onE eb.1, eb.2) := by
        simp [endV_univLiftV, germSrc_onE, hc]
      have hnext : IsPath X.src X.tgt t (endV (extend eb c)) w := by
        rw [endV_extend hc]; exact hq.2
      show uLiftPath ((h.onE eb.1, eb.2) :: mapPath h t) _ = _
      grind [uLiftPath_cons, univLiftV_liftGerm, univLiftV_extend, extend]

variable (X) in
/-- **The lift of a cellular map to the universal covers.** -/
def univLift (x₀ : X.V) :
    Hom (uCover X x₀) (uCover Y (h.onV x₀)) where
  onV := univLiftV x₀ h
  onE := univLiftE x₀ h
  onF := univLiftF x₀ h
  src_onE := fun _ => rfl
  tgt_onE := by
    intro E
    exact (univLiftV_extend x₀ h (eb := (E.1.2, true)) E.2).symm
  base_onF := fun _ => rfl
  att_onF := by
    intro F
    have hatt : IsPath X.src X.tgt (X.att F.1.2) (endV F.1.1) (X.base F.1.2) := by
      rw [F.2]; apply X.att_isLoop
    show uLiftPath (Y.att (h.onF F.1.2)) _ = _
    rw [h.att_onF _]
    apply uLiftPath_univLiftV <;> assumption

/-! ### `π₂`, the Hurewicz map and the Cockcroft property -/

variable (x₀ : X.V)

variable (X) in
/-- **The second homotopy module** of a two-complex at a base vertex: the two-cycles of its
universal cover.  (A two-complex has no three-cells, so `π₂ = H₂` of the universal cover is
the kernel of `∂₂`.) -/
def Pi2 :=
  LinearMap.ker (bdry2 (uCover X x₀))

variable (X) in
/-- **The Hurewicz map** `π₂(X) → H₂(X)`: push a two-cycle of the universal cover down to the
complex. -/
def hurewicz :=
  chain2 (univProj X x₀)

variable (X) in
/-- **The Cockcroft property**: the Hurewicz map `π₂(X) → H₂(X)` vanishes. -/
def IsCockcroft :=
  ∀ (x₀ : X.V) (c : (uCover X x₀).F →₀ ℤ), c ∈ Pi2 X x₀ → hurewicz X x₀ c = 0

variable (h : Hom X Y)

/-- **A cellular map is zero on `π₂`**: the induced map of two-chains of the universal covers
kills every two-cycle. -/
def ZeroPi2 :=
  ∀ (x₀ : X.V) (c : (uCover X x₀).F →₀ ℤ), c ∈ Pi2 X x₀ → chain2 (univLift X h x₀) c = 0

/-- The lift of a cellular map carries `π₂` into `π₂`. -/
theorem mem_pi2_chain2_univLift {x₀ : X.V} {c : (uCover X x₀).F →₀ ℤ}
    (hc : c ∈ Pi2 X x₀) : chain2 (univLift X h x₀) c ∈ Pi2 Y _ := by
  have hchain := bdry2_chain2 (univLift X h x₀) c
  have hzero : bdry2 _ c = 0 := hc
  aesop

end Comb
end FiniteChains
