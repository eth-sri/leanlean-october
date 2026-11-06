import RequestProject.BlockSpinePres
import RequestProject.OrderCocycleChains
import RequestProject.OrderCocyclePotential
import RequestProject.GenusSurfaceMonodromyExt
import RequestProject.GenusChainCollapse
import RequestProject.Tac
noncomputable section


/-! Explicit nonabelian cocycle gluing on the actual quotient Q.

The transition function comes from the marked surface theorem, not an assumed
presentation of its fundamental group. This is the geometric construction
needed for the reverse substituted-group comparison.
-/

bwd

namespace FiniteChains.Comb.OrdCocycle
universe u v w
variable {P Q : Type u} [Preorder P] [Preorder Q]
  {G : Type v} [Group G] {H : Type w} [Group H]

theorem eq_of_val_eq {c d : OrdCocycle P G} (h : ∀ a b, c.val a b = d.val a b) :
    c = d := by
  cases c with
  | mk cv cc =>
    cases d <;> aesop

theorem comap_readPath (c : OrdCocycle Q G) f hf
    (p : List ((orderCx P).E × Bool)) :
    (c.comap f hf).readPath p = c.readPath (mapPath (orderCxMap f hf) p) := by
  induction p <;> aesop

def postcompose (c : OrdCocycle P G) (φ : G →* H) : OrdCocycle P H where
  val a b := φ (c.val a b)
  comp hab hbc := by rw [← map_mul, c.comp hab hbc]

theorem postcompose_readPath (c : OrdCocycle P G) (φ : G →* H)
    p :
    (c.postcompose φ).readPath p = φ (c.readPath p) := by
  induction p with
  | nil => simp
  | cons e p ih =>
    rw [readPath_cons, readPath_cons, map_mul, ih]
    congr 1
    cases' e with e b
    cases b <;> simp [readGerm, postcompose]

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
universe u v
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [Preorder X] {att : NeSpx A →o X}
  {G : Type v} [Group G]

def positiveOldSimplex (d : QOld A) (hd : d.1.sgn = 0) : NeSpx A :=
  ⟨d.1.spx, by grind,
    d.1.isSimplex⟩

theorem posQCube_positiveOldSimplex (d : QOld A) hd :
    posQCube (positiveOldSimplex d hd) = d := by
  apply Subtype.ext
  apply QCube.ext'
  · rfl
  tauto

omit [DecidableEq V] in
theorem positiveOldSimplex_posQCube (s : NeSpx A) :
    positiveOldSimplex (posQCube s) rfl = s := by
  rfl

theorem positiveOld_upward {d e : QOld A} (hde : d ≤ e) (hd : d.1.sgn = 0) :
    e.1.sgn = 0 := by
  funext z
  by_cases hz : z ∈ e.1.spx
  · exact e.1.sgn_eq_zero z hz
  · rw [← hde.2 z hz]
    simp_all

theorem new_le_positiveOld
    (h : qNew (A := A) (att := att) x ≤ qOldIncl d) :
    x ≤ att (positiveOldSimplex d h.1) := by
  obtain ⟨_, hn, hx⟩ := h
  exact hx

variable (old : OrdCocycle (QOld A) G) (base : OrdCocycle X G)
  (k : NeSpx A → G)

def quotientCocycleValue : Qpos A X att → Qpos A X att → G
  | .inl d, .inl e => old.val d e
  | .inl _, .inr _ => 1
  | .inr x, .inl e => if he : e.1.sgn = 0 then
      base.val x (att (positiveOldSimplex e he)) * (k (positiveOldSimplex e he))⁻¹
    else 1
  | .inr x, .inr y => base.val x y

theorem quotientCocycleValue_mixed x e he :
    quotientCocycleValue (att := att) old base k (.inr x) (.inl e) =
      base.val x (att (positiveOldSimplex e he)) * (k (positiveOldSimplex e he))⁻¹ := by
  classical
  simp [quotientCocycleValue, dif_pos he]

variable (hk : ∀ {s t : NeSpx A}, s ≤ t →
  old.val (posQCube s) (posQCube t) * k t = k s * base.val (att s) (att t))

include hk in
theorem quotientCocycleValue_comp {a b c : Qpos A X att} (hab : a ≤ b) (hbc : b ≤ c) :
    quotientCocycleValue old base k a b * quotientCocycleValue old base k b c =
      quotientCocycleValue old base k a c := by
  classical
  cases a with
  | inl d =>
    cases b with
    | inl e =>
      cases c with
      | inl f => exact old.comp hab hbc
      | inr z => exact hbc.elim
    | inr y => exact hab.elim
  | inr x =>
    cases b with
    | inl e =>
      cases c with
      | inr z => exact hbc.elim
      | inl f =>
        have he := hab.1
        have hf := positiveOld_upward hbc he
        have hef : positiveOldSimplex e he ≤ positiveOldSimplex f hf := hbc.1
        have hx := new_le_positiveOld hab
        have hg := hk hef
        rw [posQCube_positiveOldSimplex, posQCube_positiveOldSimplex] at hg
        have ht : (k (positiveOldSimplex e he))⁻¹ * old.val e f =
            base.val (att (positiveOldSimplex e he)) (att (positiveOldSimplex f hf)) *
              (k (positiveOldSimplex f hf))⁻¹ := by
          calc
            _ = (k (positiveOldSimplex e he))⁻¹ *
                (old.val e f * k (positiveOldSimplex f hf)) *
                  (k (positiveOldSimplex f hf))⁻¹ := by group
            _ = _ := by simp_all
        rw [quotientCocycleValue_mixed old base k x e he,
          quotientCocycleValue_mixed old base k x f hf]
        change (base.val x (att (positiveOldSimplex e he)) *
            (k (positiveOldSimplex e he))⁻¹) * old.val e f = _
        rw [mul_assoc, ht, ← mul_assoc, base.comp hx (att.monotone hef)]
    | inr y =>
      cases c with
      | inr z => exact base.comp hab hbc
      | inl f =>
        have hf := hbc.1
        have hy := new_le_positiveOld hbc
        rw [quotientCocycleValue_mixed old base k y f hf,
          quotientCocycleValue_mixed old base k x f hf]
        change base.val x y * (base.val y (att (positiveOldSimplex f hf)) * _) = _
        rw [← mul_assoc, base.comp hab hy]

def gluedQuotientCocycle : OrdCocycle (Qpos A X att) G where
  val := quotientCocycleValue old base k
  comp := quotientCocycleValue_comp old base k hk



theorem gluedQuotientCocycle_cylinder (s : NeSpx A) :
    (gluedQuotientCocycle old base k hk).val
      (qNew (att := att) (att s)) (qOldIncl (posQCube s)) = (k s)⁻¹ := by
  change quotientCocycleValue old base k (.inr (att s)) (.inl (posQCube s)) = _
  rw [quotientCocycleValue_mixed old base k _ _ rfl,
    positiveOldSimplex_posQCube, base.val_refl, one_mul]

def quotientOldBasedInclusion s :=
  (pi1Conj (isPath_ordPos (qNew_att_le_qOldIncl (att := att) s))).comp
    (pi1Map (orderCxMap _ qOldIncl_monotone) _)

/-- The normalized cylinder edge makes the reverse reading on the based old
inclusion equal to the original old reading, without a conjugation factor. -/
theorem monodromy_quotientOldBasedInclusion s
    (c : OrdCocycle (Qpos A X att) G) χ
    (hcyl : c.val (qNew (att s)) (qOldIncl (posQCube s)) = 1)
    (hread : ∀ p,
      c.readPath (mapPath (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) p.1) =
        χ (Pi1.mk p)) :
    (c.monodromy (qNew (att s))).comp (quotientOldBasedInclusion (att := att) s) = χ := by
  apply MonoidHom.ext
  intro z
  refine Quotient.inductionOn z ?_
  intro p
  change c.readPath
    (([ordPos (qNew_att_le_qOldIncl (att := att) s)] ++
      mapPath (orderCxMap _ qOldIncl_monotone) p.1) ++
      revPath [ordPos (qNew_att_le_qOldIncl (att := att) s)]) = _
  aesop

theorem monodromy_quotientBaseInclusion x
    (c : OrdCocycle (Qpos A X att) G) (d : OrdCocycle X G)
    (hd : ∀ a b, c.val (qNew a) (qNew b) = d.val a b) :
    (c.monodromy (qNew x)).comp
      (pi1Map (orderCxMap (qNew (A := A) (att := att)) qNew_monotone) x) =
        d.monodromy x := by
  have he : c.comap _ qNew_monotone = d :=
    OrdCocycle.eq_of_val_eq hd
  apply MonoidHom.ext
  intro z
  refine Quotient.inductionOn z ?_
  intro p
  change c.readPath (mapPath (orderCxMap _ qNew_monotone) p.1) = _
  rw [← OrdCocycle.comap_readPath, he]
  rfl

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
universe v
variable (q : ℕ) [NeZero q] {X : Type} [Preorder X]
  (att : NeSpx (cmpRel (GenusVertex q)) →o X) {G : Type v} [Group G]
  (old : OrdCocycle (QOld (cmpRel (GenusVertex q))) G) (base : OrdCocycle X G)

/-- The actual standard marked equalities suffice to glue on Q, preserving
both original cocycles and giving value 1 to the base cylinder edge. -/
theorem exists_quotientCocycle_of_marked
    (hm : ∀ x : Fin q × Bool,
      old.readPath (mapPath (surfCx (cmpRel (GenusVertex q)))
        (gSig q (x.1.val, x.2))) =
      base.readPath (mapPath (orderCxMap att att.monotone) (gSig q (x.1.val, x.2)))) :
    ∃ c : OrdCocycle (Qpos (cmpRel (GenusVertex q)) X att) G,
      (∀ d e, c.val (qOldIncl d) (qOldIncl e) = old.val d e) ∧
      (∀ x y, c.val (qNew x) (qNew y) = base.val x y) ∧
      c.val (qNew (att (gBase q))) (qOldIncl (posQCube (gBase q))) = 1 := by
  have hm' : ∀ x : Fin q × Bool,
      (old.comap posQCube posQCube_monotone).readPath (gSig q (x.1.val, x.2)) =
      (base.comap att att.monotone).readPath (gSig q (x.1.val, x.2)) := by
    tauto
  obtain ⟨k, hb, hk⟩ := genus_cocycle_gauge_of_marked q
    _ _ hm'
  refine ⟨gluedQuotientCocycle old base k hk, ?_, ?_, ?_⟩
  · tauto
  · tauto
  · rw [gluedQuotientCocycle_cylinder, hb, inv_one]
