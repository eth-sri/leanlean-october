module

public import RequestProject.BlockSpinePres
public import RequestProject.OrderCocycleChains
public import RequestProject.OrderCocyclePotential
public import RequestProject.GenusSurfaceMonodromyExt
public import RequestProject.GenusChainCollapse

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Comb.OrdCocycle
universe u v w
variable {P Q : Type u} [Preorder P] [Preorder Q]
  {G : Type v} [Group G] {H : Type w} [Group H]

theorem eq_of_val_eq {c d : OrdCocycle P G} (h : ∀ a b, c.val a b = d.val a b) : c = d := by
  cases c; cases d; congr; exact funext fun a => funext (h a)

theorem comap_readPath (c : OrdCocycle Q G) (f : P → Q) (hf : Monotone f) :
    ∀ p : List ((orderCx P).E × Bool),
      (c.comap f hf).readPath p = c.readPath (mapPath (orderCxMap f hf) p)
  | [] => rfl
  | e :: p => by simp only [mapPath, List.map_cons]; rw [readPath_cons, readPath_cons, comap_readPath c f hf p]; rfl

def postcompose (c : OrdCocycle P G) (φ : G →* H) : OrdCocycle P H where
  val a b := φ (c.val a b)
  comp hab hbc := by rw [← map_mul, c.comp hab hbc]

theorem postcompose_readPath (c : OrdCocycle P G) (φ : G →* H) :
    ∀ p : List ((orderCx P).E × Bool), (c.postcompose φ).readPath p = φ (c.readPath p)
  | [] => (map_one φ).symm
  | ⟨_, b⟩ :: p => by
      rw [readPath_cons, readPath_cons, map_mul, postcompose_readPath c φ p]
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
  ⟨d.1.spx, Finset.nonempty_iff_ne_empty.mpr (fun h => d.2 ⟨h, hd⟩), d.1.isSimplex⟩

variable (old : OrdCocycle (QOld A) G) (base : OrdCocycle X G) (k : NeSpx A → G)

def quotientCocycleValue : Qpos A X att → Qpos A X att → G
  | .inl d, .inl e => old.val d e
  | .inl _, .inr _ => 1
  | .inr x, .inl e => if he : e.1.sgn = 0 then
      base.val x (att (positiveOldSimplex e he)) * (k (positiveOldSimplex e he))⁻¹
    else 1
  | .inr x, .inr y => base.val x y

variable (hk : ∀ {s t : NeSpx A}, s ≤ t →
  old.val (posQCube s) (posQCube t) * k t = k s * base.val (att s) (att t))

include hk in
def gluedQuotientCocycle : OrdCocycle (Qpos A X att) G where
  val := quotientCocycleValue old base k
  comp {a b c} hab hbc := by
    classical
    have hmixed (x : X) (e : QOld A) (he : e.1.sgn = 0) :
        quotientCocycleValue (att := att) old base k (.inr x) (.inl e) =
          base.val x (att (positiveOldSimplex e he)) * (k (positiveOldSimplex e he))⁻¹ := by
      simp only [quotientCocycleValue, dif_pos he]
    rcases a with d | x <;> rcases b with e | y <;> rcases c with f | z
    · exact old.comp hab hbc
    · exact False.elim hbc
    · exact False.elim hab
    · exact False.elim hab
    · have he : e.1.sgn = 0 := hab.1
      have hf : f.1.sgn = 0 := funext fun z => by
        by_cases hz : z ∈ f.1.spx
        · exact f.1.sgn_eq_zero z hz
        · exact (hbc.2 z hz).symm.trans (congrFun he z)
      have hef : positiveOldSimplex e he ≤ positiveOldSimplex f hf := hbc.1
      have hpos (w : QOld A) (hw : w.1.sgn = 0) : posQCube (positiveOldSimplex w hw) = w :=
        Subtype.ext (QCube.ext' rfl fun z _ => (congrFun hw z).symm)
      have hg := hk hef; rw [hpos, hpos] at hg
      have ht : (k (positiveOldSimplex e he))⁻¹ * old.val e f =
          base.val (att (positiveOldSimplex e he)) (att (positiveOldSimplex f hf)) *
            (k (positiveOldSimplex f hf))⁻¹ := by
        calc _ = (k (positiveOldSimplex e he))⁻¹ * (old.val e f * k (positiveOldSimplex f hf)) *
              (k (positiveOldSimplex f hf))⁻¹ := by group
          _ = _ := by rw [hg]; group
      rw [hmixed x e he, hmixed x f hf]
      have hx : x ≤ att (positiveOldSimplex e he) := hab.2.2
      change (base.val x (att (positiveOldSimplex e he)) * (k (positiveOldSimplex e he))⁻¹) * old.val e f = _
      rw [mul_assoc, ht, ← mul_assoc, base.comp hx (att.monotone hef)]
    · exact False.elim hbc
    · have hf : f.1.sgn = 0 := hbc.1
      have hy : y ≤ att (positiveOldSimplex f hf) := hbc.2.2
      rw [hmixed y f hf, hmixed x f hf]
      change base.val x y * (base.val y (att (positiveOldSimplex f hf)) * _) = _
      rw [← mul_assoc, base.comp hab hy]
    · exact base.comp hab hbc

def quotientOldBasedInclusion (s : NeSpx A) :
    Pi1 (orderCx (QOld A)) (posQCube s) →*
      Pi1 (orderCx (Qpos A X att)) (qNew (att := att) (att s)) :=
  (pi1Conj (isPath_ordPos (qNew_att_le_qOldIncl (att := att) s))).comp
    (pi1Map (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) (posQCube s))

theorem monodromy_quotientOldBasedInclusion (s : NeSpx A)
    (c : OrdCocycle (Qpos A X att) G) (χ : Pi1 (orderCx (QOld A)) (posQCube s) →* G)
    (hcyl : c.val (qNew (att s)) (qOldIncl (posQCube s)) = 1)
    (hread : ∀ p : Loop (orderCx (QOld A)) (posQCube s),
      c.readPath (mapPath (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) p.1) =
        χ (Pi1.mk p)) :
    (c.monodromy (qNew (att s))).comp (quotientOldBasedInclusion (att := att) s) = χ := by
  refine MonoidHom.ext fun z => Quotient.inductionOn z fun p => ?_
  change c.readPath
    (([ordPos (qNew_att_le_qOldIncl (att := att) s)] ++
      mapPath (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) p.1) ++
      revPath [ordPos (qNew_att_le_qOldIncl (att := att) s)]) = _
  simp only [OrdCocycle.readPath_append, OrdCocycle.readPath_revPath,
    OrdCocycle.readPath_cons, OrdCocycle.readPath_nil,
    OrdCocycle.readGerm_ordPos, hcyl, one_mul, mul_one, inv_one]
  exact hread p

theorem monodromy_quotientBaseInclusion (x : X)
    (c : OrdCocycle (Qpos A X att) G) (d : OrdCocycle X G)
    (hd : ∀ a b, c.val (qNew a) (qNew b) = d.val a b) :
    (c.monodromy (qNew x)).comp
      (pi1Map (orderCxMap (qNew (A := A) (att := att)) qNew_monotone) x) =
        d.monodromy x := by
  have he : c.comap (qNew (A := A) (att := att)) qNew_monotone = d := OrdCocycle.eq_of_val_eq hd
  refine MonoidHom.ext fun z => Quotient.inductionOn z fun p => ?_
  change c.readPath (mapPath (orderCxMap (qNew (A := A) (att := att)) qNew_monotone) p.1) = _
  rw [← OrdCocycle.comap_readPath, he]; rfl

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
universe v
variable (q : ℕ) [NeZero q] {X : Type} [Preorder X]
  (att : NeSpx (cmpRel (GenusVertex q)) →o X) {G : Type v} [Group G]
  (old : OrdCocycle (QOld (cmpRel (GenusVertex q))) G) (base : OrdCocycle X G)

theorem exists_quotientCocycle_of_marked
    (hm : ∀ x : Fin q × Bool,
      old.readPath (mapPath (surfCx (cmpRel (GenusVertex q)))
        (gSig q (x.1.val, x.2))) =
      base.readPath (mapPath (orderCxMap att att.monotone) (gSig q (x.1.val, x.2)))) :
    ∃ c : OrdCocycle (Qpos (cmpRel (GenusVertex q)) X att) G,
      (∀ d e, c.val (qOldIncl d) (qOldIncl e) = old.val d e) ∧
      (∀ x y, c.val (qNew x) (qNew y) = base.val x y) ∧
      c.val (qNew (att (gBase q))) (qOldIncl (posQCube (gBase q))) = 1 := by
  obtain ⟨k, hb, hk⟩ := genus_cocycle_gauge_of_marked q
    (old.comap posQCube posQCube_monotone) (base.comap att att.monotone)
    (fun x => by simpa only [OrdCocycle.comap_readPath, surfCx] using hm x)
  refine ⟨gluedQuotientCocycle old base k (hk := hk), fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  change quotientCocycleValue old base k (.inr (att (gBase q))) (.inl (posQCube (gBase q))) = 1
  simp [quotientCocycleValue,
    show positiveOldSimplex (posQCube (gBase q)) rfl = gBase q from Subtype.ext rfl, hb]
