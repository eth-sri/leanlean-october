import RequestProject.TreeCover
import RequestProject.Tac
noncomputable section


/-! Actual lifted paths with coefficients in an arbitrary receiving group. -/
bwd

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G)

def germValue (e : K.E × Bool) :=
  φ (QuotientGroup.mk (germWord T e))

def wordValue (p : List (K.E × Bool)) :=
  φ (QuotientGroup.mk (pathWord T p))

@[simp] theorem wordValue_nil : wordValue T φ [] = 1 := by
  simp [wordValue, pathWord_nil]

theorem wordValue_cons e p :
    wordValue T φ (e :: p) = germValue T φ e * wordValue T φ p := by
  rw [wordValue, pathWord_cons, QuotientGroup.mk_mul, map_mul]
  rfl

theorem germValue_revGerm e :
    germValue T φ (revGerm e) = (germValue T φ e)⁻¹ := by
  rw [germValue, germWord_revGerm, QuotientGroup.mk_inv, map_inv]
  rfl

theorem germValue_false_eq_inv e :
    germValue T φ (e, false) = (germValue T φ (e, true))⁻¹ := by
  simpa [revGerm] using germValue_revGerm T φ (e, true)

theorem germValue_false_mul_true e :
    germValue T φ (e, false) * germValue T φ (e, true) = 1 := by
  rw [germValue_false_eq_inv, inv_mul_cancel]

@[simp] theorem wordValue_treePath a : wordValue T φ (T.treePath a) = 1 := by
  simp [wordValue, pathWord_treePath]

theorem wordValue_att f : wordValue T φ (K.att f) = 1 := by
  have h : (QuotientGroup.mk (treeRel T f) : PresGroup (treeRel T)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_range_self f))
  change φ (QuotientGroup.mk (treeRel T f)) = 1
  grind

def src (x : G × K.E) := (x.1, K.src x.2)

def tgt (x : G × K.E) :=
  (x.1 * germValue T φ (x.2, true), K.tgt x.2)

def liftGerm (g : G) (e : K.E × Bool) :=
  if e.2 then ((g, e.1), true) else ((g * germValue T φ e, e.1), false)

def liftPath : List (K.E × Bool) → G → List ((G × K.E) × Bool)
  | [], _ => []
  | e :: p, g => liftGerm T φ g e :: liftPath p (g * germValue T φ e)

@[simp] theorem liftPath_nil g : liftPath T φ [] g = [] := rfl

@[simp] theorem liftPath_cons e p g :
    liftPath T φ (e :: p) g = liftGerm T φ g e :: liftPath T φ p (g * germValue T φ e) := rfl

@[simp] theorem liftGerm_projection g e :
    ((liftGerm T φ g e).1.2, (liftGerm T φ g e).2) = e := by
  grind [liftGerm]

theorem germSrc_liftGerm g e :
    germSrc (src (K := K)) (tgt T φ) (liftGerm T φ g e) = (g, gSrcX K e) := by
  cases' e with e b
  cases b
  · change (g * germValue T φ (e, false) * germValue T φ (e, true), K.tgt e) = _
    rw [mul_assoc, germValue_false_mul_true, mul_one]
    rfl
  · rfl

theorem germTgt_liftGerm g e :
    germTgt (src (K := K)) (tgt T φ) (liftGerm T φ g e) =
      (g * germValue T φ e, gTgtX K e) := by
  cases' e with e b
  cases b <;> rfl

theorem liftPath_projection p g :
    (liftPath T φ p g).map (fun eb => (eb.1.2, eb.2)) = p := by
  induction p generalizing g <;> simp_all

theorem liftPath_translate p h g :
    liftPath T φ p (h * g) =
      (liftPath T φ p g).map (fun eb => ((h * eb.1.1, eb.1.2), eb.2)) := by
  induction p generalizing g with
  | nil => rfl
  | cons e p ih =>
    have he : liftGerm T φ (h * g) e =
        ((h * (liftGerm T φ g e).1.1, (liftGerm T φ g e).1.2), (liftGerm T φ g e).2) := by
      grind [liftGerm, mul_assoc]
    simp [liftPath_cons, he, mul_assoc, ih]

theorem liftPath_isPath
    (hp : IsPathX K p a b) g :
    IsPath (src (K := K)) (tgt T φ) (liftPath T φ p g)
      (g, a) (g * wordValue T φ p, b) := by
  induction p generalizing a g with
  | nil =>
    simp_all
  | cons e p ih =>
    cases' hp with ha hp
    subst a
    refine ⟨?_, ?_⟩
    · rw [germSrc_liftGerm]
    · rw [germTgt_liftGerm, wordValue_cons, ← mul_assoc]
      simp_all
