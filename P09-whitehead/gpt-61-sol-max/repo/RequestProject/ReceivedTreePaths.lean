import Mathlib.Tactic

import RequestProject.TreeCover

/-! Actual lifted paths with coefficients in an arbitrary receiving group. -/

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G)

variable (e : K.E × Bool)
noncomputable def germValue   :=
  φ (QuotientGroup.mk (germWord T e))

variable (p : List (K.E × Bool))
noncomputable def wordValue   :=
  φ (QuotientGroup.mk (pathWord T p))

@[simp] theorem wordValue_nil : wordValue T φ [] = 1 := by
  simp [wordValue]

theorem wordValue_cons  (p : List (K.E × Bool)) :
    wordValue T φ (e :: p) = germValue T φ e * wordValue T φ p := by
  rw [wordValue, pathWord_cons, QuotientGroup.mk_mul, map_mul]
  rfl

theorem germValue_revGerm  :
    germValue T φ (revGerm e) = (germValue T φ e)⁻¹ := by
  rw [germValue, germWord_revGerm, QuotientGroup.mk_inv, map_inv]
  rfl

theorem germValue_false_eq_inv (e : K.E) :
    germValue T φ (e, false) = (germValue T φ (e, true))⁻¹ := by
  simpa [revGerm] using germValue_revGerm T φ (e, true)

theorem germValue_false_mul_true (e : K.E) :
    germValue T φ (e, false) * germValue T φ (e, true) = 1 := by
  rw [germValue_false_eq_inv, inv_mul_cancel]

@[simp] theorem wordValue_treePath (a : K.V) : wordValue T φ (T.treePath a) = 1 := by
  simp [wordValue]

theorem wordValue_att (f : K.F) : wordValue T φ (K.att f) = 1 := by
  have h : (QuotientGroup.mk (treeRel T f) : PresGroup (treeRel T)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_range_self f))
  change φ (QuotientGroup.mk (treeRel T f)) = 1
  rw [h, map_one]

def src (x : G × K.E)  := (x.1, K.src x.2)

noncomputable def tgt (x : G × K.E)  :=
  (x.1 * germValue T φ (x.2, true), K.tgt x.2)

variable (g : G)
  (e : K.E × Bool)
noncomputable def liftGerm    :=
  if e.2 then ((g, e.1), true) else ((g * germValue T φ e, e.1), false)

noncomputable def liftPath : List (K.E × Bool) → G → List ((G × K.E) × Bool)
  | [], _ => []
  | e :: p, g => liftGerm T φ g e :: liftPath p (g * germValue T φ e)

@[simp] theorem liftPath_nil  : liftPath T φ [] g = [] := rfl

@[simp] theorem liftPath_cons  (p : List (K.E × Bool)) (g : G) :
    liftPath T φ (e :: p) g = liftGerm T φ g e :: liftPath T φ p (g * germValue T φ e) := rfl

@[simp] theorem liftGerm_projection   :
    ((liftGerm T φ g e).1.2, (liftGerm T φ g e).2) = e := by aesop (add simp [liftGerm])

theorem germSrc_liftGerm   :
    germSrc (src (K := K)) (tgt T φ) (liftGerm T φ g e) = (g, germSrc K.src K.tgt e) := by
  obtain ⟨e, b⟩ := e
  cases b
  · change (g * germValue T φ (e, false) * germValue T φ (e, true), K.tgt e) = _
    rw [mul_assoc, germValue_false_mul_true, mul_one]
    rfl
  · rfl

theorem germTgt_liftGerm   :
    germTgt (src (K := K)) (tgt T φ) (liftGerm T φ g e) =
      (g * germValue T φ e, germTgt K.src K.tgt e) := by
  obtain ⟨e, b⟩ := e
  cases b <;> rfl

theorem liftPath_projection  (g : G) :
    (liftPath T φ p g).map (fun eb => (eb.1.2, eb.2)) = p := by
  induction p generalizing g <;> simp_all

theorem liftPath_translate  (h g : G) :
    liftPath T φ p (h * g) =
      (liftPath T φ p g).map (fun eb => ((h * eb.1.1, eb.1.2), eb.2)) := by
  induction p generalizing g <;> aesop (add simp [liftGerm, mul_assoc])

theorem liftPath_isPath {p : List (K.E × Bool)} {a b : K.V}
    (hp : IsPath K.src K.tgt p a b) (g : G) :
    IsPath (src (K := K)) (tgt T φ) (liftPath T φ p g)
      (g, a) (g * wordValue T φ p, b) := by
  induction p generalizing a g with
  | nil =>
    
    subst b
    simp
  | cons e p ih =>
    obtain ⟨ha, hp⟩ := hp
    subst a
    refine ⟨?_, ?_⟩
    · rw [germSrc_liftGerm]
    · grind [germTgt_liftGerm, wordValue_cons]

end FiniteChains.Comb.ReceivedTree
