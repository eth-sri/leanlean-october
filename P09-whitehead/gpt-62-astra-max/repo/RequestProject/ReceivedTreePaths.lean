module

public import RequestProject.TreeCover

@[expose] public section

/-! Actual lifted paths with coefficients in an arbitrary receiving group. -/

noncomputable section

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G)

def germValue (e : K.E × Bool) :=
  φ (QuotientGroup.mk (germWord T e))

def wordValue (p : List _) :=
  φ (QuotientGroup.mk (pathWord T p))

@[simp] theorem wordValue_nil : wordValue T φ [] = 1 := by
  simp [wordValue, pathWord_nil]

variable (e : K.E × Bool)

theorem wordValue_cons (p : List _) :
    wordValue T φ (e :: p) = germValue T φ e * wordValue T φ p := by
  rw [wordValue, pathWord_cons, QuotientGroup.mk_mul, map_mul]
  rfl

theorem germValue_revGerm :
    germValue T φ (revGerm e) = (germValue T φ e)⁻¹ := by
  simp [germValue, germWord_revGerm, QuotientGroup.mk_inv, map_inv]

variable (e : K.E)

theorem germValue_false_eq_inv :
    germValue T φ (e, false) = (germValue T φ (e, true))⁻¹ := by
  simpa [revGerm] using germValue_revGerm T φ (e, true)

theorem germValue_false_mul_true :
    germValue T φ (e, false) * germValue T φ (e, true) = 1 := by
  rw [germValue_false_eq_inv, inv_mul_cancel]

@[simp] theorem wordValue_treePath (a : K.V) : wordValue T φ (T.treePath a) = 1 := by
  simp [wordValue, pathWord_treePath]

theorem wordValue_att (f : K.F) : wordValue T φ (K.att f) = 1 := by
  have h : (QuotientGroup.mk _ : PresGroup (treeRel T)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_range_self f))
  change φ (QuotientGroup.mk (treeRel T f)) = 1
  grind

variable (x : G × K.E)

def src := (x.1, K.src x.2)

def tgt :=
  (x.1 * germValue T φ (x.2, true), K.tgt x.2)

def liftGerm (g : G) (e : K.E × Bool) :=
  if e.2 then ((g, e.1), true) else ((g * germValue T φ e, e.1), false)

def liftPath : List (K.E × Bool) → G → List ((G × K.E) × Bool)
  | [], _ => []
  | e :: p, g => liftGerm T φ g e :: liftPath p (g * germValue T φ e)

@[simp] theorem liftPath_nil (g : G) : liftPath T φ [] g = [] := rfl

@[simp] theorem liftPath_cons (e : K.E × Bool) (p : List _) (g : G) :
    liftPath T φ (e :: p) g = liftGerm T φ g e :: liftPath T φ p (g * germValue T φ e) := rfl

variable (g : G) (e : K.E × Bool)

@[simp] theorem liftGerm_projection :
    ((liftGerm T φ g e).1.2, (liftGerm T φ g e).2) = e := by
  obtain ⟨e, b⟩ := e
  cases b <;> simp [liftGerm]

theorem germSrc_liftGerm :
    germSrc (src (K := K)) (tgt T φ) (liftGerm T φ g e) = (g, germSrc K.src K.tgt e) := by
  obtain ⟨e, b⟩ := e
  cases b
  · change (g * germValue T φ _ * germValue T φ (e, true), K.tgt e) = _
    simp [mul_assoc, germValue_false_mul_true, mul_one]
  · rfl

theorem germTgt_liftGerm :
    germTgt (src (K := K)) (tgt T φ) (liftGerm T φ g e) =
      (g * germValue T φ e, germTgt K.src K.tgt e) := by
  obtain ⟨e, b⟩ := e
  cases b <;> rfl

variable (p : List (K.E × Bool))

theorem liftPath_projection (g : G) :
    (liftPath T φ p g).map (fun eb => (eb.1.2, eb.2)) = p := by
  induction p generalizing g with
  | nil => rfl
  | cons e p ih => simp [ih]

theorem liftPath_translate (h g : G) :
    liftPath T φ p (h * g) =
      (liftPath T φ p g).map (fun eb => ((h * eb.1.1, eb.1.2), eb.2)) := by
  induction p generalizing g with
  | nil => rfl
  | cons e p ih =>
    have he : liftGerm T φ (h * g) e =
        ((h * (liftGerm T φ g e).1.1, (liftGerm T φ g e).1.2), (liftGerm T φ g e).2) := by
      obtain ⟨e, b⟩ := e
      grind [liftGerm, mul_assoc]
    grind [liftPath_cons]

theorem liftPath_isPath {p : List _} {a b : K.V}
    (hp : IsPath K.src K.tgt p a b) (g : G) :
    IsPath (src (K := K)) (tgt T φ) (liftPath T φ p g)
      (g, a) (g * wordValue T φ p, b) := by
  induction p generalizing a g with
  | nil =>
    simp_all
  | cons e p ih =>
    obtain ⟨ha, hp⟩ := hp
    subst a
    refine ⟨?_, ?_⟩
    · simp [germSrc_liftGerm]
    · grind [germTgt_liftGerm, wordValue_cons]

end FiniteChains.Comb.ReceivedTree
