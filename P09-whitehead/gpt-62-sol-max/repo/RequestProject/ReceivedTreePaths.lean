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

noncomputable def germValue (e : K.E × Bool) : G :=
  φ (QuotientGroup.mk (germWord T e))

noncomputable def wordValue (p : List (K.E × Bool)) : G :=
  φ (QuotientGroup.mk (pathWord T p))

@[simp] theorem wordValue_nil : wordValue T φ [] = 1 := by
  simp [wordValue, pathWord_nil]

theorem wordValue_cons (e : K.E × Bool) (p : List (K.E × Bool)) :
    wordValue T φ (e :: p) = germValue T φ e * wordValue T φ p := by
  rw [wordValue, pathWord_cons, QuotientGroup.mk_mul, map_mul]
  rfl

theorem wordValue_att (f : K.F) : wordValue T φ (K.att f) = 1 := by
  have h : (QuotientGroup.mk (treeRel T f) : PresGroup (treeRel T)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_range_self f))
  change φ (QuotientGroup.mk (treeRel T f)) = 1
  rw [h, map_one]

abbrev freeReceiver : FreeGroup (NonTree T) →* G := φ.comp (QuotientGroup.mk' _)

abbrev src (x : G × K.E) := TreeVoltage.src (K := K) x
abbrev tgt := TreeVoltage.tgt T (freeReceiver T φ)
abbrev liftGerm := TreeVoltage.liftGerm T (freeReceiver T φ)
abbrev liftPath := TreeVoltage.liftPath T (freeReceiver T φ)


theorem liftPath_projection (p : List (K.E × Bool)) (g : G) :
    (liftPath T φ p g).map (fun eb => (eb.1.2, eb.2)) = p :=
  TreeVoltage.liftPath_projection T (freeReceiver T φ) p g

theorem liftPath_translate (p : List (K.E × Bool)) (h g : G) :
    liftPath T φ p (h * g) =
      (liftPath T φ p g).map (fun eb => ((h * eb.1.1, eb.1.2), eb.2)) :=
  (TreeVoltage.liftPath_map T (freeReceiver T φ) (freeReceiver T φ) (h * ·)
    (fun _ _ => (mul_assoc _ _ _).symm) p g).symm

theorem liftPath_isPath {p : List (K.E × Bool)} {a b : K.V}
    (hp : IsPath K.src K.tgt p a b) (g : G) :
    IsPath (src (K := K)) (tgt T φ) (liftPath T φ p g)
      (g, a) (g * wordValue T φ p, b) :=
  TreeVoltage.liftPath_isPath T (freeReceiver T φ) hp g

end FiniteChains.Comb.ReceivedTree
