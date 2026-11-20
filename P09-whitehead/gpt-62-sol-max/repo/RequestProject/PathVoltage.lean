module

public import RequestProject.CellComplex

@[expose] public section

namespace FiniteChains.Comb.PathVoltage

variable {E G : Type*} [Group G] (v : E × Bool → G)

/-- A reversed germ is based at the sheet it reaches. -/
def liftGerm (g : G) (e : E × Bool) : (G × E) × Bool :=
  if e.2 then ((g, e.1), true) else ((g * v e, e.1), false)

def liftPath : List (E × Bool) → G → List ((G × E) × Bool)
  | [], _ => []
  | e :: p, g => liftGerm v g e :: liftPath p (g * v e)

@[simp] theorem liftGerm_projection (g : G) (e : E × Bool) :
    ((liftGerm v g e).1.2, (liftGerm v g e).2) = e := by
  obtain ⟨e, b⟩ := e
  cases b <;> rfl

theorem liftPath_projection (p : List (E × Bool)) (g : G) :
    (liftPath v p g).map (fun e => (e.1.2, e.2)) = p := by
  induction p generalizing g <;> simp [liftPath, *]

/-- The vertex packing can forget the base vertex in a one-vertex presentation. -/
theorem liftPath_isPath {V W : Type*} (src tgt : E → V) (pack : G × V → W)
    (hinv : ∀ e, v (e, false) = (v (e, true))⁻¹)
    {p : List (E × Bool)} {a b : V} (hp : IsPath src tgt p a b) (g : G) :
    IsPath (fun e => pack (e.1, src e.2)) (fun e => pack (e.1 * v (e.2, true), tgt e.2))
      (liftPath v p g) (pack (g, a)) (pack (g * (p.map v).prod, b)) := by
  induction p generalizing g a with
  | nil => simpa [liftPath, IsPath] using congrArg (fun a => pack (g, a)) hp
  | cons e p ih =>
      obtain ⟨rfl, hp⟩ := hp
      obtain ⟨e, b⟩ := e
      cases b <;> simp only [liftPath, liftGerm, Bool.false_eq_true, ite_false, ite_true,
        List.map_cons, List.prod_cons, IsPath, germSrc, germTgt, ← mul_assoc]
      · exact ⟨by simp [hinv, mul_assoc], ih hp _⟩
      · exact ⟨trivial, ih hp _⟩

/-- Edge relabeling and compatible sheet maps commute with the same lift. -/
theorem liftPath_map {F H : Type*} [Group H] (w : F × Bool → H)
    (f : E → F) (s : G → H) (h : ∀ g e, s (g * v e) = s g * w (f e.1, e.2))
    (p : List (E × Bool)) (g : G) :
    (liftPath v p g).map (fun e => ((s e.1.1, f e.1.2), e.2)) =
      liftPath w (p.map fun e => (f e.1, e.2)) (s g) := by
  induction p generalizing g with
  | nil => rfl
  | cons e p ih =>
      obtain ⟨e, b⟩ := e
      cases b <;> simp [liftPath, liftGerm, ih, h]

end FiniteChains.Comb.PathVoltage
