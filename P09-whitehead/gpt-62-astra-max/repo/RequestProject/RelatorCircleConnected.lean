module

public import RequestProject.RelatorCircleEdges
public import RequestProject.OrderConstructionConnected

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- Consecutive actual circle corners lie in the same actual edge-path component. -/
theorem relatorCircle_corner_component_next (k : Fin _) :
    orderComponentLabel _
      (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) =
    orderComponentLabel _ (relatorCirclePoint w j k CPos.cor) :=
  (orderComponentLabel_eq_of_le (relatorCircleEdge3 w j k).property.le).trans
    ((orderComponentLabel_eq_of_le (relatorCircleEdge2 w j k).property.le).symm.trans
      ((orderComponentLabel_eq_of_le (relatorCircleEdge1 w j k).property.le).trans
        (orderComponentLabel_eq_of_le (relatorCircleEdge0 w j k).property.le).symm))

variable (hpos : 0 < (w j).length)
include hpos

/-- Every actual circle corner is connected to the actual initial corner. -/
theorem relatorCircle_corner_component_zero
    (k : Fin _) :
    orderComponentLabel _ (relatorCirclePoint w j k CPos.cor) =
      orderComponentLabel _ (relatorCirclePoint w j ⟨0, hpos⟩ CPos.cor) := by
  have h : ∀ n (hn : n < (w j).length),
      orderComponentLabel _ (relatorCirclePoint w j ⟨n, hn⟩ CPos.cor) =
        orderComponentLabel _ (relatorCirclePoint w j ⟨0, hpos⟩ CPos.cor) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have he : relatorCircleNext w j ⟨n, (by omega)⟩ = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hn
      grind [relatorCircle_corner_component_next]
  exact h k.val k.isLt

/-- Each nonempty genuine relator circle is connected by actual order-complex edge paths. -/
theorem relatorCircle_isConnected :
    IsConnected (orderCx (RelatorCircle w j)) := by
  have h : ∀ x : RelatorCircle w j,
      orderComponentLabel _ x =
        orderComponentLabel _ (relatorCirclePoint w j ⟨0, hpos⟩ CPos.cor) := by
    rintro ⟨⟨j', k, t⟩, hj, hk⟩
    change j' = j at hj
    subst j'
    let n : Fin _ := ⟨k, hk⟩
    have hc := relatorCircle_corner_component_zero w j hpos n
    cases t with
    | cor => exact hc
    | cmid =>
        exact (orderComponentLabel_eq_of_le (relatorCircleEdge1 w j n).property.le).trans
          ((orderComponentLabel_eq_of_le (relatorCircleEdge0 w j n).property.le).symm.trans hc)
    | cedgL =>
        exact (orderComponentLabel_eq_of_le (relatorCircleEdge0 w j n).property.le).symm.trans hc
    | cedgR =>
        exact (orderComponentLabel_eq_of_le (relatorCircleEdge2 w j n).property.le).symm.trans
          ((orderComponentLabel_eq_of_le (relatorCircleEdge1 w j n).property.le).trans
            ((orderComponentLabel_eq_of_le (relatorCircleEdge0 w j n).property.le).symm.trans hc))
  intro x y
  exact (orderComponentLabel_eq_iff _ _).mp ((h x).trans (h y).symm)

end FiniteChains.PresModel
