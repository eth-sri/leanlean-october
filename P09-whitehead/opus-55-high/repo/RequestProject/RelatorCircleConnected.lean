import RequestProject.RelatorCircleEdges
import RequestProject.OrderConstructionConnected


namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- Consecutive actual circle corners lie in the same actual edge-path component. -/
theorem relatorCircle_corner_component_next k :
    orderComponentLabel (RelatorCircle w j)
      (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) =
    orderComponentLabel (RelatorCircle w j) (relatorCirclePoint w j k CPos.cor) :=
  (orderComponentLabel_eq_of_le (relatorCircleEdge3 w j k).property.le).trans
    ((orderComponentLabel_eq_of_le (relatorCircleEdge2 w j k).property.le).symm.trans
      ((orderComponentLabel_eq_of_le (relatorCircleEdge1 w j k).property.le).trans
        (orderComponentLabel_eq_of_le (relatorCircleEdge0 w j k).property.le).symm))

/-- Every actual circle corner is connected to the actual initial corner. -/
theorem relatorCircle_corner_component_zero hpos
    k :
    orderComponentLabel (RelatorCircle w j) (relatorCirclePoint w j k CPos.cor) =
      orderComponentLabel (RelatorCircle w j) (relatorCirclePoint w j ⟨0, hpos⟩ CPos.cor) := by
  have h : ∀ n hn,
      orderComponentLabel _ (relatorCirclePoint w j ⟨n, hn⟩ CPos.cor) =
        orderComponentLabel _ (relatorCirclePoint w j ⟨0, hpos⟩ CPos.cor) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hn' : n < (w j).length := by omega
      have he : relatorCircleNext w j ⟨n, hn'⟩ = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hn
      exact (he ▸ relatorCircle_corner_component_next w j _).trans (ih hn')
  simp_all

/-- Each nonempty genuine relator circle is connected by actual order-complex edge paths. -/
theorem relatorCircle_isConnected (hpos : 0 < (w j).length) :
    IsConnected (orderCx (RelatorCircle w j)) := by
  have h : ∀ x,
      orderComponentLabel _ x =
        orderComponentLabel _ (relatorCirclePoint w j ⟨0, hpos⟩ CPos.cor) := by
    rintro ⟨⟨j', k, t⟩, hj, hk⟩
    change j' = j at hj
    subst j'
    let n : Fin (w j).length := by tauto
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
  exact (orderComponentLabel_eq_iff _ _).mp (by grind)
