import RequestProject.Statement
import RequestProject.SquareBoundary
import Mathlib.Topology.Homotopy.Lifting
import RequestProject.Tac


/-! General topological covering/pi2 results moved unchanged from Solution. -/

bwd

namespace Whitehead
open scoped unitInterval Topology

/-- Covering maps reflect based homotopies of two-dimensional loops. -/
theorem mapSquare_homotopic_iff_of_covering {E X}
    [TopologicalSpace E] [TopologicalSpace X] (p : C(E, X))
    (hp : IsCoveringMap p) {e} (a b : GenLoop (Fin 2) E e) :
    GenLoop.Homotopic (mapSquare p a) (mapSquare p b) ↔ GenLoop.Homotopic a b := (hp.homotopicRel_iff_comp (f₀ := a.1) (f₁ := b.1) (S := Cube.boundary _)
    ⟨fun _ => 0, ⟨0, Or.inl rfl⟩,
      (GenLoop.boundary a _ ⟨0, Or.inl rfl⟩).trans (GenLoop.boundary b _ ⟨0, Or.inl rfl⟩).symm⟩).symm

theorem mapSquare_homotopic {X Y} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x} {p q : GenLoop (Fin 2) X x}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (mapSquare f p) (mapSquare f q) :=
  h.comp_continuousMap f


/-- The continuous map induced on Mathlib's topological second homotopy quotient. -/
def pi2Map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) x : HomotopyGroup (Fin 2) X x → HomotopyGroup (Fin 2) Y (f x) :=
  Quotient.map (mapSquare f) (fun _ _ h => mapSquare_homotopic f h)

/-- Radial contraction of the square, used to construct covering lifts directly. -/
def radialSquare : C(I × (Fin 2 → I), Fin 2 → I) where
  toFun ta i := ta.1 * ta.2 i
  continuous_toFun := continuous_pi (fun i =>
    (continuous_fst.subtype_val.mul
      (((continuous_apply i).comp continuous_snd).subtype_val)).subtype_mk _)

/-- A based square lifts through a covering map, including its constant boundary. -/
theorem exists_mapSquare_lift {E X} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (hp : IsCoveringMap p) e q :
    ∃ a : GenLoop (Fin 2) E e, mapSquare p a = q := by
  let z : Fin 2 → I := fun _ => 0
  have hz : z ∈ Cube.boundary _ := ⟨0, Or.inl rfl⟩
  let H := q.1.comp radialSquare
  have H0 : ∀ t, H (0, t) = p e := by
    intro t
    change q (0 * t ·) = p e
    aesop
  let F := hp.liftHomotopy H (ContinuousMap.const _ e) H0
  let G := F.comp ⟨fun t => (1, t), continuous_const.prodMk continuous_id⟩
  have hG : ∀ t, p (G t) = q t := by
    intro t
    have he := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (1, t)
    change p (F (1, t)) = q (1 * t ·) at he
    aesop

  have hbase : G z = e := by
    have he := hp.const_of_comp (g := fun t => F (t, z))
      (F.continuous.comp (continuous_id.prodMk continuous_const))
      (fun t s => by
        have ht := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (t, z)
        have hs := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (s, z)
        change p (F (t, z)) = q (t * z ·) at ht
        change p (F (s, z)) = q (s * z ·) at hs
        aesop) 1 0
    exact he.trans (hp.liftHomotopy_zero H _ H0 z)
  have hboundary : ∀ t ∈ Cube.boundary _, G t = e := by
    intro t ht
    have he := hp.constOn_of_comp square_boundary_isPreconnected G.continuous.continuousOn
      (fun a ha b hb => (hG a).trans
        ((GenLoop.boundary q a ha).trans ((GenLoop.boundary q b hb).symm.trans (hG b).symm)))
      ht hz
    exact he.trans hbase
  refine ⟨⟨G, hboundary⟩, ?_⟩
  aesop


/-- The square-map formulation in the challenge is exactly the zero-map condition on
Mathlib's topological homotopy group, not an auxiliary algebraic substitute. -/
theorem killsPi2_iff {X Y} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : KillsPi2 f ↔ ∀ x z, pi2Map f x z = 1 := by
  constructor
  · intro h x z
    induction z using Quotient.inductionOn with
    | _ p => exact Quotient.sound (h x p)
  · intro h x p
    exact Quotient.exact (h x (Quotient.mk _ p))

/-- Postcomposing with a covering reflects the zero-map condition on `π₂`. -/
theorem killsPi2_covering_postcomp_iff {Y E X}
    [TopologicalSpace Y] [TopologicalSpace E] [TopologicalSpace X]
    (f : C(Y, E)) (p : C(E, X)) (hp : IsCoveringMap p) :
    KillsPi2 (p.comp f) ↔ KillsPi2 f := by
  constructor
  · intro h y a
    apply (mapSquare_homotopic_iff_of_covering p hp _ GenLoop.const).mp
    tauto
  · intro h y a
    have he := mapSquare_homotopic p (h y a)
    tauto

/-- Surjective coverings also reflect the zero-map condition when precomposed. -/
theorem killsPi2_covering_precomp_iff {E X Y}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    (p : C(E, X)) (hp : IsCoveringMap p) (hs : Function.Surjective p)
    (f : C(X, Y)) : KillsPi2 (f.comp p) ↔ KillsPi2 f := by
  constructor
  · intro h x q
    obtain ⟨e, rfl⟩ := hs x
    obtain ⟨a, ha⟩ := exists_mapSquare_lift p hp e q
    aesop
  · intro h e a
    exact h _ (mapSquare p a)
