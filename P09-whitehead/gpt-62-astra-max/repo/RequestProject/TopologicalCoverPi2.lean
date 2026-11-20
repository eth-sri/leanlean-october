module

public import RequestProject.Statement
public import RequestProject.SquareBoundary
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

/-! General topological covering/pi2 results moved unchanged from Solution. -/

namespace Whitehead
open scoped unitInterval Topology

/-- Covering maps reflect based homotopies of two-dimensional loops. -/
theorem mapSquare_homotopic_iff_of_covering {E X : Type}
    [TopologicalSpace E] [TopologicalSpace X] (p : C(E, X))
    (hp : IsCoveringMap p) {e : E} (a b : GenLoop _ E e) :
    GenLoop.Homotopic (mapSquare p a) (mapSquare p b) ↔ GenLoop.Homotopic a b := (hp.homotopicRel_iff_comp (S := Cube.boundary _)
    ⟨fun _ => 0, ⟨0, Or.inl rfl⟩,
      (GenLoop.boundary a _ ⟨0, Or.inl rfl⟩).trans (GenLoop.boundary b _ ⟨0, Or.inl rfl⟩).symm⟩).symm

section

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
include Y

theorem mapSquare_homotopic {x : X} {p q : GenLoop _ X x}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (mapSquare f p) (mapSquare f q) :=
  h.comp_continuousMap f

variable (x : X)

@[simp] theorem mapSquare_const : mapSquare f (GenLoop.const (x := x)) = GenLoop.const := rfl

/-- The continuous map induced on Mathlib's topological second homotopy quotient. -/
def pi2Map : HomotopyGroup (Fin 2) X x → HomotopyGroup (Fin 2) Y (f x) :=
  Quotient.map _ (fun _ _ h => mapSquare_homotopic f h)

end

/-- Radial contraction of the square, used to construct covering lifts directly. -/
def radialSquare : C(I × (Fin 2 → I), Fin 2 → I) where
  toFun ta i := ta.1 * ta.2 i
  continuous_toFun := continuous_pi (fun i =>
    (continuous_fst.subtype_val.mul
      (((continuous_apply i).comp continuous_snd).subtype_val)).subtype_mk _)

/-- A based square lifts through a covering map, including its constant boundary. -/
theorem exists_mapSquare_lift {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (hp : IsCoveringMap p) (e : E) (q : GenLoop _ X _) :
    ∃ a : GenLoop _ E e, mapSquare p a = q := by
  let z : Fin 2 → I := fun _ => 0
  have hz : z ∈ Cube.boundary _ := ⟨0, Or.inl rfl⟩
  let H := q.1.comp radialSquare
  have H0 : ∀ t, H (0, t) = p e := by
    intro t
    change q (fun i => 0 * t i) = p e
    aesop
  let F := hp.liftHomotopy H (ContinuousMap.const _ e) H0
  let G := F.comp ⟨fun t => (1, t), continuous_const.prodMk continuous_id⟩
  have hG : ∀ t, p (G t) = q t := by
    intro t
    have he := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (1, t)
    change p _ = q (fun i => 1 * t i) at he
    aesop

  have hbase : G z = e := by
    have he := hp.const_of_comp (g := fun t : I => F (t, z))
      (F.continuous.comp (continuous_id.prodMk continuous_const))
      (fun t s => by
        have ht := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (t, z)
        have hs := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (s, z)
        change p (F (t, z)) = q (fun i => t * z i) at ht
        change p (F (s, z)) = q (fun i => s * z i) at hs
        aesop) 1 0
    exact he.trans (hp.liftHomotopy_zero H (ContinuousMap.const _ e) H0 z)
  have hboundary : ∀ t ∈ Cube.boundary _, G t = e := by
    intro t ht
    have he := hp.constOn_of_comp square_boundary_isPreconnected G.continuous.continuousOn
      (fun a ha b hb => (hG a).trans
        ((GenLoop.boundary q a ha).trans ((GenLoop.boundary q b hb).symm.trans (hG b).symm)))
      ht hz
    exact he.trans hbase
  refine ⟨⟨G, hboundary⟩, ?_⟩
  apply GenLoop.ext
  exact hG

/-- The square-map formulation in the challenge is exactly the zero-map condition on
Mathlib's topological homotopy group, not an auxiliary algebraic substitute. -/
theorem killsPi2_iff {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : KillsPi2 f ↔ ∀ x z, pi2Map f x z = 1 := by
  constructor
  · intro h x z
    induction z using Quotient.inductionOn with
    | _ p => exact Quotient.sound (h x p)
  · intro h x p
    exact Quotient.exact (h x (Quotient.mk _ p))

/-- Postcomposing with a covering reflects the zero-map condition on `π₂`. -/
theorem killsPi2_covering_postcomp_iff {Y E X : Type}
    [TopologicalSpace Y] [TopologicalSpace E] [TopologicalSpace X]
    (f : C(Y, E)) (p : C(E, X)) (hp : IsCoveringMap p) :
    KillsPi2 (p.comp f) ↔ KillsPi2 f := by
  constructor
  · intro h y a
    apply (mapSquare_homotopic_iff_of_covering p hp _ GenLoop.const).mp <;> aesop
  · intro h y a
    have he := mapSquare_homotopic p (h y a)
    assumption

/-- Surjective coverings also reflect the zero-map condition when precomposed. -/
theorem killsPi2_covering_precomp_iff {E X Y : Type}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    (p : C(E, X)) (hp : IsCoveringMap p) (hs : Function.Surjective p)
    (f : C(X, Y)) : KillsPi2 (f.comp p) ↔ KillsPi2 f := by
  constructor
  · intro h x q
    obtain ⟨e, rfl⟩ := hs x
    obtain ⟨a, ha⟩ := exists_mapSquare_lift p hp e q <;> aesop
  · intro h e a
    exact h _ (mapSquare p a)

end Whitehead
