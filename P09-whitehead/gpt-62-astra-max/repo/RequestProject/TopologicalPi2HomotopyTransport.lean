module


public import RequestProject.SquareMovingBasepoint

@[expose] public section

/-! Invariance of the challenge's actual based-square zero condition under ordinary
homotopies and homotopy equivalences. Base points need not be fixed by the homotopies. -/

noncomputable section

namespace Whitehead
open scoped unitInterval Topology

variable {X Y Z : Type}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable (f : C(X, Y)) (g : C(Y, Z))

theorem killsPi2_precompose (hg : KillsPi2 g) :
    KillsPi2 (g.comp f) := by
  intro x p
  exact hg _ (mapSquare f p)

theorem killsPi2_postcompose (hf : KillsPi2 f) :
    KillsPi2 (g.comp f) := by
  intro x p
  have h := mapSquare_homotopic g (hf x p)
  assumption

section

variable {f g : C(X, Y)} (hfg : f.Homotopic g)
include hfg

/-- An ordinary homotopy preserves the vanishing of the induced second homotopy map. -/
theorem killsPi2_of_homotopic
    (hg : KillsPi2 g) : KillsPi2 f := by
  obtain ⟨H⟩ := hfg
  intro x p
  obtain ⟨G⟩ := hg x p
  have hz₀ : (fun _ : Fin 2 => 0) ∈ Cube.boundary _ := ⟨0, Or.inl rfl⟩
  let F : ContinuousMap.HomotopyWith _ (mapSquare g p).val
      SquareConstantBoundary := {
    toHomotopy := H.compContinuousMap p.val
    prop' := by
      intro t z hz
      simp_all [GenLoop.boundary] }
  let G' : ContinuousMap.HomotopyWith _
      (ContinuousMap.const _ _) SquareConstantBoundary := {
    toHomotopy := G.toHomotopy
    prop' := by
      intro t z hz
      change G _ = G _
      rw [G.eq_fst t hz, G.eq_fst t hz₀]
      exact (GenLoop.boundary (mapSquare g p) z hz).trans
        (GenLoop.boundary (mapSquare g p) _ hz₀).symm }
  exact genLoop_null_of_movingBoundary _ (F.trans G')

theorem killsPi2_homotopic_iff :
    KillsPi2 f ↔ KillsPi2 g :=
  ⟨killsPi2_of_homotopic hfg.symm, killsPi2_of_homotopic hfg⟩

end

/-- A homotopy equivalence in the target reflects the based-square zero condition. -/
theorem killsPi2_homotopyEquiv_postcomp_iff (e : ContinuousMap.HomotopyEquiv Y Z)
    (f : C(X, Y)) : KillsPi2 (e.toFun.comp f) ↔ KillsPi2 f := by
  constructor
  · intro h
    have hk := killsPi2_postcompose _ e.invFun h
    change KillsPi2 ((e.invFun.comp e.toFun).comp f) at hk
    have hh : ((e.invFun.comp e.toFun).comp f).Homotopic f := by
      simpa using e.left_inv.comp (ContinuousMap.Homotopic.refl f)
    grind [killsPi2_homotopic_iff]
  · exact killsPi2_postcompose f e.toFun

/-- A homotopy equivalence in the source reflects the based-square zero condition. -/
theorem killsPi2_homotopyEquiv_precomp_iff (e : ContinuousMap.HomotopyEquiv X Y)
    (f : C(Y, Z)) : KillsPi2 (f.comp e.toFun) ↔ KillsPi2 f := by
  constructor
  · intro h
    have hk := killsPi2_precompose e.invFun _ h
    change KillsPi2 (f.comp (e.toFun.comp e.invFun)) at hk
    have hh : (f.comp (e.toFun.comp e.invFun)).Homotopic f := by
      simpa using (ContinuousMap.Homotopic.refl f).comp e.right_inv
    grind [killsPi2_homotopic_iff]
  · exact killsPi2_precompose e.toFun f

/-- The zero condition is transported across a homotopy-commutative square whose
vertical maps are genuine homotopy equivalences. -/
theorem killsPi2_homotopyEquiv_square_iff {X' Y' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y']
    (e : ContinuousMap.HomotopyEquiv X X') (d : ContinuousMap.HomotopyEquiv Y Y')
    (f : C(X, Y)) (g : C(X', Y'))
    (h : (g.comp e.toFun).Homotopic (d.toFun.comp f)) :
    KillsPi2 g ↔ KillsPi2 f := by
  grind [killsPi2_homotopyEquiv_precomp_iff, killsPi2_homotopic_iff, killsPi2_homotopyEquiv_postcomp_iff]

end Whitehead
