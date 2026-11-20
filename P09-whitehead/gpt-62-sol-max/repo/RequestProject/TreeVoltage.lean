module

public import RequestProject.TreePresentation
public import RequestProject.PathVoltage

@[expose] public section

/-! A presentation cover with sheets indexed by any receiving group.
The same graph and lifted attaching paths are used for quotient groups and other receivers. -/

noncomputable section

namespace FiniteChains.Comb.TreeVoltage
open SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : FreeGroup (NonTree T) →* G)

abbrev germ (e : K.E × Bool) := φ (germWord T e)
abbrev word (p : List (K.E × Bool)) := φ (pathWord T p)

def src (x : G × K.E) := (x.1, K.src x.2)
def tgt (x : G × K.E) := (x.1 * germ T φ (x.2, true), K.tgt x.2)

abbrev liftGerm := PathVoltage.liftGerm (germ T φ)
abbrev liftPath := PathVoltage.liftPath (germ T φ)




theorem liftPath_projection (p : List (K.E × Bool)) (g : G) :
    (liftPath T φ p g).map (fun e => (e.1.2, e.2)) = p :=
  PathVoltage.liftPath_projection _ _ _

theorem liftPath_isPath {p : List (K.E × Bool)} {a b : K.V}
    (hp : IsPath K.src K.tgt p a b) (g : G) :
    IsPath (src (K := K)) (tgt T φ) (liftPath T φ p g) (g, a) (g * word T φ p, b) := by
  have hi (e : K.E) : germ T φ (e, false) = (germ T φ (e, true))⁻¹ := by
    have h := germWord_revGerm T (e, true)
    change germWord T (e, false) = _ at h
    exact (congrArg φ h).trans (map_inv φ _)
  have hw : word T φ p = (p.map (germ T φ)).prod := by
    change φ ((p.map (germWord T)).prod) = _
    rw [map_list_prod, List.map_map]
    rfl
  rw [hw]
  exact PathVoltage.liftPath_isPath (germ T φ) K.src K.tgt id hi hp g

noncomputable def cover (hφ : ∀ f, word T φ (K.att f) = 1) : Complex2.{u} where
  V := G × K.V
  E := G × K.E
  F := G × K.F
  src := src
  tgt := tgt T φ
  base f := (f.1, K.base f.2)
  att f := liftPath T φ (K.att f.2) f.1
  att_isLoop f := by simpa [hφ] using liftPath_isPath T φ (K.att_isLoop f.2) f.1

noncomputable def projection (hφ : ∀ f, word T φ (K.att f) = 1) : Hom (cover T φ hφ) K where
  onV := Prod.snd
  onE := Prod.snd
  onF := Prod.snd
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := (liftPath_projection T φ (K.att f.2) f.1).symm

/-- Any map of sheets commuting with edge translations commutes with path lifting. -/
theorem liftPath_map {H : Type u} [Group H] (ψ : FreeGroup (NonTree T) →* H)
    (s : G → H) (h : ∀ g e, s (g * germ T φ e) = s g * germ T ψ e)
    (p : List (K.E × Bool)) (g : G) :
    (liftPath T φ p g).map (fun e => ((s e.1.1, e.1.2), e.2)) = liftPath T ψ p (s g) := by
  simpa using PathVoltage.liftPath_map (germ T φ) (germ T ψ) id s h p g

end FiniteChains.Comb.TreeVoltage
