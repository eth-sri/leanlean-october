module

public import RequestProject.PresWordEmbedding
public import RequestProject.PresPosetReading
public import RequestProject.OrderUniversalCocycleReading


@[expose] public section

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
universe u t s
variable {α β J K : Type u} {G : Type t} {H : Type s} [Group G] [Group H]
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v) (a : α → G) (b : β → H) (φ : G →* H)
  (hb : ∀ i, b (h.gen i) = φ (a i))

include hb in
theorem wordVal_map (l : List _) :
    wordVal b (l.map (fun p => (h.gen p.1, p.2))) = φ (wordVal a l) := by
  have he : (FreeGroup.lift b).comp (FreeGroup.map h.gen) = φ.comp (FreeGroup.lift a) := by
    apply FreeGroup.ext_hom
    simp_all
  exact DFunLike.congr_fun he (FreeGroup.mk l)

include hb in
theorem prefixVal_map (j : J) (k : ℕ) :
    prefixVal v b (h.cell j) k = φ (prefixVal w a j k) := by
  unfold prefixVal
  rw [h.word, ← List.map_take]
  apply h.wordVal_map <;> assumption

include hb in
theorem roseVal_map (p q : Rose α) :
    roseVal b (h.roseMap p) (h.roseMap q) = φ (roseVal a p q) := by
  cases p <;> cases q <;> simp [roseMap, Function.Embedding.coeFn_mk, roseVal, hb, apply_ite]
  simp_all

include hb in
theorem trivVal_map (j : J) (k : ℕ) (c : CPos) :
    trivVal v b (h.cell j) k c = φ (trivVal w a j k c) := by
  have ha : aFun v (h.cell j, k, CPos.cedgL) = h.roseMap _ :=
    h.attaching_map (j, k, CPos.cedgL)
  have hr : roseVal b Rose.base (aFun v (h.cell j, k, CPos.cedgL)) =
      φ (roseVal a Rose.base (aFun w (j, k, CPos.cedgL))) := by
    rw [ha]
    exact h.roseVal_map a b φ hb Rose.base _
  cases c <;> simp only [trivVal, h.prefixVal_map a b φ hb, hr, map_mul, map_inv]

def cylinderFun : CylBase w → CylBase v
  | .inl p => .inl (h.roseMap p)
  | .inr p => .inr (h.circleFun p)

variable (p : CylBase w)

theorem posMap_inl : h.posMap (.inl p) = .inl (h.cylinderFun p) := by
  cases p <;> rfl

theorem cylinderFun_retraction :
    cylRetr _ (h.cylinderFun p) = h.roseMap (cylRetr (aHom w) p) := by
  cases p with
  | inl p => rfl
  | inr p => exact h.attaching_map p

variable (hw : ∀ j, wordVal a (w j) = 1) (hv : ∀ j, wordVal b (v j) = 1)

include hb in
/-- The complete presentation cocycle is natural under literal word embeddings. -/
theorem presCoc_map (p q : PresPos w) :
    (presCoc v b hv).val (h.posMap p) (h.posMap q) = φ ((presCoc w a hw).val p q) := by
  cases p with
  | inr j =>
    cases q with
    | inr k => exact (map_one φ).symm
    | inl q =>
      rw [h.posMap_inl]
      exact (map_one φ).symm
  | inl p =>
    cases q with
    | inl q =>
      rw [h.posMap_inl, h.posMap_inl]
      change roseVal b _
        _ =
          φ _
      rw [h.cylinderFun_retraction, h.cylinderFun_retraction]
      apply h.roseVal_map <;> assumption
    | inr j =>
      cases p with
      | inl r => exact (map_one φ).symm
      | inr c => apply h.trivVal_map <;> assumption

include hb in
theorem readGerm_map (e : (orderCx (PresPos w)).E × Bool) :
    (presCoc v b hv).readGerm ((orderCxMap h.posMap h.posMap.monotone).onE e.1, e.2) =
      φ ((presCoc w a hw).readGerm e) := by
  rcases e with ⟨e, s⟩
  cases s <;> simp only [OrdCocycle.readGerm, Bool.false_eq_true, if_false, if_true]
  · rw [map_inv]
    exact congrArg Inv.inv (h.presCoc_map a b φ hb hw hv _ _)
  · apply h.presCoc_map <;> assumption

include hb in
theorem readPath_map (p : List _) :
    (presCoc v b hv).readPath (mapPath (orderCxMap h.posMap h.posMap.monotone) p) =
      φ ((presCoc w a hw).readPath p) := by
  induction p with
  | nil => simp
  | cons e p ih =>
    change (presCoc v b hv).readPath
      (((orderCxMap h.posMap h.posMap.monotone).onE e.1, e.2) ::
        mapPath (orderCxMap h.posMap h.posMap.monotone) p) = _
    rw [OrdCocycle.readPath_cons, OrdCocycle.readPath_cons,
      h.readGerm_map a b φ hb hw hv, ih, map_mul]

include hb in
/-- Naturality holds on the actual path-class universal cover, not just on loops. -/
theorem readVertex_map (x : PresPos w) (p : UV (orderCx (PresPos w)) x) :
    (presCoc v b hv).readVertex (h.posMap x)
      (@univLiftV (orderCx (PresPos w)) (orderCx (PresPos v)) x
        (orderCxMap h.posMap h.posMap.monotone) p) =
        φ ((presCoc w a hw).readVertex x p) := by
  induction p using Quotient.inductionOn with
  | h p => apply h.readPath_map <;> assumption

end FiniteChains.PresModel.PresWordEmbedding
