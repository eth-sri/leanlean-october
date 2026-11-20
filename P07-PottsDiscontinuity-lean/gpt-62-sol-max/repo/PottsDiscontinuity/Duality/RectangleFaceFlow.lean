module

public import PottsDiscontinuity.Duality.RectangleFlowDimension
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

public section

namespace PottsDiscontinuity.FK

open Finset Medial SimpleGraph
open scoped Classical

noncomputable section

variable (a : LatticeVertex) (w h : ℕ)

local notation "G₀" => rectangleGraph a w h
local notation "V₀" => RectangleVertex a w h

/-- All genuine edges of the rectangle, presented as the all-open subgraph. -/
abbrev rectangleAllEdges : Configuration G₀ :=
  (univ : Finset (rectanglePrimalEdgeCarrier a w h))

@[simp] theorem mem_rectangleAllEdges (e : rectanglePrimalEdgeCarrier a w h) :
    e ∈ rectangleAllEdges a w h :=
  @mem_univ _ (rectanglePrimalEdgeCarrierFintype a w h) e

local notation "Ω" => rectangleAllEdges a w h
local notation "E₀" => OpenEdgeIndex G₀ Ω
local notation "F₀" => Subtype (fun z => z ∈ rectangleDualInterior a w h)

@[simp] theorem mem_rectangleDualInterior_iff {z : LatticeVertex} :
    z ∈ rectangleDualInterior a w h ↔
      a.1 ≤ z.1 ∧ z.1 < a.1 + (w : ℤ) ∧ a.2 ≤ z.2 ∧ z.2 < a.2 + (h : ℤ) := by
  simp only [rectangleDualInterior, mem_filter, rectangleDualExpanded, mem_latticeRectangle]
  constructor <;> intro hz <;> omega

private theorem card_faces : Fintype.card F₀ = w * h := by
  have he : rectangleDualInterior a w h = Ico a.1 (a.1 + (w : ℤ)) ×ˢ Ico a.2 (a.2 + (h : ℤ)) := by
    ext z
    simp [and_assoc]
  simp [he, Int.card_Ico]

/-- Extend an interior face potential by zero on the exterior. -/
@[expose] def facePotentialPad (φ : F₀ → ℝ) (z : LatticeVertex) : ℝ :=
  if hz : z ∈ rectangleDualInterior a w h then φ ⟨z, hz⟩ else 0

private theorem sum_face_ind (φ : F₀ → ℝ) (z : LatticeVertex) :
    (∑ f : F₀, if f.val = z then φ f else 0) = facePotentialPad a w h φ z := by
  unfold facePotentialPad
  split_ifs with hz
  · rw [sum_eq_single (⟨z, hz⟩ : F₀)]
    · simp
    · intro f _ hf
      simp [show f.val ≠ z from fun h => hf (Subtype.ext h)]
    · simp
  · refine sum_eq_zero fun f _ => ite_eq_right (fun (he : f.val = z) => hz ?_)
    rw [← he]
    exact f.property

private def bondOf (e : E₀) := rectanglePrimalEdgeBond a w h e.val

private def liftBond (b : LatticeBond)
    (hb : b.source ∈ latticeRectangle a w h ∧ b.target ∈ latticeRectangle a w h) : E₀ :=
  ⟨rectanglePrimalBondToEdge a w h ⟨b, hb⟩, mem_rectangleAllEdges a w h _⟩

@[simp] private theorem bondOf_liftBond (b : LatticeBond) (hb) :
    bondOf a w h (liftBond a w h b hb) = b :=
  congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).apply_symm_apply ⟨b, hb⟩)

private theorem liftBond_eq_iff (b : LatticeBond) (hb) (e : E₀) :
    e = liftBond a w h b hb ↔ bondOf a w h e = b := by
  have hi : Function.Injective (bondOf a w h) :=
    Subtype.val_injective.comp ((rectanglePrimalEdgeBondEquiv a w h).injective.comp
      Subtype.val_injective)
  simp [← hi.eq_iff]

private def faceSide (z : LatticeVertex) : Fin 4 → LatticeBond
  | 0 => ⟨z, .horizontal⟩
  | 1 => ⟨(z.1 + 1, z.2), .vertical⟩
  | 2 => ⟨(z.1, z.2 + 1), .horizontal⟩
  | 3 => ⟨z, .vertical⟩

private def sideEdge (f : F₀) (k : Fin 4) : E₀ := liftBond a w h (faceSide f.val k) (by
  have hf := (mem_rectangleDualInterior_iff a w h).1 f.property
  fin_cases k <;> simp [faceSide, mem_latticeRectangle, LatticeBond.source, LatticeBond.target] <;> omega)

private theorem sideEdge_eq_iff (e : E₀) (f : F₀) (k : Fin 4) :
    e = sideEdge a w h f k ↔ bondOf a w h e = faceSide f.val k :=
  liftBond_eq_iff a w h _ _ _

@[expose] def rectangleFullDivergence : (E₀ → ℝ) →ₗ[ℝ] (V₀ → ℝ) :=
  signedDivergence G₀ Ω (rectangleOpenEdgeOrientation a w h Ω)

private def delta (e : E₀) (e' : E₀) : ℝ := if e' = e then 1 else 0

private theorem div_delta (e : E₀) (v : V₀) :
    rectangleFullDivergence a w h (delta a w h e) v =
      (if (bondOf a w h e).source = v.val then 1 else 0) -
      (if (bondOf a w h e).target = v.val then 1 else 0) := by
  unfold rectangleFullDivergence
  rw [signedDivergence_apply]
  congr 1 <;> (
    rw [sum_eq_single e]
    · simp only [delta, ite_true, rectangleOpenEdgeOrientation, bondOf, Subtype.ext_iff]
      rfl
    · intro i _ hi; simp [delta, hi]
    · simp)

private def faceCycle (f : F₀) : E₀ → ℝ :=
  delta a w h (sideEdge a w h f 0) + delta a w h (sideEdge a w h f 1) -
    delta a w h (sideEdge a w h f 2) - delta a w h (sideEdge a w h f 3)

private theorem div_cycle (f : F₀) : rectangleFullDivergence a w h (faceCycle a w h f) = 0 := by
  unfold faceCycle
  rw [map_sub, map_sub, map_add]
  funext v
  simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, div_delta, sideEdge, bondOf_liftBond,
    faceSide, LatticeBond.source, LatticeBond.target]
  ring

private theorem faceCycle_eval (f : F₀) (e : E₀) :
    faceCycle a w h f e =
      let b := bondOf a w h e
      let u := fun side => if (b.faceBase side) = f.val then (1 : ℝ) else 0
      if b.axis = .horizontal then u true - u false else u false - u true := by
  simp only [faceCycle, Pi.sub_apply, Pi.add_apply, delta, sideEdge_eq_iff]
  generalize bondOf a w h e = b
  rcases b with ⟨⟨x,y⟩, _|_⟩ <;> rcases f with ⟨⟨p,q⟩, hf⟩
  · have hy : y - 1 = q ↔ y = q + 1 := by omega
    simp [faceSide, LatticeBond.faceBase, hy]
  · have hx : x - 1 = p ↔ x = p + 1 := by omega
    simp [faceSide, LatticeBond.faceBase, hx]

/-- Curl is the superposition of the oriented boundaries of the unit faces. -/
def rectangleFaceCurl : (F₀ → ℝ) →ₗ[ℝ] E₀ → ℝ where
  toFun φ := ∑ f, φ f • faceCycle a w h f
  map_add' φ ψ := by simp [add_smul, sum_add_distrib]
  map_smul' r φ := by simp [Finset.smul_sum, smul_smul]

theorem rectangleFullDivergence_faceCurl (φ : F₀ → ℝ) :
    rectangleFullDivergence a w h (rectangleFaceCurl a w h φ) = 0 := by
  change rectangleFullDivergence a w h (∑ f, φ f • faceCycle a w h f) = 0
  simp [div_cycle]

theorem rectangleFaceCurl_eval (φ : F₀ → ℝ) (e : E₀) :
    rectangleFaceCurl a w h φ e =
      let b := rectanglePrimalEdgeBond a w h e.val
      let u := fun side => facePotentialPad a w h φ (b.faceBase side)
      if b.axis = .horizontal then u true - u false else u false - u true := by
  change (∑ f, φ f • faceCycle a w h f) e = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, faceCycle_eval]
  change _ = (if (bondOf a w h e).axis = .horizontal then _ else _)
  split_ifs <;> simp only [mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_face_ind, eq_comm] <;> rfl

theorem curl_injective : Function.Injective (rectangleFaceCurl a w h) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro φ hφ
  rw [LinearMap.mem_ker] at hφ
  rw [Submodule.mem_bot]
  funext z
  have hz := (mem_rectangleDualInterior_iff a w h).mp z.property
  let i := z.val.1
  let j (n : ℕ) := a.2 + (n : ℤ) - 1
  have hzero (n : ℕ) (hn : n ≤ h) : facePotentialPad a w h φ (i, j n) = 0 := by
    induction n with
    | zero => simp [facePotentialPad, j]
    | succ n ih =>
      let b : LatticeBond := ⟨(i, a.2 + (n : ℤ)), .horizontal⟩
      have hb : b.source ∈ latticeRectangle a w h ∧ b.target ∈ latticeRectangle a w h := by
        simp [b, i, LatticeBond.source, LatticeBond.target, mem_latticeRectangle]; omega
      have he := congrFun hφ (liftBond a w h b hb)
      rw [rectangleFaceCurl_eval] at he
      rw [show rectanglePrimalEdgeBond a w h (liftBond a w h b hb).val = b from
        bondOf_liftBond a w h b hb] at he
      have he' : facePotentialPad a w h φ (i, a.2 + (n : ℤ)) - facePotentialPad a w h φ (i, j n) = 0 := by
        assumption
      rw [ih (by omega), sub_zero] at he'
      rwa [show j (n+1) = a.2 + (n : ℤ) by simp [j] <;> omega]
  let n := (z.val.2 - a.2 + 1).toNat
  have he := hzero n (by omega)
  have hz' : (i, j n) = z.val := Prod.ext rfl (by dsimp [j, n]; omega)
  rw [hz'] at he
  simpa [facePotentialPad] using he

private abbrev horizontalBases := Finset.Ico a.1 (a.1 + (w : ℤ)) ×ˢ
  Finset.Icc a.2 (a.2 + (h : ℤ))
private abbrev verticalBases := Finset.Icc a.1 (a.1 + (w : ℤ)) ×ˢ
  Finset.Ico a.2 (a.2 + (h : ℤ))

private def bondBases : RectanglePrimalBond a w h ≃
    (↥(horizontalBases a w h) ⊕ ↥(verticalBases a w h)) where
  toFun b := by
    rcases b with ⟨⟨⟨x,y⟩,ax⟩, hb⟩
    cases ax
    · refine .inl ⟨(x,y), ?_⟩
      simp [horizontalBases, mem_latticeRectangle, LatticeBond.source, LatticeBond.target] at *
      omega
    · refine .inr ⟨(x,y), ?_⟩
      simp [verticalBases, mem_latticeRectangle, LatticeBond.source, LatticeBond.target] at *
      omega
  invFun c := by
    rcases c with ⟨⟨x,y⟩,hc⟩ | ⟨⟨x,y⟩,hc⟩
    · refine ⟨⟨(x,y),.horizontal⟩, ?_⟩
      simp [horizontalBases, mem_latticeRectangle, LatticeBond.source, LatticeBond.target] at *
      omega
    · refine ⟨⟨(x,y),.vertical⟩, ?_⟩
      simp [verticalBases, mem_latticeRectangle, LatticeBond.source, LatticeBond.target] at *
      omega
  left_inv := by rintro ⟨⟨⟨x,y⟩,_|_⟩,h⟩ <;> rfl
  right_inv := by rintro (⟨⟨x,y⟩,h⟩|⟨⟨x,y⟩,h⟩) <;> rfl

private theorem card_allEdges : Fintype.card (rectanglePrimalEdgeCarrier a w h) =
    w * (h+1) + (w+1) * h := by
  rw [Fintype.card_congr ((rectanglePrimalEdgeBondEquiv a w h).trans (bondBases a w h)),
    Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  have hi (x : ℤ) (n : ℕ) : (x + (n:ℤ) + 1 - x).toNat = n + 1 := by omega
  simp [hi]

private def coordEquiv (x : ℤ) (n : ℕ) : Fin (n+1) ≃ ↥(Finset.Icc x (x + (n : ℤ))) where
  toFun k := ⟨x + (k.val:ℤ), by simp; omega⟩
  invFun k := ⟨(k.val - x).toNat, by have := Finset.mem_Icc.mp k.2; omega⟩
  left_inv k := by apply Fin.ext; simp
  right_inv k := by
    apply Subtype.ext
    have := Finset.mem_Icc.mp k.2
    dsimp
    omega

private theorem rectangle_preconnected : (rectangleGraph a w h).Preconnected := by
  let e := ((coordEquiv a.1 w).prodCongr (coordEquiv a.2 h)).trans
    (Equiv.subtypeProdEquivProd.symm.trans (Equiv.subtypeEquivRight (fun _ => Finset.mem_product.symm)))
  let f : ((pathGraph (w+1)).boxProd (pathGraph (h+1))) →g rectangleGraph a w h :=
    ⟨e, by
      intro i j hij
      change squareLattice.Adj (a.1+(i.1.val:ℤ),a.2+(i.2.val:ℤ))
        (a.1+(j.1.val:ℤ),a.2+(j.2.val:ℤ))
      rw [boxProd_adj] at hij
      rw [squareLattice_adj_iff]
      rcases hij with ⟨hp,he⟩ | ⟨hp,he⟩ <;>
        have := congrArg Fin.val he <;> have := pathGraph_adj.mp hp <;> dsimp <;> omega⟩
  intro u v
  have hr := ((pathGraph_preconnected (w+1)).boxProd (pathGraph_preconnected (h+1))) (e.symm u) (e.symm v)
  have hf := hr.map f
  change (rectangleGraph a w h).Reachable (e (e.symm u)) (e (e.symm v)) at hf
  rwa [Equiv.apply_symm_apply e u, Equiv.apply_symm_apply e v] at hf

private theorem componentCount_allEdges : componentCount (rectangleGraph a w h)
    (BoundaryCondition.free ∅) Ω = 1 := by
  have hG : openGraph (rectangleGraph a w h) Ω = rectangleGraph a w h := by
    ext u v
    refine ⟨fun huv => openGraph_le _ _ huv, fun huv => (openGraph_adj _ _ _ _).mpr ?_⟩
    exact ⟨⟨s(u,v), huv⟩, @Finset.mem_univ _ (rectanglePrimalEdgeCarrierFintype a w h) _, rfl⟩
  rw [componentCount, componentSetoid_free, hG]
  let : Subsingleton (Quotient (rectangleGraph a w h).reachableSetoid) :=
    ⟨Quotient.ind₂ fun _ _ => Quotient.sound (rectangle_preconnected a w h _ _)⟩
  let : Nonempty (Quotient (rectangleGraph a w h).reachableSetoid) :=
    ⟨Quotient.mk _ ⟨a, by simp [mem_latticeRectangle]⟩⟩
  exact Nat.card_unique

private theorem finrank_fullDivergence_ker :
    Module.finrank ℝ (LinearMap.ker (rectangleFullDivergence a w h)) = w * h := by
  have hdim := rectangleSignedFlowDimension a w h Ω
  rw [componentCount_allEdges, card_rectangleVertex] at hdim
  change Module.finrank ℝ (LinearMap.ker (rectangleFullDivergence a w h)) + (w+1)*(h+1) =
    (Finset.univ : Finset (rectanglePrimalEdgeCarrier a w h)).card + 1 at hdim
  rw [card_univ, card_allEdges] at hdim
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at hdim
  omega

theorem rectangleFaceCurl_range :
    LinearMap.range (rectangleFaceCurl a w h) = LinearMap.ker (rectangleFullDivergence a w h) := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro _ ⟨φ, rfl⟩
    exact rectangleFullDivergence_faceCurl a w h φ
  · rw [finrank_fullDivergence_ker,
      LinearMap.finrank_range_of_inj (curl_injective a w h), Module.finrank_fintype_fun_eq_card, card_faces]

end
end PottsDiscontinuity.FK
