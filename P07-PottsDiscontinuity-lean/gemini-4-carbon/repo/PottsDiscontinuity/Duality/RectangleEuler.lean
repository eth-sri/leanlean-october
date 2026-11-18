module

public import PottsDiscontinuity.Duality.RectangleDualConfiguration
public import PottsDiscontinuity.Duality.FiniteGraphBoundaryParity
public import PottsDiscontinuity.FK.ComponentMerge
public import PottsDiscontinuity.TorusTopology.SquareLatticeTurning

@[expose] public section

namespace PottsDiscontinuity.FK

open SimpleGraph PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial PottsDiscontinuity.TorusTopology

noncomputable section

def rectangleCarrierOfConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    Finset (rectanglePrimalEdgeCarrier a w h) := A

private lemma dualGraphEdgeEquiv_val (a : LatticeVertex) (w h : ℕ)
    (de : RectangleDualEdgeCarrier a w h) :
    (rectangleDualGraphEdgeEquiv a w h de).1 = rectangleDualCarrierPair a w h de := rfl

private lemma free_empty_componentCount (a : LatticeVertex) (w h : ℕ) :
    componentCount (rectangleGraph a w h)
      (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) ∅ = (w + 1) * (h + 1) := by
  have hbot : componentSetoid (rectangleGraph a w h) (BoundaryCondition.free ∅) ∅ = Setoid.ker id := by
    apply le_antisymm
    · apply componentSetoid_le
      · apply reachableSetoid_le_of_adj; intro x y hxy
        obtain ⟨_, he, _⟩ := (openGraph_adj _ _ x y).mp hxy; exact absurd he (Finset.notMem_empty _)
      · intro _ _ h; exact h
    · intro x y h; change x = y at h; subst h; exact (componentSetoid _ _ _).refl x
  change Nat.card (Quotient _) = _
  rw [Nat.card_congr ((Quotient.congrRight (Setoid.ext_iff.mp hbot)).trans
    (Setoid.quotientKerEquivOfSurjective id Function.surjective_id)), Nat.card_eq_fintype_card, card_rectangleVertex]

private lemma dual_empty_componentCount (a : LatticeVertex) (w h : ℕ) :
    componentCount (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h) (rectangleDualConfiguration a w h ∅) = 1 := by
  let G_D := rectangleDualGraph a w h; let ξ_D := rectangleDualBoundaryCondition a w h
  let S_D := componentSetoid G_D ξ_D (rectangleDualConfiguration a w h ∅)
  have hb₀_exp : (a.1 - 1, a.2 - 1) ∈ rectangleDualExpanded a w h := by rw [rectangleDualExpanded, mem_latticeRectangle]; omega
  let b₀ : RectangleDualVertex a w h := ⟨(a.1 - 1, a.2 - 1), hb₀_exp⟩
  have hb₀_bd : b₀.1 ∈ rectangleDualBoundary a w h := by simp [b₀, rectangleDualBoundary, rectangleDualInterior, hb₀_exp]
  have hstep : ∀ n : ℕ, ∀ z : RectangleDualVertex a w h, (z.1.1 - (a.1 - 1)).toNat = n → S_D.r z b₀ := fun n => by
    induction n with
    | zero =>
      intro z hn; have := (mem_latticeRectangle _ _ _ _).mp z.2
      exact boundary_component G_D ξ_D _ (.inr ⟨Finset.mem_filter.mpr ⟨z.2, fun hi => by
        rw [rectangleDualInterior, Finset.mem_filter] at hi; omega⟩, hb₀_bd⟩)
    | succ n ih =>
      intro z hn
      by_cases hbd : z.1 ∈ rectangleDualBoundary a w h
      · exact boundary_component G_D ξ_D _ (.inr ⟨hbd, hb₀_bd⟩)
      · have hc : (z.1 ∈ rectangleDualInterior a w h) := by by_contra hni; exact hbd (Finset.mem_filter.mpr ⟨z.2, hni⟩)
        have hc' := (Finset.mem_filter.mp hc).2
        let b : RectanglePrimalBond a w h := ⟨⟨z.1, .vertical⟩, by
          constructor <;> rw [mem_latticeRectangle] <;> dsimp [LatticeBond.source, LatticeBond.target] <;> omega⟩
        let de := rectanglePrimalDualEdgeEquiv a w h (rectanglePrimalBondToEdge a w h b)
        have hpe_b : rectanglePrimalEdgeBond a w h de.primalEdge = b.1 :=
          congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).right_inv b)
        have hcb : de.crossingBond = ⟨(z.1.1 - 1, z.1.2), .horizontal⟩ := by
          rw [de.crossingBond_eq, rectangleCrossingDualBond, hpe_b]; rfl
        let z' := rectangleDualEdgeSource a w h de
        have htgt : rectangleDualEdgeTarget a w h de = z := Subtype.ext <| by
          change de.crossingBond.target = z.1; rw [hcb]; dsimp [LatticeBond.target]; ext <;> omega
        have hadj : (openGraph G_D (rectangleDualConfiguration a w h ∅)).Adj z z' :=
          (openGraph_adj _ _ z z').mpr ⟨rectangleDualGraphEdgeEquiv a w h de,
            (mem_rectangleDualConfiguration a w h ∅ de).mpr (Finset.notMem_empty _),
            by rw [dualGraphEdgeEquiv_val, rectangleDualCarrierPair, htgt, Sym2.eq_swap]⟩
        exact S_D.trans (actualConnected_component G_D ξ_D _ (actualConnected_of_adj G_D _ hadj))
          (ih z' (by change (de.crossingBond.source.1 - _).toNat = _; rw [hcb]; dsimp only [LatticeBond.source]; omega))
  have : Subsingleton (Quotient S_D) := ⟨Quotient.ind₂ fun x y => Quotient.sound (S_D.trans (hstep _ x rfl) (S_D.symm (hstep _ y rfl)))⟩
  have : Nonempty (Quotient S_D) := ⟨Quotient.mk S_D b₀⟩
  exact Nat.card_unique

private abbrev toCfg (a : LatticeVertex) (w h : ℕ) (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Configuration (rectangleGraph a w h) := A

private lemma rect_exclusion (a : LatticeVertex) (w h : ℕ)
    (A₀ : Finset (rectanglePrimalEdgeCarrier a w h))
    {u v : RectangleVertex a w h} (huv : (rectangleGraph a w h).Adj u v)
    (heA₀ : (⟨s(u, v), (rectangleGraph a w h).mem_edgeSet.mpr huv⟩ : rectanglePrimalEdgeCarrier a w h) ∉ A₀)
    (hrel : (componentSetoid (rectangleGraph a w h) (BoundaryCondition.free ∅) (toCfg a w h A₀)).r u v) :
    let e : rectanglePrimalEdgeCarrier a w h := ⟨s(u, v), (rectangleGraph a w h).mem_edgeSet.mpr huv⟩
    let de := rectanglePrimalDualEdgeEquiv a w h e
    ¬ (componentSetoid (rectangleDualGraph a w h) (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h (insert e A₀))).r
      (rectangleDualEdgeSource a w h de) (rectangleDualEdgeTarget a w h de) := by
  intro e de hdual
  have hle : componentSetoid (rectangleGraph a w h) (BoundaryCondition.free ∅) (toCfg a w h A₀) ≤
      (openGraph (rectangleGraph a w h) (toCfg a w h A₀)).reachableSetoid := by
    apply componentSetoid_le
    · intro _ _ h; exact h
    · intro x y h; change x = y at h; subst h; exact .refl x
  obtain ⟨w_open⟩ := hle hrel
  let hom : openGraph (rectangleGraph a w h) (toCfg a w h A₀) →g FK.squareLattice :=
    ⟨Subtype.val, fun hadj => (rectangleGraph_adj_iff a w h _ _).mp (openGraph_le _ _ hadj)⟩
  let w₁ := w_open.map hom
  have hw₁_edges : ∀ {x y} (wo : (openGraph (rectangleGraph a w h) (toCfg a w h A₀)).Walk x y),
      ∀ f ∈ (wo.map hom).edges, ∃ e' ∈ A₀, f = Sym2.map Subtype.val e'.1 := by
    intro x y wo; induction wo with
    | nil => simp
    | @cons x z _ hadj _ ih =>
      intro f hf; rcases List.mem_cons.mp hf with rfl | hf
      · obtain ⟨e', he'A, he'eq⟩ := (openGraph_adj _ _ x z).mp hadj
        exact ⟨e', he'A, (congrArg (Sym2.map Subtype.val) he'eq).symm⟩
      · exact ih f hf
  let p_cl : FK.squareLattice.Walk v.1 v.1 := .cons ((rectangleGraph_adj_iff a w h u v).mp huv).symm w₁
  have hp_supp (z) (hz : z ∈ p_cl.support) : z ∈ latticeRectangle a w h := by
    rcases List.mem_cons.mp hz with rfl | hz
    · exact v.2
    · obtain ⟨z₀, _, rfl⟩ := List.mem_map.mp (Walk.support_map hom w_open ▸ hz); exact z₀.2
  have hw_out (f : Sym2 LatticeVertex) (ho : ∃ z ∈ f, z ∉ latticeRectangle a w h) : gridWalkInd p_cl f = 0 := by
    apply gridWalkInd_eq_zero_of_not_mem; intro hm
    obtain ⟨dt, hdt, hdt_eq⟩ := List.mem_map.mp hm; obtain ⟨z, hzf, hzn⟩ := ho
    rcases Sym2.mem_iff.mp (hdt_eq ▸ hzf) with rfl | rfl
    · exact hzn (hp_supp _ (Walk.dart_fst_mem_support_of_mem_darts p_cl hdt))
    · exact hzn (hp_supp _ (Walk.dart_snd_mem_support_of_mem_darts p_cl hdt))
  let φ (z : LatticeVertex) : ZMod 2 := gridRayPot a.1 p_cl z.1 z.2
  have hφ_y (x y : ℤ) (hx : a.1 ≤ x) : φ (x, y) + φ (x, y - 1) = gridWalkInd p_cl (gridHEdge x y) :=
    gridRayPot_step_y a.1 p_cl (fun y' => hw_out _ ⟨(a.1 - 1, y'), by simp [gridHEdge], by rw [mem_latticeRectangle]; omega⟩) hx y
  have hφ_bd (z : RectangleDualVertex a w h) (hbd : z.1 ∈ rectangleDualBoundary a w h) : φ z.1 = 0 := by
    have hexp := (mem_latticeRectangle _ _ _ _).mp z.2
    have hnint := (Finset.mem_filter.mp hbd).2; rw [rectangleDualInterior, Finset.mem_filter] at hnint
    have hcases : z.1.1 < a.1 ∨ a.1 + (w : ℤ) ≤ z.1.1 ∨ z.1.2 < a.2 ∨ a.2 + (h : ℤ) ≤ z.1.2 := by
      by_contra hall; exact hnint ⟨z.2, by omega⟩
    dsimp [φ, gridRayPot]
    rcases hcases with hx | hx | hy | hy
    · rw [Finset.Icc_eq_empty (by omega)]; simp
    · rw [show z.1.1 = a.1 + (w : ℤ) by dsimp [rectangleDualExpanded] at hexp; omega,
        gridRowVEdgeSum a.1 (a.1 + w) z.1.2 p_cl fun x hx' => ((mem_latticeRectangle _ _ _ _).mp (hp_supp x hx')).1, grid_zmod2_two]
    · exact Finset.sum_eq_zero fun x' _ => hw_out _ ⟨(x', z.1.2), by simp [gridVEdge], by rw [mem_latticeRectangle]; omega⟩
    · exact Finset.sum_eq_zero fun x' _ => hw_out _ ⟨(x', z.1.2 + 1), by simp [gridVEdge], by rw [mem_latticeRectangle]; omega⟩
  have hφ_dualEdge (df : RectangleDualEdgeCarrier a w h) :
      φ (rectangleDualEdgeSource a w h df).1 + φ (rectangleDualEdgeTarget a w h df).1 =
        gridWalkInd p_cl (Sym2.map Subtype.val df.primalEdge.1) := by
    rw [rectangleDualEdgeSource_val, rectangleDualEdgeTarget_val, df.crossingBond_eq, rectangleCrossingDualBond,
      ← rectanglePrimalEdgeBond_toSym2_public]
    have hb_mem := rectanglePrimalEdgeBond_endpoints_mem_public a w h df.primalEdge
    generalize rectanglePrimalEdgeBond a w h df.primalEdge = b at hb_mem ⊢
    rcases b with ⟨⟨bx, by_⟩, ax⟩
    have hx : a.1 ≤ bx := ((mem_latticeRectangle _ _ _ _).mp hb_mem.1).1.1
    cases ax <;> dsimp [dualBondOfPrimal, LatticeBond.source, LatticeBond.target, LatticeBond.toSym2]
    · rw [sub_add_cancel, add_comm, hφ_y bx by_ hx]; rfl
    · rw [sub_add_cancel, add_comm, gridRayPot_step_x a.1 p_cl hx by_]; rfl
  have hker : componentSetoid (rectangleDualGraph a w h) (rectangleDualBoundaryCondition a w h)
      (rectangleDualConfiguration a w h (insert e A₀)) ≤ Setoid.ker (fun z : RectangleDualVertex a w h => φ z.1) := by
    apply componentSetoid_le
    · apply reachableSetoid_le_of_adj; intro z₁ z₂ hadj
      obtain ⟨g, hg, hgeq⟩ := (openGraph_adj _ _ z₁ z₂).mp hadj
      obtain ⟨df, rfl⟩ := (rectangleDualGraphEdgeEquiv a w h).surjective g
      have hg' := (mem_rectangleDualConfiguration a w h (insert e A₀) df).mp hg
      rw [dualGraphEdgeEquiv_val, rectangleDualCarrierPair] at hgeq
      have hw0 : gridWalkInd p_cl (Sym2.map Subtype.val df.primalEdge.1) = 0 :=
        gridWalkInd_eq_zero_of_not_mem p_cl fun hmem_cl => by
          rcases List.mem_cons.mp hmem_cl with h1 | h2
          · change Sym2.map Subtype.val df.primalEdge.1 = s(v.1, u.1) at h1
            have hdf_e : df.primalEdge = e := Subtype.ext (Sym2.map.injective Subtype.val_injective (h1.trans Sym2.eq_swap))
            exact hg' (hdf_e ▸ Finset.mem_insert_self e A₀)
          · obtain ⟨e', he'A, he'eq⟩ := hw₁_edges w_open _ h2
            have hdf_e' : df.primalEdge = e' := Subtype.ext (Sym2.map.injective Subtype.val_injective he'eq)
            exact hg' (Finset.mem_insert_of_mem (hdf_e' ▸ he'A))
      have hsum := (hφ_dualEdge df).trans hw0
      change φ z₁.1 = φ z₂.1
      rcases Sym2.eq_iff.mp hgeq.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        (generalize φ (rectangleDualEdgeSource a w h df).1 = x at hsum ⊢
         generalize φ (rectangleDualEdgeTarget a w h df).1 = y at hsum ⊢; revert x y hsum; decide)
    · intro z₁ z₂ hbd; rcases hbd with rfl | ⟨h1, h2⟩; rfl; change φ z₁.1 = φ z₂.1; rw [hφ_bd z₁ h1, hφ_bd z₂ h2]
  have hφ_one : φ (rectangleDualEdgeSource a w h de).1 + φ (rectangleDualEdgeTarget a w h de).1 = 1 := by
    rw [hφ_dualEdge de]; change gridWalkInd p_cl (Sym2.map Subtype.val e.1) = 1
    have he_eq : Sym2.map Subtype.val e.1 = s(v.1, u.1) := Sym2.eq_swap
    rw [he_eq]; change (if s(v.1, u.1) = s(v.1, u.1) then 1 else 0) + gridWalkInd w₁ s(v.1, u.1) = 1
    rw [ite_eq_left rfl, gridWalkInd_eq_zero_of_not_mem w₁ fun hm => by
      obtain ⟨e', he'A, he'eq⟩ := hw₁_edges w_open _ hm
      have h_eq : e' = e := Subtype.ext (Sym2.map.injective Subtype.val_injective (he'eq.symm.trans he_eq.symm))
      rw [h_eq] at he'A; exact heA₀ he'A, add_zero]
  have hφ_eq : φ (rectangleDualEdgeSource a w h de).1 = φ (rectangleDualEdgeTarget a w h de).1 := hker hdual
  rw [hφ_eq, grid_zmod2_two] at hφ_one; exact absurd hφ_one (by decide)

private lemma rect_existence (a : LatticeVertex) (w h : ℕ)
    (A₀ : Finset (rectanglePrimalEdgeCarrier a w h))
    {u v : RectangleVertex a w h} (huv : (rectangleGraph a w h).Adj u v)
    (hnot : ¬ (componentSetoid (rectangleGraph a w h) (BoundaryCondition.free ∅) (toCfg a w h A₀)).r u v) :
    let e : rectanglePrimalEdgeCarrier a w h := ⟨s(u, v), (rectangleGraph a w h).mem_edgeSet.mpr huv⟩
    let de := rectanglePrimalDualEdgeEquiv a w h e
    (componentSetoid (rectangleDualGraph a w h) (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h (insert e A₀))).r
      (rectangleDualEdgeSource a w h de) (rectangleDualEdgeTarget a w h de) := by
  classical
  intro e de
  let G_P := rectangleGraph a w h
  let S_P := componentSetoid G_P (BoundaryCondition.free ∅) (toCfg a w h A₀)
  let G_D := rectangleDualGraph a w h; let ξ_D := rectangleDualBoundaryCondition a w h
  let S_D := componentSetoid G_D ξ_D (rectangleDualConfiguration a w h (insert e A₀))
  let u_star := rectangleDualEdgeSource a w h de; let v_star := rectangleDualEdgeTarget a w h de
  let e_star := rectangleDualGraphEdgeEquiv a w h de
  let X (x : RectangleVertex a w h) : Bool := decide (S_P.r u x)
  let isCutEdge (f : rectanglePrimalEdgeCarrier a w h) : Prop := ∃ x y, f.1 = s(x, y) ∧ X x ≠ X y
  have hisCut_iff (f : rectanglePrimalEdgeCarrier a w h) (x y) (hf : f.1 = s(x, y)) : isCutEdge f ↔ X x ≠ X y :=
    ⟨fun ⟨x', y', hf', hne'⟩ => by rcases Sym2.eq_iff.mp (hf.symm.trans hf') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hne'; exact hne'.symm,
      fun hne => ⟨x, y, hf, hne⟩⟩
  let cutDual : Configuration G_D := Finset.univ.filter fun g => isCutEdge ((rectangleDualGraphEdgeEquiv a w h).symm g).primalEdge
  let E'_D : Configuration G_D := cutDual.erase e_star
  have he_star_cut : e_star ∈ cutDual := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    rw [Equiv.symm_apply_apply]; exact ⟨u, v, rfl, by dsimp [X]; rw [decide_eq_true (S_P.refl u), decide_eq_false hnot]; decide⟩⟩
  have hE'_sub : E'_D ⊆ rectangleDualConfiguration a w h (insert e A₀) := fun g hg => by
    obtain ⟨hg_ne, hg_cut⟩ := Finset.mem_erase.mp hg
    obtain ⟨df, rfl⟩ := (rectangleDualGraphEdgeEquiv a w h).surjective g
    rw [mem_rectangleDualConfiguration, Finset.mem_insert, not_or]
    obtain ⟨x, y, hxy, hneX⟩ : isCutEdge df.primalEdge := by simpa using (Finset.mem_filter.mp hg_cut).2
    refine ⟨fun hpe => hg_ne (congrArg (rectangleDualGraphEdgeEquiv a w h) ((rectanglePrimalDualEdgeEquiv a w h).symm.injective hpe)), fun hpA => ?_⟩
    have hrel_xy : S_P.r x y := actualConnected_component G_P _ _ (actualConnected_of_adj G_P _ ((openGraph_adj G_P _ x y).mpr ⟨df.primalEdge, hpA, hxy⟩))
    exact hneX (by dsimp [X]; exact decide_eq_decide.mpr ⟨fun h => S_P.trans h hrel_xy, fun h => S_P.trans h (S_P.symm hrel_xy)⟩)
  let H_full := openGraph G_D cutDual; let H_D := openGraph G_D E'_D
  have hdeg_full_even (z : RectangleDualVertex a w h) (hz : z.1 ∈ rectangleDualInterior a w h) : Even (H_full.degree z) := by
    have hc := (Finset.mem_filter.mp hz).2
    let v00 : RectangleVertex a w h := ⟨(z.1.1, z.1.2), by rw [mem_latticeRectangle]; omega⟩
    let v10 : RectangleVertex a w h := ⟨(z.1.1 + 1, z.1.2), by rw [mem_latticeRectangle]; omega⟩
    let v11 : RectangleVertex a w h := ⟨(z.1.1 + 1, z.1.2 + 1), by rw [mem_latticeRectangle]; omega⟩
    let v01 : RectangleVertex a w h := ⟨(z.1.1, z.1.2 + 1), by rw [mem_latticeRectangle]; omega⟩
    let zDir : Fin 4 → RectangleDualVertex a w h
      | 0 => ⟨(z.1.1, z.1.2 - 1), by unfold rectangleDualExpanded; rw [mem_latticeRectangle]; omega⟩
      | 1 => ⟨(z.1.1 + 1, z.1.2), by unfold rectangleDualExpanded; rw [mem_latticeRectangle]; omega⟩
      | 2 => ⟨(z.1.1, z.1.2 + 1), by unfold rectangleDualExpanded; rw [mem_latticeRectangle]; omega⟩
      | 3 => ⟨(z.1.1 - 1, z.1.2), by unfold rectangleDualExpanded; rw [mem_latticeRectangle]; omega⟩
    let cutDir : Fin 4 → Bool
      | 0 => X v00 != X v10 | 1 => X v10 != X v11 | 2 => X v01 != X v11 | 3 => X v00 != X v01
    have hzDir_inj : Function.Injective zDir := fun i j hij => by
      have := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp only [zDir, Prod.ext_iff] at this; omega)
    have hmk (b : RectanglePrimalBond a w h) (x y : RectangleVertex a w h) (yD : RectangleDualVertex a w h)
        (hxy_b : Sym2.map Subtype.val (s(x, y) : Sym2 _) = b.1.toSym2) (hXne : X x ≠ X y)
        (hdual_z : s((dualBondOfPrimal b.1).source, (dualBondOfPrimal b.1).target) = s(z.1, yD.1)) : H_full.Adj z yD := by
      let pe := rectanglePrimalBondToEdge a w h b; let df := rectanglePrimalDualEdgeEquiv a w h pe
      have hpe_b : rectanglePrimalEdgeBond a w h df.primalEdge = b.1 :=
        congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).right_inv b)
      refine (openGraph_adj _ _ z yD).mpr ⟨rectangleDualGraphEdgeEquiv a w h df,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [Equiv.symm_apply_apply]
          exact ⟨x, y, Sym2.map.injective Subtype.val_injective ((rectanglePrimalEdgeBond_toSym2_public a w h pe).symm.trans
            ((congrArg LatticeBond.toSym2 hpe_b).trans hxy_b.symm)), hXne⟩⟩, ?_⟩
      rw [dualGraphEdgeEquiv_val]
      exact Sym2.map.injective Subtype.val_injective (by
        simpa [rectangleDualCarrierPair, rectangleDualEdgeSource_val, rectangleDualEdgeTarget_val,
          df.crossingBond_eq, rectangleCrossingDualBond, hpe_b] using hdual_z)
    have hrev (df : RectangleDualEdgeCarrier a w h) (hdf : isCutEdge df.primalEdge) (y : RectangleDualVertex a w h)
        (i : Fin 4) (x₁ x₂ : RectangleVertex a w h)
        (hpair : Sym2.map Subtype.val df.primalEdge.1 = Sym2.map Subtype.val (s(x₁, x₂) : Sym2 _))
        (hcut_eq : cutDir i = (X x₁ != X x₂)) (hy_eq : y.1 = (zDir i).1) :
        ∃ j, cutDir j = true ∧ zDir j = y :=
      ⟨i, hcut_eq ▸ bne_iff_ne.mpr ((hisCut_iff df.primalEdge x₁ x₂ (Sym2.map.injective Subtype.val_injective hpair)).mp hdf),
        Subtype.ext hy_eq.symm⟩
    have hnb_eq : H_full.neighborFinset z = (Finset.univ.filter fun i => cutDir i = true).image zDir := by
      ext y; simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun hadj => ?_, fun ⟨i, hi, hy⟩ => ?_⟩
      · obtain ⟨g, hg_cut, hgy⟩ := (openGraph_adj G_D cutDual z y).mp hadj
        obtain ⟨df, rfl⟩ := (rectangleDualGraphEdgeEquiv a w h).surjective g
        rw [dualGraphEdgeEquiv_val, rectangleDualCarrierPair] at hgy
        have hdf : isCutEdge df.primalEdge := by simpa using (Finset.mem_filter.mp hg_cut).2
        have hb_sym := rectanglePrimalEdgeBond_toSym2_public a w h df.primalEdge
        have hcb_sym : s(z.1, y.1) = s((dualBondOfPrimal (rectanglePrimalEdgeBond a w h df.primalEdge)).source,
            (dualBondOfPrimal (rectanglePrimalEdgeBond a w h df.primalEdge)).target) := by
          simpa [rectangleDualEdgeSource_val, rectangleDualEdgeTarget_val,
            df.crossingBond_eq, rectangleCrossingDualBond] using (congrArg (Sym2.map Subtype.val) hgy).symm
        rcases hb_eq : rectanglePrimalEdgeBond a w h df.primalEdge with ⟨⟨bx, by_⟩, ax⟩
        rw [hb_eq] at hb_sym hcb_sym
        cases ax <;>
          dsimp [dualBondOfPrimal, LatticeBond.source, LatticeBond.target, LatticeBond.toSym2] at hcb_sym hb_sym <;>
          rcases Sym2.eq_iff.mp hcb_sym with ⟨hz1, hy1⟩ | ⟨hz1, hy1⟩
        · exact hrev df hdf y 2 v01 v11 (by rw [← hb_sym]; dsimp [v01, v11]; simp [Prod.ext_iff] at hz1 ⊢; omega) rfl (by simp [Prod.ext_iff, zDir] at hz1 hy1 ⊢; omega)
        · exact hrev df hdf y 0 v00 v10 (by rw [← hb_sym]; dsimp [v00, v10]; simp [Prod.ext_iff] at hz1 ⊢; omega) rfl (by simp [Prod.ext_iff, zDir] at hz1 hy1 ⊢; omega)
        · exact hrev df hdf y 1 v10 v11 (by rw [← hb_sym]; dsimp [v10, v11]; simp [Prod.ext_iff] at hz1 ⊢; omega) rfl (by simp [Prod.ext_iff, zDir] at hz1 hy1 ⊢; omega)
        · exact hrev df hdf y 3 v00 v01 (by rw [← hb_sym]; dsimp [v00, v01]; simp [Prod.ext_iff] at hz1 ⊢; omega) rfl (by simp [Prod.ext_iff, zDir] at hz1 hy1 ⊢; omega)
      · subst hy; fin_cases i
        · exact hmk ⟨⟨(z.1.1, z.1.2), .horizontal⟩, v00.2, v10.2⟩ v00 v10 (zDir 0) rfl (bne_iff_ne.mp hi)
            (by dsimp [dualBondOfPrimal, LatticeBond.source, LatticeBond.target, zDir]; rw [sub_add_cancel, Sym2.eq_swap])
        · exact hmk ⟨⟨(z.1.1 + 1, z.1.2), .vertical⟩, v10.2, v11.2⟩ v10 v11 (zDir 1) rfl (bne_iff_ne.mp hi)
            (by dsimp [dualBondOfPrimal, LatticeBond.source, LatticeBond.target, zDir]; rw [add_sub_cancel_right])
        · exact hmk ⟨⟨(z.1.1, z.1.2 + 1), .horizontal⟩, v01.2, v11.2⟩ v01 v11 (zDir 2) rfl (bne_iff_ne.mp hi)
            (by dsimp [dualBondOfPrimal, LatticeBond.source, LatticeBond.target, zDir]; rw [add_sub_cancel_right])
        · exact hmk ⟨⟨(z.1.1, z.1.2), .vertical⟩, v00.2, v01.2⟩ v00 v01 (zDir 3) rfl (bne_iff_ne.mp hi)
            (by dsimp [dualBondOfPrimal, LatticeBond.source, LatticeBond.target, zDir]; rw [sub_add_cancel, Sym2.eq_swap])
    rw [← card_neighborFinset_eq_degree, hnb_eq, Finset.card_image_of_injective _ hzDir_inj]
    exact (by decide : ∀ b00 b10 b11 b01 : Bool, Even ((Finset.univ : Finset (Fin 4)).filter fun i : Fin 4 =>
      (match i with | 0 => b00 != b10 | 1 => b10 != b11 | 2 => b01 != b11 | 3 => b00 != b01) = true).card)
      (X v00) (X v10) (X v11) (X v01)
  have hu_ne_v_star : u_star ≠ v_star := G_D.ne_of_adj ((rectangleDualGraph_adj_iff a w h u_star v_star).mpr ⟨de, rfl⟩)
  have hH_D_adj (x y) : H_D.Adj x y ↔ H_full.Adj x y ∧ s(x, y) ≠ s(u_star, v_star) := by
    rw [openGraph_adj, openGraph_adj]
    exact ⟨fun ⟨g, hg, hxy⟩ => ⟨⟨g, (Finset.mem_erase.mp hg).2, hxy⟩, fun hs => (Finset.mem_erase.mp hg).1 (Subtype.ext (hxy.trans hs))⟩,
      fun ⟨⟨g, hg_cut, hxy⟩, hne_s⟩ => ⟨g, Finset.mem_erase.mpr ⟨fun hge => hne_s (hxy.symm.trans (congrArg Subtype.val hge)), hg_cut⟩, hxy⟩⟩
  have hadj_full_uv : H_full.Adj u_star v_star := (openGraph_adj G_D cutDual u_star v_star).mpr ⟨e_star, he_star_cut, rfl⟩
  let Bd : Finset (RectangleDualVertex a w h) := Finset.univ.filter fun z => z.1 ∈ rectangleDualBoundary a w h
  have hreach_or_bd (w_s o_s : RectangleDualVertex a w h)
      (hwo : w_s = u_star ∧ o_s = v_star ∨ w_s = v_star ∧ o_s = u_star) :
      S_D.r w_s o_s ∨ ∃ b ∈ Bd, S_D.r w_s b := by
    by_cases hw_bd : w_s ∈ Bd
    · exact .inr ⟨w_s, hw_bd, S_D.refl _⟩
    · have hw_int : w_s.1 ∈ rectangleDualInterior a w h := by
        by_contra hni; exact hw_bd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨w_s.2, hni⟩⟩)
      have hw_ne_o : w_s ≠ o_s := by rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hu_ne_v_star; exact hu_ne_v_star.symm
      have hodd_end : Odd (H_D.degree w_s) := by
        have hnb : H_D.neighborFinset w_s = (H_full.neighborFinset w_s).erase o_s := by
          ext y; simp only [mem_neighborFinset, Finset.mem_erase, hH_D_adj]
          rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨fun ⟨h1, h2⟩ => ⟨fun hy => h2 (hy ▸ rfl), h1⟩,
              fun ⟨h1, h2⟩ => ⟨h2, fun hs => by rcases Sym2.eq_iff.mp hs with ⟨_, rfl⟩ | ⟨h3, _⟩; exact h1 rfl; exact hu_ne_v_star h3⟩⟩
          · exact ⟨fun ⟨h1, h2⟩ => ⟨fun hy => h2 (hy ▸ Sym2.eq_swap), h1⟩,
              fun ⟨h1, h2⟩ => ⟨h2, fun hs => by rcases Sym2.eq_iff.mp hs with ⟨h3, _⟩ | ⟨_, rfl⟩; exact hu_ne_v_star h3.symm; exact h1 rfl⟩⟩
        have ho_mem : o_s ∈ H_full.neighborFinset w_s := by
          rw [mem_neighborFinset]; rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hadj_full_uv; exact hadj_full_uv.symm
        have hcard := Finset.card_erase_add_one ho_mem
        rw [← hnb, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hcard
        obtain ⟨m, hm⟩ := hdeg_full_even w_s hw_int; exact ⟨m - 1, by omega⟩
      obtain ⟨b, hb1, t, ht, hr⟩ := exists_reachable_between_of_odd_degree_sum H_D {w_s} (Bd ∪ {o_s})
        (by simp [hw_bd, hw_ne_o])
        (fun z hz => by
          simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz
          have hz_int : z.1 ∈ rectangleDualInterior a w h := by
            by_contra hni; exact hz.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨z.2, hni⟩⟩)
          have hzu : z ≠ u_star ∧ z ≠ v_star := by rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact ⟨hz.1, hz.2.2⟩; exact ⟨hz.2.2, hz.1⟩
          have hnb : H_D.neighborFinset z = H_full.neighborFinset z := by
            ext y; simp only [mem_neighborFinset, hH_D_adj]
            exact ⟨And.left, fun h => ⟨h, fun hs => by rcases Sym2.eq_iff.mp hs with ⟨rfl, _⟩ | ⟨rfl, _⟩; exact hzu.1 rfl; exact hzu.2 rfl⟩⟩
          rw [← card_neighborFinset_eq_degree, hnb, card_neighborFinset_eq_degree]; exact hdeg_full_even z hz_int)
        (by rw [Finset.sum_singleton]; exact hodd_end)
      rw [Finset.mem_singleton] at hb1; subst b
      have hSD_wt : S_D.r w_s t := actualConnected_component G_D ξ_D _ (actualConnected_mono hE'_sub hr)
      rcases Finset.mem_union.mp ht with htBd | hto
      · exact .inr ⟨t, htBd, hSD_wt⟩
      · rw [Finset.mem_singleton] at hto; subst hto; exact .inl hSD_wt
  rcases hreach_or_bd u_star v_star (.inl ⟨rfl, rfl⟩) with h1 | ⟨b₁, hb₁, hr₁⟩
  · exact h1
  · rcases hreach_or_bd v_star u_star (.inr ⟨rfl, rfl⟩) with h2 | ⟨b₂, hb₂, hr₂⟩
    · exact S_D.symm h2
    · exact S_D.trans hr₁ (S_D.trans (boundary_component G_D ξ_D _ (.inr ⟨(Finset.mem_filter.mp hb₁).2, (Finset.mem_filter.mp hb₂).2⟩)) (S_D.symm hr₂))

theorem rectangleEuler_additive_card_config (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    componentCount (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h (rectangleCarrierOfConfiguration a w h A)) +
        (w + 1) * (h + 1) =
      A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A + 1 := by
  classical
  change componentCount _ _ (rectangleDualConfiguration a w h (rectangleCarrierOfConfiguration a w h A)) + _ =
    (rectangleCarrierOfConfiguration a w h A).card + componentCount _ _ (toCfg a w h (rectangleCarrierOfConfiguration a w h A)) + 1
  generalize rectangleCarrierOfConfiguration a w h A = B
  induction B using Finset.induction_on with
  | empty =>
    rw [dual_empty_componentCount, Finset.card_empty, zero_add, show toCfg a w h ∅ = ∅ from rfl, free_empty_componentCount]; omega
  | @insert e A₀ heA₀ ih =>
    let p := e.1.out; have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
    have huv : (rectangleGraph a w h).Adj p.1 p.2 := (rectangleGraph a w h).mem_edgeSet.mp (hrepr ▸ e.2)
    have he_mk : e = ⟨s(p.1, p.2), (rectangleGraph a w h).mem_edgeSet.mpr huv⟩ := Subtype.ext hrepr.symm
    let de := rectanglePrimalDualEdgeEquiv a w h e
    let u_s := rectangleDualEdgeSource a w h de; let v_s := rectangleDualEdgeTarget a w h de
    have huv_D : (rectangleDualGraph a w h).Adj u_s v_s := (rectangleDualGraph_adj_iff a w h u_s v_s).mpr ⟨de, rfl⟩
    have hdual_ins : rectangleDualConfiguration a w h A₀ =
        insert ⟨s(u_s, v_s), (rectangleDualGraph a w h).mem_edgeSet.mpr huv_D⟩
          (rectangleDualConfiguration a w h (insert e A₀)) := by
      ext g; obtain ⟨df, rfl⟩ := (rectangleDualGraphEdgeEquiv a w h).surjective g
      rw [show (⟨s(u_s, v_s), (rectangleDualGraph a w h).mem_edgeSet.mpr huv_D⟩ : (rectangleDualGraph a w h).edgeSet) =
          rectangleDualGraphEdgeEquiv a w h de from Subtype.ext rfl,
        Finset.mem_insert, (rectangleDualGraphEdgeEquiv a w h).apply_eq_iff_eq,
        mem_rectangleDualConfiguration, mem_rectangleDualConfiguration, Finset.mem_insert, not_or]
      exact ⟨fun hnA => if hdf : df = de then .inl hdf else .inr ⟨fun hpe => hdf ((rectanglePrimalDualEdgeEquiv a w h).symm.injective hpe), hnA⟩,
        fun h => h.elim (fun h => h ▸ heA₀) And.right⟩
    rw [Finset.card_insert_of_notMem heA₀]
    by_cases hrelP : (componentSetoid (rectangleGraph a w h) (BoundaryCondition.free ∅) (toCfg a w h A₀)).r p.1 p.2
    · have hP : componentCount (rectangleGraph a w h) (BoundaryCondition.free ∅) (toCfg a w h (insert e A₀)) =
          componentCount (rectangleGraph a w h) (BoundaryCondition.free ∅) (toCfg a w h A₀) :=
        he_mk ▸ componentCount_insert_eq_of_related _ (toCfg a w h A₀) huv hrelP
      have hD : componentCount (rectangleDualGraph a w h) (rectangleDualBoundaryCondition a w h) (rectangleDualConfiguration a w h A₀) + 1 =
          componentCount (rectangleDualGraph a w h) (rectangleDualBoundaryCondition a w h) (rectangleDualConfiguration a w h (insert e A₀)) := by
        rw [hdual_ins]; exact componentCount_insert_of_not_related _ _ huv_D (by dsimp [u_s, v_s, de]; rw [he_mk]; exact rect_exclusion a w h A₀ huv (he_mk ▸ heA₀) hrelP)
      omega
    · have hP : componentCount (rectangleGraph a w h) (BoundaryCondition.free ∅) (toCfg a w h (insert e A₀)) + 1 =
          componentCount (rectangleGraph a w h) (BoundaryCondition.free ∅) (toCfg a w h A₀) :=
        he_mk ▸ componentCount_insert_of_not_related _ (toCfg a w h A₀) huv hrelP
      have hD : componentCount (rectangleDualGraph a w h) (rectangleDualBoundaryCondition a w h) (rectangleDualConfiguration a w h A₀) =
          componentCount (rectangleDualGraph a w h) (rectangleDualBoundaryCondition a w h) (rectangleDualConfiguration a w h (insert e A₀)) := by
        rw [hdual_ins]; exact componentCount_insert_eq_of_related _ _ huv_D (by dsimp [u_s, v_s, de]; rw [he_mk]; exact rect_existence a w h A₀ huv hrelP)
      omega

end
end PottsDiscontinuity.FK
