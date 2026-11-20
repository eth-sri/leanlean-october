module

public import RequestProject.PresPosetModel
public import RequestProject.PresentationDictionary

@[expose] public section

/-!
# The generators of a presentation as loops of the poset model

This file constructs the first half of the marked comparison between a presentation and the
poset model `FiniteChains.PresModel.PresPos` of its presentation complex: the homomorphism

    `alphaHom : PresGroup ρ →* π₁(orderCx (PresPos w), ptBase)`

carrying the class of a generator to the loop of that generator.  What has to be proved for it
to exist is that the loop read off a relator word is null-homotopic in the model
(`FiniteChains.PresModel.htpy_wordLoop_nil`), and this is proved, not assumed: the attaching
circle of the relator is carried onto that loop by the cylinder (naturality homotopy
`FiniteChains.Comb.htpy_loop_mapPath_le`), and the attaching circle itself dies under the cone
point of the two-cell (`FiniteChains.Comb.htpy_nil_of_pathIn_le`).

Injectivity of `alphaHom` is proved in `RequestProject/PresPosetReading.lean` by constructing a
left inverse.
-/
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace FiniteChains
namespace PresModel

open Comb

universe u

variable {α J : Type u} (w : J → List (α × Bool))

/-! ### The attaching circle as a path -/

variable (j : J)

theorem isPath_segAt {k : ℕ} (hk : k < (w j).length) :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (segAt w j k)
      (TCirc.pt w j k CPos.cor) (TCirc.pt w j (TCirc.csucc w j k) CPos.cor) := by
  rw [segAt, dif_pos hk] <;> aesop

theorem isPath_circPath : ∀ {m : ℕ}, m ≤ (w j).length →
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circPath w j m)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j (m % (w j).length) CPos.cor) := by
  intro m
  induction m with
  | zero =>
      solve_by_elim
  | succ m ih =>
      intro hm
      have hlt := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hprev := ih (le_of_lt hlt)
      rw [(Nat.mod_eq_of_lt hlt)] at hprev
      exact isPath_append_iff.mpr ⟨_, hprev, isPath_segAt w j hlt⟩

/-- The attaching loop of a relator is a loop at the corner in front of its first letter. -/
theorem isPath_circLoop :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circLoop w j)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j 0 CPos.cor) := by
  have h := isPath_circPath w j (le_refl (w j).length)
  aesop

/-! ### The attaching circle lies under the two-cell -/

variable (j : J)

theorem pathIn_mapPath_segAt {k : ℕ} (hk : k < (w j).length) :
    PathIn (fun x : PresPos w => x ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (segAt w j k)) := by
  have hcs : TCirc.csucc w j k < (w j).length :=
    Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le k) hk)
  rw [segAt, dif_pos hk]
  intro e he
  simp only [mapPath, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
  obtain ⟨g, hg, rfl⟩ := he
  rcases hg with rfl | rfl | rfl | rfl
  · solve_by_elim [iCirc_le_apexOf]
  · solve_by_elim [iCirc_le_apexOf]
  · solve_by_elim [iCirc_le_apexOf]
  · solve_by_elim [iCirc_le_apexOf]

theorem pathIn_mapPath_circPath : ∀ {m : ℕ}, m ≤ (w j).length →
    PathIn (fun x : PresPos w => x ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (circPath w j m)) := by
  intro m
  induction m with
  | zero => solve_by_elim [pathIn_nil]
  | succ m ih =>
      intro hm
      show PathIn _ (mapPath _ (circPath w j m ++ segAt w j m))
      rw [mapPath_append]
      intro e he
      rcases List.mem_append.1 he with h | h
      · exact ih (le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self m) hm)) e h
      · apply pathIn_mapPath_segAt <;> assumption

/-! ### The attaching circle is carried onto the loop of its word -/

variable (j : J)

theorem mapPath_segAt {k : ℕ} (hk : k < (w j).length) :
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (segAt w j k)
      = letterLoop w (w j)[k] := by
  have hp := List.getElem?_eq_getElem hk
  have hmid : iRose w (aFun w (TCirc.pt w j k CPos.cmid))
      = iRose w (Rose.mid (w j)[k].1) := by solve_by_elim [aFun_pt_cmid_of_get]
  have hL : iRose w (aFun w (TCirc.pt w j k CPos.cedgL))
      = iRose w (Rose.edg (w j)[k].1 (!(w j)[k].2)) := by solve_by_elim [aFun_pt_cedgL_of_get]
  have hR : iRose w (aFun w (TCirc.pt w j k CPos.cedgR))
      = iRose w (Rose.edg (w j)[k].1 (w j)[k].2) := by solve_by_elim [aFun_pt_cedgR_of_get]
  rw [segAt, dif_pos hk]
  show [ordPos ((iRose_aFun_monotone w) (TCirc.cor_le_cedgL w hk)),
      ordNeg ((iRose_aFun_monotone w) (TCirc.cmid_le_cedgL w hk)),
      ordPos ((iRose_aFun_monotone w) (TCirc.cmid_le_cedgR w hk)),
      ordNeg ((iRose_aFun_monotone w) (TCirc.cor_csucc_le_cedgR w hk))]
    = letterLoop w _
  rcases hpair : (w j)[k] with ⟨i, b⟩
  cases b with
  | true =>
      aesop
  | false =>
      aesop

theorem mapPath_circPath : ∀ {m : ℕ}, m ≤ (w j).length →
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (circPath w j m)
      = wordLoop w ((w j).take m) := by
  intro m
  induction m with
  | zero => solve_by_elim
  | succ m ih =>
      intro hm
      have hlt := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hsplit : (w j).take (m + 1) = (w j).take m ++ [(w j)[m]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        rfl
      show mapPath _ (circPath w j m ++ segAt w j m) = _
      rw [mapPath_append, ih (le_of_lt hlt), mapPath_segAt w j hlt, hsplit, wordLoop_append]
      simp [wordLoop]

/-! ### The loop of a relator word is null-homotopic in the model -/

theorem htpy_wordLoop_nil (j : J) :
    Htpy _ (ptBase w) (ptBase w) (wordLoop w (w j)) [] := by
  by_cases h0 : 0 < (w j).length
  case neg =>
    rw [(List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h0))]
    exact Htpy.refl _
  case pos =>
  set u : TCirc w := TCirc.pt w j 0 CPos.cor with hu
  have hloop :=
    isPath_circLoop w j
  have hfg := iCirc_le_iRose_aFun w
  -- the image of the attaching circle in the base copy is the loop of the word
  have himg : mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w))
      (circLoop w j) = wordLoop w (w j) := by
    have h := mapPath_circPath w j (le_refl (w j).length)
    aesop
  -- the attaching circle itself dies under the cone point of the two-cell
  have hcone :=
    htpy_nil_of_pathIn_le _ (iCirc_le_apexOf w CPos.cor h0)
      (isPath_mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) hloop)
      (pathIn_mapPath_circPath w j (le_refl (w j).length))
  -- the naturality homotopy relates the two images
  have hnat := htpy_loop_mapPath_le (iCirc_monotone w) (iRose_aFun_monotone w) hfg hloop
  rw [himg] at hnat
  have h2 := htpy_ordNeg_ordPos (hfg u)
  refine hnat.trans ((hcone.congr_append (isPath_ordNeg (hfg u)) (isPath_ordPos (hfg u))).trans ?_)
  assumption

/-! ### The comparison homomorphism -/

/-- The class of the loop of a word. -/
def wordClass (l : List _) :=
  Pi1.mk ⟨wordLoop w l, isPath_wordLoop w l⟩

/-- The class of the loop of a generator. -/
def genClass (i : α) :=
  Pi1.mk ⟨genLoop w i, isPath_genLoop w i⟩

theorem wordClass_append (l l' : List _) :
    wordClass w (l ++ l') = wordClass w l * wordClass w l' := by
  refine Quotient.sound ?_ <;> simp_all

variable (i : α)

theorem wordClass_single_true : wordClass w [(i, true)] = genClass w i := rfl

theorem wordClass_single_false : wordClass w [(i, false)] = (genClass w i)⁻¹ := rfl

/-- The homomorphism of the free group into the fundamental group of the model. -/
def alphaFree :=
  FreeGroup.lift (genClass w)

theorem alphaFree_mk (l : List _) : alphaFree w (FreeGroup.mk l) = wordClass w l := by
  induction l with
  | nil =>
      rfl
  | cons eb l ih =>
      obtain ⟨i, b⟩ := eb
      have hsplit : ((i, b) :: l) = [(i, b)] ++ l := rfl
      rw [hsplit, ← FreeGroup.mul_mk, map_mul, ih, wordClass_append]
      grind [wordClass_single_false, alphaFree, FreeGroup.lift_mk, wordClass_single_true]

/-- **The relators die in the model.** -/
theorem alphaFree_relator (j : J) : alphaFree w (FreeGroup.mk (w j)) = 1 := by
  rw [alphaFree_mk]
  exact Quotient.sound (htpy_wordLoop_nil w j)

/-! ### The model of a presentation -/

variable (ρ : J → FreeGroup α)

/-- A word representing each relator of the presentation `ρ`. -/
def presWords : J → List (α × Bool) := fun j => Quot.out (ρ j)

theorem mk_presWords (j : J) :
    FreeGroup.mk (presWords ρ j) = ρ j := Quot.out_eq _

end PresModel
end FiniteChains
