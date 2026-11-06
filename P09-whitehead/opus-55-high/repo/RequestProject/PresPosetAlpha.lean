import RequestProject.PresPosetModel
import RequestProject.PresentationDictionary
import RequestProject.Tac


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

bwd

namespace FiniteChains.PresModel

open Comb

universe u

variable {α J : Type u} (w : J → List (α × Bool))

/-! ### The attaching circle as a path -/

theorem isPath_segAt j {k} (hk : k < (w j).length) :
    IsPathX (orderCx (TCirc w)) (segAt w j k)
      (TCirc.pt w j k CPos.cor) (TCirc.pt w j (TCirc.csucc w j k) CPos.cor) := by
  rw [segAt]
  aesop

theorem isPath_circPath j : ∀ {m}, m ≤ (w j).length →
    IsPathX (orderCx (TCirc w)) (circPath w j m)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j (m % (w j).length) CPos.cor) := by
  intro m
  induction m with
  | zero =>
      tauto
  | succ m ih =>
      intro hm
      have hlt : m < (w j).length := by omega
      have hmod := Nat.mod_eq_of_lt hlt
      have hprev := ih (le_of_lt hlt)
      rw [hmod] at hprev
      exact isPath_append_iff.mpr ⟨_, hprev, isPath_segAt w j hlt⟩

/-- The attaching loop of a relator is a loop at the corner in front of its first letter. -/
theorem isPath_circLoop j :
    IsPathX (orderCx (TCirc w)) (circLoop w j)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j 0 CPos.cor) := by
  have h := isPath_circPath w j (by rfl)
  aesop

/-! ### The attaching circle lies under the two-cell -/

theorem pathIn_mapPath_segAt j {k} (hk : k < (w j).length) :
    PathIn (· ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (segAt w j k)) := by
  have hcs : TCirc.csucc w j k < (w j).length :=
    Nat.mod_lt _ (by grind)
  rw [segAt, dif_pos hk]
  intro e he
  simp only [mapPath, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
  obtain ⟨g, hg, rfl⟩ := he
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨iCirc_le_apexOf w CPos.cor hk, iCirc_le_apexOf w CPos.cedgL hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cmid hk, iCirc_le_apexOf w CPos.cedgL hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cmid hk, iCirc_le_apexOf w CPos.cedgR hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cor hcs, iCirc_le_apexOf w CPos.cedgR hk⟩

theorem pathIn_mapPath_circPath j : ∀ {m}, m ≤ (w j).length →
    PathIn (· ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (circPath w j m)) := by
  intro m
  induction m with
  | zero => tauto
  | succ m ih =>
      intro hm
      have hlt : m < (w j).length := by omega
      show PathIn _ (mapPath _ (circPath w j m ++ segAt w j m))
      rw [mapPath_append]
      intro e he
      rcases List.mem_append.1 he with h | h
      · exact ih (le_of_lt hlt) e h
      · exact pathIn_mapPath_segAt w j hlt e h

/-! ### The attaching circle is carried onto the loop of its word -/

theorem mapPath_segAt j {k} hk :
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (segAt w j k)
      = letterLoop w (w j)[k] := by
  have hp := List.getElem?_eq_getElem hk
  have hmid : iRose w (aFun w (TCirc.pt w j k CPos.cmid))
      = iRose w (Rose.mid (w j)[k].1) := by rw [aFun_pt_cmid_of_get w hp]
  have hL : iRose w (aFun w (TCirc.pt w j k CPos.cedgL))
      = iRose w (Rose.edg (w j)[k].1 (!(w j)[k].2)) := by rw [aFun_pt_cedgL_of_get w hp]
  have hR : iRose w (aFun w (TCirc.pt w j k CPos.cedgR))
      = iRose w (Rose.edg (w j)[k].1 (w j)[k].2) := by rw [aFun_pt_cedgR_of_get w hp]
  rw [segAt, dif_pos hk]
  show [ordPos ((iRose_aFun_monotone w) (TCirc.cor_le_cedgL w hk)),
      ordNeg ((iRose_aFun_monotone w) (TCirc.cmid_le_cedgL w hk)),
      ordPos ((iRose_aFun_monotone w) (TCirc.cmid_le_cedgR w hk)),
      ordNeg ((iRose_aFun_monotone w) (TCirc.cor_csucc_le_cedgR w hk))]
    = letterLoop w (w j)[k]
  cases' hpair : (w j)[k] with i b
  cases b <;> aesop

theorem mapPath_circPath j : ∀ {m}, m ≤ (w j).length →
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (circPath w j m)
      = wordLoop w ((w j).take m) := by
  intro m
  induction m with
  | zero => tauto
  | succ m ih =>
      intro hm
      have hlt : m < (w j).length := by omega
      have hsplit : (w j).take (m + 1) = (w j).take m ++ [(w j)[m]] := by
        simp
      show mapPath _ (circPath w j m ++ segAt w j m) = _
      rw [mapPath_append, ih (le_of_lt hlt), mapPath_segAt w j hlt, hsplit, wordLoop_append]
      grind [wordLoop]

/-! ### The loop of a relator word is null-homotopic in the model -/

theorem htpy_wordLoop_nil j :
    Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w) (wordLoop w (w j)) [] := by
  by_cases h0 : 0 < (w j).length
  case neg =>
    have hnil : w j = [] := by simp_all
    rw [hnil]
    exact Htpy.refl _
  case pos =>
  set u : TCirc w := TCirc.pt w j 0 CPos.cor with hu
  have hloop :=
    isPath_circLoop w j
  have hfg := iCirc_le_iRose_aFun w
  -- the image of the attaching circle in the base copy is the loop of the word
  have himg : mapPath (orderCxMap _ (iRose_aFun_monotone w))
      (circLoop w j) = wordLoop w (w j) := by
    have h := mapPath_circPath w j (by rfl)
    aesop
  -- the attaching circle itself dies under the cone point of the two-cell
  have hcone :=
    htpy_nil_of_pathIn_le _ (iCirc_le_apexOf w CPos.cor h0)
      (isPath_mapPath _ hloop)
      (pathIn_mapPath_circPath w j (by simp))
  -- the naturality homotopy relates the two images
  have hnat := htpy_loop_mapPath_le (iCirc_monotone w) (iRose_aFun_monotone w) hfg hloop
  rw [himg] at hnat
  have h1 : Htpy _ (ptBase w) (ptBase w)
      ([ordNeg (hfg u)] ++ mapPath (orderCxMap _ (iCirc_monotone w)) (circLoop w j)
        ++ [ordPos (hfg u)])
      ([ordNeg (hfg u)] ++ [] ++ [ordPos (hfg u)]) :=
    hcone.congr_append (by aesop) (by aesop)
  have h2 : Htpy _ (ptBase w) (ptBase w)
      [ordNeg (hfg u), ordPos (hfg u)] [] := htpy_ordNeg_ordPos _
  refine hnat.trans (h1.trans ?_)
  simpa using h2

/-! ### The comparison homomorphism -/

/-- The class of the loop of a word. -/
def wordClass (l : List (α × Bool)) :=
  Pi1.mk ⟨wordLoop w l, isPath_wordLoop w l⟩

/-- The class of the loop of a generator. -/
def genClass (i : α) :=
  Pi1.mk ⟨genLoop w i, isPath_genLoop w i⟩

theorem wordClass_append l l' :
    wordClass w (l ++ l') = wordClass w l * wordClass w l' := by
  refine Quotient.sound ?_
  simp



/-- The homomorphism of the free group into the fundamental group of the model. -/
def alphaFree :=
  FreeGroup.lift (genClass w)


theorem alphaFree_mk l : alphaFree w (FreeGroup.mk l) = wordClass w l := by
  induction l with
  | nil =>
      rfl
  | cons eb l ih =>
      cases' eb with i b
      have hsplit : ((i, b) :: l) = [(i, b)] ++ l := rfl
      rw [hsplit, ← FreeGroup.mul_mk, map_mul, ih, wordClass_append]
      congr 1
      cases b
      · rfl
      rfl

/-- **The relators die in the model.** -/
theorem alphaFree_relator j : alphaFree w (FreeGroup.mk (w j)) = 1 := by
  rw [alphaFree_mk]
  exact Quotient.sound (htpy_wordLoop_nil w j)

/-! ### The model of a presentation -/

/-- A word representing each relator of the presentation `ρ`. -/
noncomputable def presWords (ρ : J → FreeGroup α) : J → List (α × Bool) := fun j => Quot.out (ρ j)

theorem mk_presWords (ρ : J → FreeGroup α) j :
    FreeGroup.mk (presWords ρ j) = ρ j := Quot.out_eq _
