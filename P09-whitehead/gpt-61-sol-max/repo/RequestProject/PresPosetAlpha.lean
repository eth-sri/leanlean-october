import Mathlib.Tactic

import RequestProject.PresPosetModel
import RequestProject.PresentationDictionary

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

namespace FiniteChains.PresModel


open Comb


variable {α J : Type u} (w : J → List (α × Bool))

/-! ### The attaching circle as a path -/

variable (j : J)
  {k : ℕ}
theorem isPath_segAt   (hk : k < (w j).length) :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (segAt w j k)
      (TCirc.pt w j k CPos.cor) (TCirc.pt w j (TCirc.csucc w j k) CPos.cor) := by aesop (add simp [segAt])

theorem isPath_circPath  : ∀ {m : ℕ}, m ≤ (w j).length →
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circPath w j m)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j (m % (w j).length) CPos.cor) := by
  intro m
  induction m with
  | zero =>
      aesop
  | succ m ih =>
      intro hm
      have hlt  := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hmod  := Nat.mod_eq_of_lt hlt
      have hprev := ih (le_of_lt hlt)
      rw [hmod] at hprev
      show IsPath _ _ (circPath w j m ++ segAt w j m) _ _
      exact isPath_append_iff.mpr ⟨_, hprev, isPath_segAt w j hlt⟩

/-- The attaching loop of a relator is a loop at the corner in front of its first letter. -/
theorem isPath_circLoop  :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circLoop w j)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j 0 CPos.cor) := by
  have h := isPath_circPath w j (le_refl (w j).length)
  rwa [Nat.mod_self] at h

/-! ### The attaching circle lies under the two-cell -/

theorem pathIn_mapPath_segAt   (hk : k < (w j).length) :
    PathIn (fun x : PresPos w => x ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (segAt w j k)) := by
  have hcs : TCirc.csucc w j k < (w j).length :=
    Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le k) hk)
  rw [segAt, dif_pos hk]
  intro e he
  simp only [mapPath, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
  obtain ⟨g, hg, rfl⟩ := he
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨iCirc_le_apexOf w CPos.cor hk, iCirc_le_apexOf w CPos.cedgL hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cmid hk, iCirc_le_apexOf w CPos.cedgL hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cmid hk, iCirc_le_apexOf w CPos.cedgR hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cor hcs, iCirc_le_apexOf w CPos.cedgR hk⟩

theorem pathIn_mapPath_circPath  : ∀ {m : ℕ}, m ≤ (w j).length →
    PathIn (fun x : PresPos w => x ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (circPath w j m)) := by
  classical
  intro m
  induction m <;> grind [FiniteChains.Comb.PathIn, mapPath, circPath, pathIn_mapPath_segAt]

/-! ### The attaching circle is carried onto the loop of its word -/

theorem mapPath_segAt   (hk : k < (w j).length) :
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (segAt w j k)
      = letterLoop w (w j)[k] := by
  have hp  := List.getElem?_eq_getElem hk
  have hcor : iRose w (aFun w (TCirc.pt w j k CPos.cor)) = iRose w Rose.base := rfl
  have hcorS : iRose w (aFun w (TCirc.pt w j (TCirc.csucc w j k) CPos.cor))
      = iRose w Rose.base := rfl
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
  rcases hpair : (w j)[k] with ⟨i, b⟩
  rw [hpair] at hmid hL hR
  cases b with
  | true =>
      aesop
  | false =>
      aesop

theorem mapPath_circPath  : ∀ {m : ℕ}, m ≤ (w j).length →
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (circPath w j m)
      = wordLoop w ((w j).take m) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hlt  := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hsplit : (w j).take (m + 1) = (w j).take m ++ [(w j)[m]] := by
        simp_all
      grind [mapPath, circPath, mapPath_segAt, wordLoop]

/-! ### The loop of a relator word is null-homotopic in the model -/

theorem htpy_wordLoop_nil  :
    Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w) (wordLoop w (w j)) [] := by
  by_cases h0 : 0 < (w j).length
  case neg =>
    classical simp_all [Nat.eq_zero_of_not_pos, FiniteChains.Comb.Htpy.refl]
  case pos =>
  set u : TCirc w := TCirc.pt w j 0 CPos.cor with hu
  have hloop  :=
    isPath_circLoop w j
  have hfg  := iCirc_le_iRose_aFun w
  -- the image of the attaching circle in the base copy is the loop of the word
  have himg : mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w))
      (circLoop w j) = wordLoop w (w j) := by
    have h := mapPath_circPath w j (le_refl (w j).length)
    rwa [List.take_length] at h
  -- the attaching circle itself dies under the cone point of the two-cell
  have hcone  :=
    htpy_nil_of_pathIn_le (apexOf w j) (iCirc_le_apexOf w CPos.cor h0)
      (isPath_mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) hloop)
      (pathIn_mapPath_circPath w j (le_refl (w j).length))
  -- the naturality homotopy relates the two images
  have hnat := htpy_loop_mapPath_le (iCirc_monotone w) (iRose_aFun_monotone w) hfg hloop
  rw [himg] at hnat
  have h1  :=
    hcone.congr_append (isPath_ordNeg (hfg u)) (isPath_ordPos (hfg u))
  have h2  := htpy_ordNeg_ordPos (hfg u)
  refine hnat.trans (h1.trans ?_)
  simpa using h2

/-! ### The comparison homomorphism -/

variable (l : List (α × Bool))
/-- The class of the loop of a word. -/
def wordClass   :=
  Pi1.mk ⟨wordLoop w l, isPath_wordLoop w l⟩

/-- The class of the loop of a generator. -/
def genClass (i : α)  :=
  Pi1.mk ⟨genLoop w i, isPath_genLoop w i⟩







/-- The homomorphism of the free group into the fundamental group of the model. -/
def alphaFree  :=
  FreeGroup.lift (genClass w)



theorem alphaFree_mk  : alphaFree w (FreeGroup.mk l) = wordClass w l := by
  induction l <;> aesop (add simp [alphaFree])

/-- **The relators die in the model.** -/
theorem alphaFree_relator  : alphaFree w (FreeGroup.mk (w j)) = 1 := by
  rw [alphaFree_mk]
  exact Quotient.sound (htpy_wordLoop_nil w j)

/-! ### The model of a presentation -/

/-- A word representing each relator of the presentation `ρ`. -/
noncomputable def presWords (ρ : J → FreeGroup α)  := fun j => Quot.out (ρ j)

theorem mk_presWords (ρ : J → FreeGroup α) (j : J) :
    FreeGroup.mk (presWords ρ j) = ρ j := Quot.out_eq _







end FiniteChains.PresModel

