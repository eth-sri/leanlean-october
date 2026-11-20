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

namespace FiniteChains
namespace PresModel

open Comb

universe u

variable {α J : Type u} (w : J → List (α × Bool))

/-! ### The attaching circle as a path -/

theorem isPath_segAt (j : J) {k : ℕ} (hk : k < (w j).length) :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (segAt w j k)
      (TCirc.pt w j k CPos.cor) (TCirc.pt w j (TCirc.csucc w j k) CPos.cor) := by
  rw [segAt, dif_pos hk]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem isPath_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
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
theorem isPath_circLoop (j : J) :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circLoop w j)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j 0 CPos.cor) := by
  have h := isPath_circPath w j (le_refl (w j).length)
  aesop

/-! ### The attaching circle lies under the two-cell -/

theorem pathIn_mapPath_segAt (j : J) {k : ℕ} (hk : k < (w j).length) :
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

theorem pathIn_mapPath_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    PathIn (fun x : PresPos w => x ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (circPath w j m)) := by
  intro m
  induction m with
  | zero => tauto
  | succ m ih =>
      intro hm
      have hlt  := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      show PathIn _ (mapPath _ (circPath w j m ++ segAt w j m))
      rw [mapPath_append]
      intro e he
      rcases List.mem_append.1 he with h | h
      · exact ih (le_of_lt hlt) e h
      · exact pathIn_mapPath_segAt w j hlt e h

/-! ### The attaching circle is carried onto the loop of its word -/

def roseGeneratorWord (a : α) : List ((orderCx (Rose α)).E × Bool) :=
  [ordPos (Rose.base_le_edg a false), ordNeg (Rose.mid_le_edg a false),
    ordPos (Rose.mid_le_edg a true), ordNeg (Rose.base_le_edg a true)]

theorem roseGeneratorWord_valid (a : α) :
    IsPath (orderCx (Rose α)).src (orderCx (Rose α)).tgt (roseGeneratorWord a) .base .base :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def roseLetterWord (p : α × Bool) : List ((orderCx (Rose α)).E × Bool) :=
  if p.2 then roseGeneratorWord p.1 else revPath (X := orderCx (Rose α)) (roseGeneratorWord p.1)

def roseWord (l : List (α × Bool)) : List ((orderCx (Rose α)).E × Bool) := l.flatMap roseLetterWord

theorem roseLetterWord_valid (p : α × Bool) :
    IsPath (orderCx (Rose α)).src (orderCx (Rose α)).tgt (roseLetterWord p) .base .base := by
  rcases p with ⟨a, b⟩
  cases b
  · exact isPath_revPath (roseGeneratorWord_valid a)
  · trivial

theorem roseWord_valid (l : List (α × Bool)) :
    IsPath (orderCx (Rose α)).src (orderCx (Rose α)).tgt (roseWord l) .base .base := by
  induction l with
  | nil => rfl
  | cons p l ih => exact (roseLetterWord_valid p).append ih

theorem mapPath_aFun_segAt (j : J) {k : ℕ} (hk : k < (w j).length) :
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (segAt w j k) = roseLetterWord (w j)[k] := by
  have hp  := List.getElem?_eq_getElem hk
  have hmid : aFun w (TCirc.pt w j k CPos.cmid) = Rose.mid (w j)[k].1 := by
    rw [aFun_pt_cmid_of_get w hp]
  have hL : aFun w (TCirc.pt w j k CPos.cedgL) = Rose.edg (w j)[k].1 (!(w j)[k].2) := by
    rw [aFun_pt_cedgL_of_get w hp]
  have hR : aFun w (TCirc.pt w j k CPos.cedgR) = Rose.edg (w j)[k].1 (w j)[k].2 := by
    rw [aFun_pt_cedgR_of_get w hp]
  rw [segAt, dif_pos hk]
  change [ordPos ((aFun_monotone w) (TCirc.cor_le_cedgL w hk)),
    ordNeg ((aFun_monotone w) (TCirc.cmid_le_cedgL w hk)),
    ordPos ((aFun_monotone w) (TCirc.cmid_le_cedgR w hk)),
    ordNeg ((aFun_monotone w) (TCirc.cor_csucc_le_cedgR w hk))] = _
  rcases he : (w j)[k] with ⟨a, b⟩
  rw [he] at hmid hL hR
  cases b
  · aesop
  · aesop

theorem mapPath_aFun_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (circPath w j m) = roseWord ((w j).take m) := by
  intro m
  induction m with
  | zero => aesop
  | succ m ih =>
    intro hm
    have hlt : m < (w j).length := by omega
    have hsplit : (w j).take (m + 1) = (w j).take m ++ [(w j)[m]] := by
      simp
    change mapPath _ (circPath w j m ++ segAt w j m) = _
    rw [mapPath_append, ih (Nat.le_of_lt hlt), mapPath_aFun_segAt w j hlt, hsplit]
    simp only [roseWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem mapPath_aFun_circLoop (j : J) :
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (circLoop w j) = roseWord (w j) := by
  simpa only [List.take_length, circLoop] using mapPath_aFun_circPath w j (le_refl (w j).length)

private theorem mapPath_iRose_letter (p : α × Bool) :
    mapPath (orderCxMap (iRose w) (iRose_monotone w)) (roseLetterWord p) = letterLoop w p := by
  rcases p with ⟨i, b⟩
  cases b <;> rfl

private theorem mapPath_circPath (j : J) {m : ℕ} (hm : m ≤ (w j).length) :
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (circPath w j m)
      = wordLoop w ((w j).take m) := by
  change mapPath ((orderCxMap (iRose w) (iRose_monotone w)).comp
    (orderCxMap (aFun w) (aFun_monotone w))) _ = _
  rw [← mapPath_comp, mapPath_aFun_circPath w j hm]
  induction (w j).take m with
  | nil => rfl
  | cons e l ih =>
      change mapPath _ (roseLetterWord e ++ roseWord l) = letterLoop w e ++ wordLoop w l
      rw [mapPath_append, mapPath_iRose_letter, ih]

/-! ### The loop of a relator word is null-homotopic in the model -/

theorem htpy_wordLoop_nil (j : J) :
    Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w) (wordLoop w (w j)) [] := by
  by_cases h0 : 0 < (w j).length
  case neg =>
    have hnil  := List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h0)
    rw [hnil]
    tauto
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
  aesop

/-! ### The comparison homomorphism -/

/-- The class of the loop of a word. -/
def wordClass (l : List (α × Bool)) : Pi1 (orderCx (PresPos w)) (ptBase w) :=
  Pi1.mk ⟨wordLoop w l, isPath_wordLoop w l⟩

/-- The class of the loop of a generator. -/
def genClass (i : α) : Pi1 (orderCx (PresPos w)) (ptBase w) :=
  Pi1.mk ⟨genLoop w i, isPath_genLoop w i⟩

theorem wordClass_append (l l' : List (α × Bool)) :
    wordClass w (l ++ l') = wordClass w l * wordClass w l' := by
  refine Quotient.sound ?_ <;> simp



/-- The homomorphism of the free group into the fundamental group of the model. -/
def alphaFree : FreeGroup α →* Pi1 (orderCx (PresPos w)) (ptBase w) :=
  FreeGroup.lift (genClass w)

theorem alphaFree_of (i : α) : alphaFree w (FreeGroup.of i) = genClass w i := by
  aesop

theorem alphaFree_mk (l : List (α × Bool)) : alphaFree w (FreeGroup.mk l) = wordClass w l := by
  induction l with
  | nil =>
      rfl
  | cons eb l ih =>
      obtain ⟨i, b⟩ := eb
      have hsplit : ((i, b) :: l) = [(i, b)] ++ l := rfl
      rw [hsplit, ← FreeGroup.mul_mk, map_mul, ih, wordClass_append]
      congr 1
      cases b <;> rfl

/-- **The relators die in the model.** -/
theorem alphaFree_relator (j : J) : alphaFree w (FreeGroup.mk (w j)) = 1 := by
  rw [alphaFree_mk]
  exact Quotient.sound (htpy_wordLoop_nil w j)

/-! ### The model of a presentation -/

/-- A word representing each relator of the presentation `ρ`. -/
noncomputable def presWords (ρ : J → FreeGroup α) : J → List (α × Bool) := fun j => Quot.out (ρ j)

theorem mk_presWords (ρ : J → FreeGroup α) (j : J) :
    FreeGroup.mk (presWords ρ j) = ρ j := Quot.out_eq _




end PresModel
end FiniteChains
