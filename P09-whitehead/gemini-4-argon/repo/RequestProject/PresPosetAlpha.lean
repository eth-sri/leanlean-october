module

public import RequestProject.PresPosetModel
public import RequestProject.PresentationDictionary

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.PresModel

open Comb

universe u

variable {α J : Type u} (w : J → List (α × Bool))

theorem isPath_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circPath w j m)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j (m % (w j).length) CPos.cor)
  | 0, _ => by show TCirc.pt w j 0 CPos.cor = TCirc.pt w j (0 % (w j).length) CPos.cor; rw [Nat.zero_mod]
  | m + 1, hm => by
      have hlt : m < (w j).length := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hprev := isPath_circPath j (le_of_lt hlt)
      rw [Nat.mod_eq_of_lt hlt] at hprev
      refine isPath_append_iff.mpr ⟨_, hprev, ?_⟩
      rw [segAt, dif_pos hlt]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem pathIn_mapPath_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    PathIn (fun x : PresPos w => x ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (circPath w j m))
  | 0, _ => pathIn_nil _
  | m + 1, hm => by
      have hlt : m < (w j).length := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hcs : TCirc.csucc w j m < (w j).length := Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le m) hlt)
      show PathIn _ (mapPath _ (circPath w j m ++ segAt w j m))
      rw [mapPath_append]
      intro e he
      rcases List.mem_append.1 he with h | h
      · exact pathIn_mapPath_circPath j (le_of_lt hlt) e h
      · rw [segAt, dif_pos hlt] at h
        simp only [mapPath, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with ⟨g, rfl | rfl | rfl | rfl, rfl⟩
        · exact ⟨iCirc_le_apexOf w CPos.cor hlt, iCirc_le_apexOf w CPos.cedgL hlt⟩
        · exact ⟨iCirc_le_apexOf w CPos.cmid hlt, iCirc_le_apexOf w CPos.cedgL hlt⟩
        · exact ⟨iCirc_le_apexOf w CPos.cmid hlt, iCirc_le_apexOf w CPos.cedgR hlt⟩
        · exact ⟨iCirc_le_apexOf w CPos.cor hcs, iCirc_le_apexOf w CPos.cedgR hlt⟩

theorem mapPath_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (circPath w j m)
      = wordLoop w ((w j).take m)
  | 0, _ => rfl
  | m + 1, hm => by
      have hlt : m < (w j).length := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hp : (w j)[m]? = some (w j)[m] := List.getElem?_eq_getElem hlt
      have hseg : mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (segAt w j m)
          = letterLoop w (w j)[m] := by
        have hcor : iRose w (aFun w (TCirc.pt w j m CPos.cor)) = iRose w Rose.base := rfl
        have hcorS : iRose w (aFun w (TCirc.pt w j (TCirc.csucc w j m) CPos.cor)) = iRose w Rose.base := rfl
        have hmid : iRose w (aFun w (TCirc.pt w j m CPos.cmid)) = iRose w (Rose.mid (w j)[m].1) := by
          rw [aFun_pt_cmid_of_get w hp]
        have hL : iRose w (aFun w (TCirc.pt w j m CPos.cedgL)) = iRose w (Rose.edg (w j)[m].1 (!(w j)[m].2)) := by
          rw [aFun_pt_cedgL_of_get w hp]
        have hR : iRose w (aFun w (TCirc.pt w j m CPos.cedgR)) = iRose w (Rose.edg (w j)[m].1 (w j)[m].2) := by
          rw [aFun_pt_cedgR_of_get w hp]
        rw [segAt, dif_pos hlt]
        show [ordPos ((iRose_aFun_monotone w) (TCirc.cor_le_cedgL w hlt)),
            ordNeg ((iRose_aFun_monotone w) (TCirc.cmid_le_cedgL w hlt)),
            ordPos ((iRose_aFun_monotone w) (TCirc.cmid_le_cedgR w hlt)),
            ordNeg ((iRose_aFun_monotone w) (TCirc.cor_csucc_le_cedgR w hlt))] = letterLoop w (w j)[m]
        rcases hpair : (w j)[m] with ⟨i, false | true⟩ <;> rw [hpair] at hmid hL hR
        · show _ = genLoopRev w i
          simp only [genLoopRev, List.cons.injEq, and_true]
          exact ⟨ordPos_congr hcor hL _ _, ordNeg_congr hmid hL _ _,
            ordPos_congr hmid hR _ _, ordNeg_congr hcorS hR _ _⟩
        · show _ = genLoop w i
          simp only [genLoop, List.cons.injEq, and_true]
          exact ⟨ordPos_congr hcor hL _ _, ordNeg_congr hmid hL _ _,
            ordPos_congr hmid hR _ _, ordNeg_congr hcorS hR _ _⟩
      show mapPath _ (circPath w j m ++ segAt w j m) = _
      rw [mapPath_append, mapPath_circPath j (le_of_lt hlt), hseg, List.take_add_one, hp,
        Option.toList_some, wordLoop_append]
      simp [wordLoop]

def wordClass (l : List (α × Bool)) : Pi1 (orderCx (PresPos w)) (ptBase w) :=
  Pi1.mk ⟨wordLoop w l, isPath_wordLoop w l⟩

def genClass (i : α) : Pi1 (orderCx (PresPos w)) (ptBase w) :=
  Pi1.mk ⟨genLoop w i, isPath_genLoop w i⟩

theorem wordClass_append (l l' : List (α × Bool)) :
    wordClass w (l ++ l') = wordClass w l * wordClass w l' :=
  Quotient.sound (by
    show Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w) (wordLoop w (l ++ l')) (wordLoop w l ++ wordLoop w l')
    rw [wordLoop_append])

def alphaFree : FreeGroup α →* Pi1 (orderCx (PresPos w)) (ptBase w) :=
  FreeGroup.lift (genClass w)

theorem alphaFree_of (i : α) : alphaFree w (FreeGroup.of i) = genClass w i := by
  simp [alphaFree]

theorem alphaFree_mk : ∀ l : List (α × Bool), alphaFree w (FreeGroup.mk l) = wordClass w l
  | [] => by simp only [alphaFree, FreeGroup.lift_mk, List.map_nil, List.prod_nil]; rfl
  | (i, b) :: l => by
      rw [show ((i, b) :: l) = [(i, b)] ++ l from rfl, ← FreeGroup.mul_mk, map_mul,
        alphaFree_mk l, wordClass_append]
      congr 1; cases b <;> · simp [alphaFree, FreeGroup.lift_mk]; rfl

theorem alphaFree_relator (j : J) : alphaFree w (FreeGroup.mk (w j)) = 1 := by
  rw [alphaFree_mk]
  refine Quotient.sound ?_
  show Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w) (wordLoop w (w j)) []
  by_cases h0 : 0 < (w j).length
  · set u : TCirc w := TCirc.pt w j 0 CPos.cor
    have hloop : IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circLoop w j) u u := by
      have h := isPath_circPath w j (le_refl (w j).length); rwa [Nat.mod_self] at h
    have hfg := iCirc_le_iRose_aFun w
    have himg := mapPath_circPath w j (le_refl (w j).length)
    rw [List.take_length] at himg
    have hcone : Htpy (orderCx (PresPos w)) (iCirc w u) (iCirc w u)
        (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (circLoop w j)) [] :=
      htpy_nil_of_pathIn_le (apexOf w j) (iCirc_le_apexOf w CPos.cor h0)
        (isPath_mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) hloop)
        (pathIn_mapPath_circPath w j (le_refl (w j).length))
    have hnat := htpy_loop_mapPath_le (iCirc_monotone w) (iRose_aFun_monotone w) hfg hloop
    erw [himg] at hnat
    exact hnat.trans ((hcone.congr_append (isPath_ordNeg (hfg u)) (isPath_ordPos (hfg u))).trans
      (by simpa using htpy_ordNeg_ordPos (hfg u)))
  · rw [List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h0)]; exact Htpy.refl _

def presWords (ρ : J → FreeGroup α) : J → List (α × Bool) := fun j => Quot.out (ρ j)

theorem mk_presWords (ρ : J → FreeGroup α) (j : J) :
    FreeGroup.mk (presWords ρ j) = ρ j := Quot.out_eq _
