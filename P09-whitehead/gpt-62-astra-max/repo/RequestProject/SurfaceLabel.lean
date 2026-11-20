module

public import RequestProject.SurfaceCells
public import RequestProject.AttCycle

@[expose] public section

/-!
# The marking of the polygon: the cellular map into the model of the presentation complex

The polygon of `RequestProject/SurfacePoset.lean` is *marked*: its boundary is subdivided into
the letters of a chosen relator word `w j₀`, and the marking is a **monotone map of the face
poset of the surface into the poset model of the presentation complex**.  Monotonicity is what
makes it a cellular map, and it is the only thing the chamber construction asks of an attaching
map.

The marking is forced by the geometry:

* a boundary vertex and a boundary edge go to the cell of the subdivided rose carrying the same
  letter of the word (this is what makes the boundary of the polygon read the word);
* the collar is the attaching circle of the two-cell of the relator `j₀`: the collar vertex and
  the collar edge at the position `p` go to the corresponding point of that circle;
* the triangles of the collar are degenerate: they go to the one-cell of the rose carrying the
  letter, and so do the two diagonals;
* the centre, the radii and the triangles of the fan go to the two-cell of the relator `j₀`.

`FiniteChains.Davis.surfAtt` is the resulting attaching map `NeSpx (cmpRel …) →o PresPos w`.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel Cell

universe u

section Label

variable {α J : Type u} {w : J → List (α × Bool)} {j₀ : J}
  {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι}
  {vlab : κ → Rose α} {elb : ι → Rose α}

/-! ### The position arithmetic -/

theorem fin_succ_val (p : Fin M) : (p + 1).val = (p.val + 1) % M := by
  grind

/-! ### The circle of the relator -/

variable (p : Fin M)

variable (w j₀) in
/-- The point of the attaching circle of the relator `j₀` carried by the collar vertex at the
position `p`. -/
def cVtx :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cor else CPos.cmid)

variable (w j₀) in
/-- The point of the attaching circle of the relator `j₀` carried by the collar edge at the
position `p`. -/
def cEdg :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cedgL else CPos.cedgR)

variable (hM : M = 2 * (w j₀).length)

include hM

variable (p : Fin M)

omit [NeZero M] in
theorem half_lt : p.val / 2 < (w j₀).length := by
  omega

omit [NeZero M] in
theorem aFun_cVtx : aFun w (cVtx w j₀ p) = vertLab (w j₀) p.val := by
  obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by omega)
  by_cases h : p.val % 2 = 0
  · simp_all [cVtx, if_pos, aFun_pt_cor, vertLab_of_even]
  · rw [cVtx, if_neg h, aFun_pt_cmid_of_get w hq, vertLab_of_odd (by omega) hq]

omit [NeZero M] in
theorem aFun_cEdg : aFun w (cEdg w j₀ p) = edgeLab (w j₀) p.val := by
  obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by omega)
  by_cases h : p.val % 2 = 0
  · rw [cEdg, if_pos h, aFun_pt_cedgL_of_get w hq, edgeLab_eq hq, if_pos h]
  · rw [cEdg, if_neg h, aFun_pt_cedgR_of_get w hq, edgeLab_eq hq, if_neg h]

omit [NeZero M] in
theorem cVtx_le_cEdg : cVtx w j₀ p ≤ cEdg w j₀ p := by
  by_cases h : p.val % 2 = 0
  · rw [cVtx, cEdg, if_pos h, if_pos h]
    solve_by_elim [TCirc.cor_le_cedgL, half_lt]
  · rw [cVtx, cEdg, if_neg h, if_neg h]
    solve_by_elim [TCirc.cmid_le_cedgR, half_lt]

theorem cVtx_succ_le_cEdg : cVtx w j₀ (p + 1) ≤ cEdg w j₀ p := by
  have hsucc := fin_succ_val p
  by_cases h : p.val % 2 = 0
  · -- the next position is the midpoint of the same letter
    have hlt1 : p.val + 1 < M := by omega
    have hval : (p + 1).val = p.val + 1 := by simp_all [hsucc, Nat.mod_eq_of_lt]
    have hhalf : (p + 1).val / 2 = p.val / 2 := by omega
    rw [cVtx, cEdg, if_neg (by omega), if_pos h, hhalf]
    solve_by_elim [TCirc.cmid_le_cedgL, half_lt]
  · -- the next position is the corner in front of the next letter
    rw [cVtx, cEdg, if_neg h]
    rcases Nat.lt_or_ge (p.val + 1) M with hlt1 | hge
    · have hval : (p + 1).val = p.val + 1 := by simp_all [hsucc, Nat.mod_eq_of_lt]
      have hhalf : (p + 1).val / 2 = p.val / 2 + 1 := by omega
      have hcs : TCirc.csucc w j₀ (p.val / 2) = p.val / 2 + 1 := by
        rw [TCirc.csucc, Nat.mod_eq_of_lt (by omega)]
      rw [if_pos (by omega), hhalf, ← hcs]
      solve_by_elim [TCirc.cor_csucc_le_cedgR, half_lt]
    · have hval : (p + 1).val = 0 := by
        rw [hsucc, show p.val + 1 = M by omega, Nat.mod_self]
      have hhalf : (p + 1).val / 2 = 0 := by simp [hval]
      have hcs : TCirc.csucc w j₀ (p.val / 2) = 0 := by
        rw [TCirc.csucc, show p.val / 2 + 1 = (w j₀).length by omega, Nat.mod_self]
      rw [if_pos (by simp [hval]), hhalf, ← hcs]
      solve_by_elim [TCirc.cor_csucc_le_cedgR, half_lt]

/-! ### The labels of the boundary -/

variable (p : Fin M)

omit [NeZero M] in
theorem vertLab_le_edgeLab' :
    vertLab (w j₀) p.val ≤ edgeLab (w j₀) p.val :=
  vertLab_le_edgeLab (by omega)

theorem vertLab_succ_le_edgeLab' :
    vertLab (w j₀) (p + 1).val ≤ edgeLab (w j₀) p.val := by
  have hsucc := fin_succ_val p
  rcases Nat.lt_or_ge (p.val + 1) M with hlt1 | hge
  · have hval : (p + 1).val = p.val + 1 := by simp_all [hsucc, Nat.mod_eq_of_lt]
    rw [hval]
    exact vertLab_succ_le_edgeLab (by omega)
  · have hval : (p + 1).val = 0 := by
      rw [hsucc, show p.val + 1 = M by omega, Nat.mod_self]
    rw [hval, vertLab_of_even rfl]
    exact base_le_edgeLab (by omega)

/-! ### The marking -/

variable (w j₀ vc ec vlab elb) in
/-- **The marking of the cells of the surface** by the cells of the model of the presentation
complex. -/
def gLab : Cell κ ι M → PresPos w
  | vtx v => iRose w (vlab v)
  | bed e => iRose w (elb e)
  | cvx p => iCirc w (cVtx w j₀ p)
  | ced p => iCirc w (cEdg w j₀ p)
  | dia p => iRose w (vlab (vc p))
  | gdi p => iRose w (elb (ec p))
  | tr1 p => iRose w (elb (ec p))
  | tr2 p => iRose w (elb (ec p))
  | ctr => apexOf w j₀
  | rad _ => apexOf w j₀
  | inn _ => apexOf w j₀

variable (hvlab : ∀ p : Fin M, vlab (vc p) = vertLab (w j₀) p.val)
  (helb : ∀ p : Fin M, elb (ec p) = edgeLab (w j₀) p.val)

include hvlab helb

/-! ### The marking is monotone -/

variable (p : Fin M)

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab helb in
theorem iCirc_cVtx_le_apex : iCirc w (cVtx w j₀ p) ≤ apexOf w j₀ :=
  iCirc_le_apexOf w _ (half_lt hM p)

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab helb in
theorem iCirc_cEdg_le_apex : iCirc w (cEdg w j₀ p) ≤ apexOf w j₀ :=
  iCirc_le_apexOf w _ (half_lt hM p)

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] helb in
theorem iCirc_cVtx_le_dia :
    iCirc w (cVtx w j₀ p) ≤ iRose w (vlab (vc p)) := by
  grind [aFun_cVtx, iCirc_le_iRose_aFun]

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab in
theorem iCirc_cEdg_le_bed :
    iCirc w (cEdg w j₀ p) ≤ iRose w (elb (ec p)) := by
  grind [aFun_cEdg, iCirc_le_iRose_aFun]

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab in
theorem iCirc_cVtx_le_bed :
    iCirc w (cVtx w j₀ p) ≤ iRose w (elb (ec p)) := by
  refine le_trans (iCirc_le_iRose_aFun w _) ((iRose_monotone w) ?_)
  simp_all [aFun_cVtx, vertLab_le_edgeLab']

omit [DecidableEq κ] [DecidableEq ι] hvlab in
theorem iCirc_cVtx_succ_le_bed :
    iCirc w (cVtx w j₀ (p + 1)) ≤ iRose w (elb (ec p)) := by
  refine le_trans (iCirc_le_iRose_aFun w _) ((iRose_monotone w) ?_)
  simp_all [aFun_cVtx, vertLab_succ_le_edgeLab']

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] in
theorem vlab_le_elb : iRose w (vlab (vc p)) ≤ iRose w (elb (ec p)) := by
  rw [hvlab p, helb p]; exact vertLab_le_edgeLab' hM p

omit [DecidableEq κ] [DecidableEq ι] in
theorem vlab_succ_le_elb :
    iRose w (vlab (vc (p + 1))) ≤ iRose w (elb (ec p)) := by
  rw [hvlab _, helb p]; exact vertLab_succ_le_edgeLab' hM p

omit [DecidableEq κ] [DecidableEq ι] in
/-- **The marking is monotone on strict faces.** -/
theorem gLab_le_of_plt {x y : Cell κ ι M} (h : plt vc ec x y) :
    gLab w j₀ vc ec vlab elb x ≤ gLab w j₀ vc ec vlab elb y := by
  cases x with
  | vtx v =>
      cases y with
      | bed e =>
          obtain ⟨i, hi, hv⟩ := h
          rw [← hi]
          rcases hv with rfl | rfl
          · apply vlab_le_elb <;> assumption
          · apply vlab_succ_le_elb <;> assumption
      | dia p =>
          have hv : vc p = v := h
          aesop
      | gdi p =>
          rw [← h]; exact vlab_le_elb hM hvlab helb p
      | tr1 p =>
          rcases h with hv | hv
          · rw [← hv]; apply vlab_le_elb <;> assumption
          · rw [← hv]; apply vlab_succ_le_elb <;> assumption
      | tr2 p =>
          rw [← h]; exact vlab_le_elb hM hvlab helb p
      | _ => simp_all [plt]
  | cvx q =>
      cases y with
      | ced r =>
          rcases h with rfl | rfl
          · solve_by_elim [iCirc_monotone, cVtx_le_cEdg]
          · solve_by_elim [iCirc_monotone, cVtx_succ_le_cEdg]
      | dia r =>
          rw [h]; exact iCirc_cVtx_le_dia hM hvlab r
      | gdi r =>
          rw [h]; exact iCirc_cVtx_succ_le_bed hM helb r
      | rad r =>
          exact iCirc_cVtx_le_apex hM q
      | tr1 p =>
          rw [h]; exact iCirc_cVtx_succ_le_bed hM helb p
      | tr2 p =>
          rcases h with rfl | rfl
          · apply iCirc_cVtx_le_bed <;> assumption
          · apply iCirc_cVtx_succ_le_bed <;> assumption
      | inn p =>
          exact iCirc_cVtx_le_apex hM q
      | _ => simp_all [plt]
  | ctr =>
      cases y with
      | rad p => exact le_refl _
      | inn p => exact le_refl _
      | _ => simp [plt] at h
  | bed e =>
      cases y with
      | tr1 p =>
          have he : e = ec p := h
          aesop
      | _ => simp_all [plt]
  | ced r =>
      cases y with
      | tr2 p =>
          rw [h]; exact iCirc_cEdg_le_bed hM helb p
      | inn p =>
          exact iCirc_cEdg_le_apex hM r
      | _ => simp_all [plt]
  | dia r =>
      cases y with
      | tr1 p =>
          rw [h]; exact vlab_succ_le_elb hM hvlab helb p
      | tr2 p =>
          rw [h]; exact vlab_le_elb hM hvlab helb p
      | _ => simp_all [plt]
  | gdi r =>
      cases y with
      | tr1 p =>
          have hr : r = p := h
          aesop
      | tr2 p =>
          have hr : r = p := h
          aesop
      | _ => simp_all [plt]
  | rad r =>
      cases y with
      | inn p => exact le_refl _
      | _ => simp [plt] at h
  | tr1 p => simp_all [plt]
  | tr2 p => simp_all [plt]
  | inn p => simp_all [plt]

variable (hc : Compat vc ec)

/-- **The marking as a monotone map of the face poset of the surface.** -/
def gHom : SCell vc ec hc →o PresPos w where
  toFun x := gLab w j₀ vc ec vlab elb x
  monotone' := by
    rintro x y (rfl | h)
    · exact le_refl _
    · apply gLab_le_of_plt <;> assumption

omit [DecidableEq κ] [DecidableEq ι] in
@[simp] theorem gHom_apply (x : Cell κ ι M) :
    gHom hM hvlab helb hc (toS vc ec hc x) = gLab w j₀ vc ec vlab elb x := rfl

/-- **The attaching map of the surface block**: the marking, read on the chains of the
barycentric subdivision. -/
noncomputable def surfAtt :=
  nerveAtt (gHom hM hvlab helb hc)

end Label

end Davis
end FiniteChains
