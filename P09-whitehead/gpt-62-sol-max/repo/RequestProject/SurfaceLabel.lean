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
  show (p.val + (1 : Fin M).val) % M = (p.val + 1) % M
  simp

/-! ### The circle of the relator -/

variable (w j₀) in
/-- The point of the attaching circle of the relator `j₀` carried by the collar vertex at the
position `p`. -/
def cVtx (p : Fin M) : TCirc w :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cor else CPos.cmid)

variable (w j₀) in
/-- The point of the attaching circle of the relator `j₀` carried by the collar edge at the
position `p`. -/
def cEdg (p : Fin M) : TCirc w :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cedgL else CPos.cedgR)

variable (hM : M = 2 * (w j₀).length)

include hM

omit [NeZero M] in
theorem half_lt (p : Fin M) : p.val / 2 < (w j₀).length := by
  omega

omit [NeZero M] in
theorem aFun_cVtx (p : Fin M) : aFun w (cVtx w j₀ p) = vertLab (w j₀) p.val := by
  obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by omega)
  by_cases h : p.val % 2 = 0
  · rw [cVtx, if_pos h, aFun_pt_cor, vertLab_of_even h]
  · rw [cVtx, if_neg h, aFun_pt_cmid_of_get w hq, vertLab_of_odd (by omega) hq]

omit [NeZero M] in
theorem aFun_cEdg (p : Fin M) : aFun w (cEdg w j₀ p) = edgeLab (w j₀) p.val := by
  obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by omega)
  by_cases h : p.val % 2 = 0
  · rw [cEdg, if_pos h, aFun_pt_cedgL_of_get w hq, edgeLab_eq hq, if_pos h]
  simp_all [cEdg, aFun_pt_cedgR_of_get w hq, edgeLab_eq hq]

omit [NeZero M] in
theorem cVtx_le_cEdg (p : Fin M) : cVtx w j₀ p ≤ cEdg w j₀ p := by
  by_cases h : p.val % 2 = 0
  · rw [cVtx, cEdg, if_pos h, if_pos h]
    exact TCirc.cor_le_cedgL w (half_lt hM p)
  · rw [cVtx, cEdg, if_neg h, if_neg h]
    exact TCirc.cmid_le_cedgR w (half_lt hM p)

theorem cVtx_succ_le_cEdg (p : Fin M) : cVtx w j₀ (p + 1) ≤ cEdg w j₀ p := by
  have hp := p.isLt
  have hmod : (p.val + 1) % M % 2 = (p.val + 1) % 2 := by
    exact Nat.mod_mod_of_dvd _ (hM.symm ▸ dvd_mul_right 2 _)
  simp only [cVtx, cEdg, fin_succ_val, hmod]
  by_cases h : p.val % 2 = 0
  · rw [if_neg (by omega), if_pos h, Nat.mod_eq_of_lt (by omega),
      show (p.val + 1) / 2 = p.val / 2 by omega]
    exact TCirc.cmid_le_cedgL w (half_lt hM p)
  · rw [if_pos (by omega), if_neg h,
      show (p.val + 1) % M / 2 = TCirc.csucc w j₀ (p.val / 2) by
        rw [congrArg (fun m => (p.val + 1) % m) hM, Nat.mod_mul_right_div_self, TCirc.csucc,
          show (p.val + 1) / 2 = p.val / 2 + 1 by omega]]
    exact TCirc.cor_csucc_le_cedgR w (half_lt hM p)

omit [NeZero M] in
theorem vertLab_le_edgeLab' (p : Fin M) :
    vertLab (w j₀) p.val ≤ edgeLab (w j₀) p.val := by
  rw [← aFun_cVtx hM, ← aFun_cEdg hM]
  exact aFun_monotone w (cVtx_le_cEdg hM p)

theorem vertLab_succ_le_edgeLab' (p : Fin M) :
    vertLab (w j₀) (p + 1).val ≤ edgeLab (w j₀) p.val := by
  rw [← aFun_cVtx hM, ← aFun_cEdg hM]
  exact aFun_monotone w (cVtx_succ_le_cEdg hM p)

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

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab helb in
theorem iCirc_cVtx_le_apex (p : Fin M) : iCirc w (cVtx w j₀ p) ≤ apexOf w j₀ :=
  iCirc_le_apexOf w _ (half_lt hM p)

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab helb in
theorem iCirc_cEdg_le_apex (p : Fin M) : iCirc w (cEdg w j₀ p) ≤ apexOf w j₀ :=
  iCirc_le_apexOf w _ (half_lt hM p)

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] helb in
theorem iCirc_cVtx_le_dia (p : Fin M) :
    iCirc w (cVtx w j₀ p) ≤ iRose w (vlab (vc p)) := by
  rw [hvlab p, ← aFun_cVtx hM p]
  exact iCirc_le_iRose_aFun w _

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab in
theorem iCirc_cEdg_le_bed (p : Fin M) :
    iCirc w (cEdg w j₀ p) ≤ iRose w (elb (ec p)) := by
  rw [helb p, ← aFun_cEdg hM p]
  exact iCirc_le_iRose_aFun w _

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab in
theorem iCirc_cVtx_le_bed (p : Fin M) :
    iCirc w (cVtx w j₀ p) ≤ iRose w (elb (ec p)) := by
  refine le_trans (iCirc_le_iRose_aFun w _) ((iRose_monotone w) ?_)
  rw [aFun_cVtx hM p, helb p]
  exact vertLab_le_edgeLab' hM p

omit [DecidableEq κ] [DecidableEq ι] hvlab in
theorem iCirc_cVtx_succ_le_bed (p : Fin M) :
    iCirc w (cVtx w j₀ (p + 1)) ≤ iRose w (elb (ec p)) := by
  refine le_trans (iCirc_le_iRose_aFun w _) ((iRose_monotone w) ?_)
  rw [aFun_cVtx hM (p + 1), helb p]
  exact vertLab_succ_le_edgeLab' hM p

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] in
theorem vlab_le_elb (p : Fin M) : iRose w (vlab (vc p)) ≤ iRose w (elb (ec p)) := by
  rw [hvlab p, helb p]
  exact vertLab_le_edgeLab' hM p

omit [DecidableEq κ] [DecidableEq ι] in
theorem vlab_succ_le_elb (p : Fin M) :
    iRose w (vlab (vc (p + 1))) ≤ iRose w (elb (ec p)) := by
  refine (iRose_monotone w) ?_
  rw [hvlab (p + 1), helb p]
  exact vertLab_succ_le_edgeLab' hM p

omit [DecidableEq κ] [DecidableEq ι] in
/-- **The marking is monotone on strict faces.** -/
theorem gLab_le_of_plt {x y : Cell κ ι M} (h : plt vc ec x y) :
    gLab w j₀ vc ec vlab elb x ≤ gLab w j₀ vc ec vlab elb y := by
  have hvl := vlab_le_elb hM hvlab helb
  have hvs := vlab_succ_le_elb hM hvlab helb
  have hd := iCirc_cVtx_le_dia hM hvlab
  have hb := iCirc_cVtx_le_bed hM helb
  have hbs := iCirc_cVtx_succ_le_bed hM helb
  have he := iCirc_cEdg_le_bed hM helb
  have hva := iCirc_cVtx_le_apex hM
  have hea := iCirc_cEdg_le_apex hM
  have hce p := iCirc_monotone w (cVtx_le_cEdg hM p)
  have hces p := iCirc_monotone w (cVtx_succ_le_cEdg hM p)
  cases x <;> cases y <;> simp only [plt, gLab] at h ⊢ <;>
    grind only [le_refl]

variable (hc : Compat vc ec)

/-- **The marking as a monotone map of the face poset of the surface.** -/
def gHom : SCell vc ec hc →o PresPos w where
  toFun x := gLab w j₀ vc ec vlab elb x
  monotone' := by
    rintro x y (rfl | h)
    · aesop
    · exact gLab_le_of_plt hM hvlab helb h


/-- **The attaching map of the surface block**: the marking, read on the chains of the
barycentric subdivision. -/
noncomputable def surfAtt : NeSpx (cmpRel (SCell vc ec hc)) →o PresPos w :=
  nerveAtt (gHom hM hvlab helb hc)

end Label

end Davis
end FiniteChains
