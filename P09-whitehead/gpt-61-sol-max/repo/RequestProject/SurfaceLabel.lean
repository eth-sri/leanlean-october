import Mathlib.Tactic

import RequestProject.SurfaceCells
import RequestProject.AttCycle

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

namespace FiniteChains.Davis


open RACG Mirror Comb PresModel Cell


section

variable {α J : Type u} {w : J → List (α × Bool)} {j₀ : J}
  {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι}
  {vlab : κ → Rose α} {elb : ι → Rose α}

/-! ### The position arithmetic -/

theorem fin_succ_val (p : Fin M) : (p + 1).val = (p.val + 1) % M := by grind

/-! ### The circle of the relator -/

variable (w j₀) in
/-- The point of the attaching circle of the relator `j₀` carried by the collar vertex at the
position `p`. -/
def cVtx (p : Fin M)  :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cor else CPos.cmid)

variable (w j₀) in
/-- The point of the attaching circle of the relator `j₀` carried by the collar edge at the
position `p`. -/
def cEdg (p : Fin M)  :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cedgL else CPos.cedgR)

variable (hM : M = 2 * (w j₀).length)

include hM

section
omit [NeZero M]
variable (p : Fin M)
theorem half_lt  : p.val / 2 < (w j₀).length := by
  have := p.isLt
  omega

theorem aFun_cVtx  : aFun w (cVtx w j₀ p) = vertLab (w j₀) p.val := by
  obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by have := p.isLt; omega)
  by_cases h : p.val % 2 = 0
  · simp_all [cVtx]
  · grind [FiniteChains.PresModel.aFun_pt_cmid_of_get, FiniteChains.Davis.vertLab_of_odd, cVtx]

theorem aFun_cEdg  : aFun w (cEdg w j₀ p) = edgeLab (w j₀) p.val := by
  obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by have := p.isLt; omega)
  by_cases h : p.val % 2 = 0
  · classical grind [cEdg, aFun_pt_cedgL_of_get, edgeLab_eq]
  · grind [FiniteChains.PresModel.aFun_pt_cedgR_of_get, FiniteChains.Davis.edgeLab_eq, cEdg]

theorem cVtx_le_cEdg  : cVtx w j₀ p ≤ cEdg w j₀ p := by
  by_cases h : p.val % 2 = 0
  · rw [cVtx, cEdg, if_pos h, if_pos h]
    exact TCirc.cor_le_cedgL w (half_lt hM p)
  · rw [cVtx, cEdg, if_neg h, if_neg h]
    exact TCirc.cmid_le_cedgR w (half_lt hM p)
end

theorem cVtx_succ_le_cEdg (p : Fin M) : cVtx w j₀ (p + 1) ≤ cEdg w j₀ p := by
  
  have hsucc := fin_succ_val p
  by_cases h : p.val % 2 = 0
  · -- the next position is the midpoint of the same letter
    have hlt1 : p.val + 1 < M := by omega
    have hval : (p + 1).val = p.val + 1 := by rw [hsucc, Nat.mod_eq_of_lt hlt1]
    have hodd : (p + 1).val % 2 ≠ 0 := by rw [hval]; omega
    have hhalf : (p + 1).val / 2 = p.val / 2 := by rw [hval]; omega
    rw [cVtx, cEdg, if_neg hodd, if_pos h, hhalf]
    exact TCirc.cmid_le_cedgL w (half_lt hM p)
  · -- the next position is the corner in front of the next letter
    rw [cVtx, cEdg, if_neg h]
    rcases Nat.lt_or_ge (p.val + 1) M with hlt1 | hge
    · have hval : (p + 1).val = p.val + 1 := by rw [hsucc, Nat.mod_eq_of_lt hlt1]
      have heven : (p + 1).val % 2 = 0 := by rw [hval]; omega
      have hhalf : (p + 1).val / 2 = p.val / 2 + 1 := by rw [hval]; omega
      have hcs : TCirc.csucc w j₀ (p.val / 2) = p.val / 2 + 1 := by
        rw [TCirc.csucc, Nat.mod_eq_of_lt (by omega)]
      rw [if_pos heven, hhalf, ← hcs]
      exact TCirc.cor_csucc_le_cedgR w (half_lt hM p)
    · have hval : (p + 1).val = 0 := by
        classical grind [Nat.mod_self]
      have heven : (p + 1).val % 2 = 0 := by rw [hval]
      have hhalf : (p + 1).val / 2 = 0 := by rw [hval]
      have hcs : TCirc.csucc w j₀ (p.val / 2) = 0 := by
        rw [TCirc.csucc, show p.val / 2 + 1 = (w j₀).length by omega, Nat.mod_self]
      rw [if_pos heven, hhalf, ← hcs]
      exact TCirc.cor_csucc_le_cedgR w (half_lt hM p)

/-! ### The labels of the boundary -/

omit [NeZero M] in
theorem vertLab_le_edgeLab' (p : Fin M) :
    vertLab (w j₀) p.val ≤ edgeLab (w j₀) p.val :=
  vertLab_le_edgeLab (by have := p.isLt; omega)

theorem vertLab_succ_le_edgeLab' (p : Fin M) :
    vertLab (w j₀) (p + 1).val ≤ edgeLab (w j₀) p.val := by
  
  have hsucc := fin_succ_val p
  rcases Nat.lt_or_ge (p.val + 1) M with hlt1 | hge
  · classical simp_all [Nat.mod_eq_of_lt, FiniteChains.Davis.vertLab_succ_le_edgeLab]
  · have hval : (p + 1).val = 0 := by
      classical grind [Nat.mod_self]
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

section
omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab helb
theorem iCirc_cVtx_le_apex (p : Fin M) : iCirc w (cVtx w j₀ p) ≤ apexOf w j₀ :=
  iCirc_le_apexOf w _ (half_lt hM p)

theorem iCirc_cEdg_le_apex (p : Fin M) : iCirc w (cEdg w j₀ p) ≤ apexOf w j₀ :=
  iCirc_le_apexOf w _ (half_lt hM p)
end

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] helb in
theorem iCirc_cVtx_le_dia (p : Fin M) :
    iCirc w (cVtx w j₀ p) ≤ iRose w (vlab (vc p)) := by
  classical grind [FiniteChains.Davis.aFun_cVtx, FiniteChains.PresModel.iCirc_le_iRose_aFun]

section
omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab
theorem iCirc_cEdg_le_bed (p : Fin M) :
    iCirc w (cEdg w j₀ p) ≤ iRose w (elb (ec p)) := by
  classical grind [FiniteChains.Davis.aFun_cEdg, FiniteChains.PresModel.iCirc_le_iRose_aFun]

theorem iCirc_cVtx_le_bed (p : Fin M) :
    iCirc w (cVtx w j₀ p) ≤ iRose w (elb (ec p)) := by
  refine le_trans (iCirc_le_iRose_aFun w _) ((iRose_monotone w) ?_)
  rw [aFun_cVtx hM p, helb p]
  exact vertLab_le_edgeLab' hM p
end

omit [DecidableEq κ] [DecidableEq ι] hvlab in
theorem iCirc_cVtx_succ_le_bed (p : Fin M) :
    iCirc w (cVtx w j₀ (p + 1)) ≤ iRose w (elb (ec p)) := by
  refine le_trans (iCirc_le_iRose_aFun w _) ((iRose_monotone w) ?_)
  rw [aFun_cVtx hM (p + 1), helb p]
  exact vertLab_succ_le_edgeLab' hM p

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] in
theorem vlab_le_elb (p : Fin M) : iRose w (vlab (vc p)) ≤ iRose w (elb (ec p)) := by
  refine (iRose_monotone w) ?_
  rw [hvlab p, helb p]
  exact vertLab_le_edgeLab' hM p

omit [DecidableEq κ] [DecidableEq ι] in
theorem vlab_succ_le_elb (p : Fin M) :
    iRose w (vlab (vc (p + 1))) ≤ iRose w (elb (ec p)) := by
  refine (iRose_monotone w) ?_
  rw [hvlab (p + 1), helb p]
  exact vertLab_succ_le_edgeLab' hM p

set_option maxHeartbeats 1000000 in
omit [DecidableEq κ] [DecidableEq ι] in
/-- **The marking is monotone on strict faces.** -/
theorem gLab_le_of_plt {x y : Cell κ ι M} (h : plt vc ec x y) :
    gLab w j₀ vc ec vlab elb x ≤ gLab w j₀ vc ec vlab elb y := by
  classical
  have h₁ (p : Fin M) := (iCirc_monotone w) (cVtx_le_cEdg hM p)
  have h₂ (p : Fin M) := (iCirc_monotone w) (cVtx_succ_le_cEdg hM p)
  cases x <;> cases y <;> simp only [plt, gLab] at h ⊢ <;>
    aesop (config := { enableSimp := false }) (add unsafe apply [le_refl, iCirc_cVtx_le_apex, iCirc_cEdg_le_apex,
      iCirc_cVtx_le_dia, iCirc_cEdg_le_bed, iCirc_cVtx_le_bed,
      iCirc_cVtx_succ_le_bed, vlab_le_elb, vlab_succ_le_elb])

variable (hc : Compat vc ec)

/-- **The marking as a monotone map of the face poset of the surface.** -/
def gHom : SCell vc ec hc →o PresPos w where
  toFun x := gLab w j₀ vc ec vlab elb x
  monotone' := by
    rintro x y (rfl | h)
    · exact le_refl _
    · exact gLab_le_of_plt hM hvlab helb h



/-- **The attaching map of the surface block**: the marking, read on the chains of the
barycentric subdivision. -/
noncomputable def surfAtt  :=
  nerveAtt (gHom hM hvlab helb hc)

end

end FiniteChains.Davis

