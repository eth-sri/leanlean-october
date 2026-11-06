module

public import RequestProject.SurfaceCells
public import RequestProject.AttCycle

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Davis

open RACG Mirror Comb Cell PresModel

universe u

variable {α J : Type u} {w : J → List (α × Bool)} {j₀ : J}
  {κ ι : Type u} {M : ℕ}
  {vc : Fin M → κ} {ec : Fin M → ι}
  {vlab : κ → Rose α} {elb : ι → Rose α}

variable (w j₀) in
def cVtx (p : Fin M) : TCirc w :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cor else CPos.cmid)

variable (w j₀) in
def cEdg (p : Fin M) : TCirc w :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cedgL else CPos.cedgR)

variable (w j₀ vc ec vlab elb) in
def gLab : Cell κ ι M → PresPos w
  | vtx v => iRose w (vlab v)
  | bed e => iRose w (elb e)
  | cvx p => iCirc w (cVtx w j₀ p)
  | ced p => iCirc w (cEdg w j₀ p)
  | dia p => iRose w (vlab (vc p))
  | gdi p | tr1 p | tr2 p => iRose w (elb (ec p))
  | ctr | rad _ | inn _ => apexOf w j₀

theorem fin_succ_val [NeZero M] (p : Fin M) : (p + 1).val = (p.val + 1) % M :=
  Nat.add_mod_mod p.val 1 M

variable (hM : M = 2 * (w j₀).length)
  (hvlab : ∀ p : Fin M, vlab (vc p) = vertLab (w j₀) p.val)
  (helb : ∀ p : Fin M, elb (ec p) = edgeLab (w j₀) p.val)
  [NeZero M] (hc : Compat vc ec)

def gHom : SCell vc ec hc →o PresPos w where
  toFun x := gLab w j₀ vc ec vlab elb x
  monotone' := by
        have hhalf (p : Fin M) : p.val / 2 < (w j₀).length := by have := p.isLt; omega
        have haV (p : Fin M) : aFun w (cVtx w j₀ p) = vertLab (w j₀) p.val := by
          obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by have := p.isLt; omega)
          by_cases h : p.val % 2 = 0
          · rw [cVtx, if_pos h, aFun_pt_cor, vertLab_of_even h]
          · rw [cVtx, if_neg h, aFun_pt_cmid_of_get w hq, vertLab_of_odd (by omega) hq]
        have haE (p : Fin M) : aFun w (cEdg w j₀ p) = edgeLab (w j₀) p.val := by
          obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by have := p.isLt; omega)
          by_cases h : p.val % 2 = 0 <;> simp [cEdg, h, aFun_pt_cedgL_of_get w hq,
            aFun_pt_cedgR_of_get w hq, edgeLab_eq hq]
        have hvle (p : Fin M) : vertLab (w j₀) p.val ≤ edgeLab (w j₀) p.val :=
          vertLab_le_edgeLab (by have := p.isLt; omega)
        have hvsle (p : Fin M) : vertLab (w j₀) (p + 1).val ≤ edgeLab (w j₀) p.val := by
          have := p.isLt; rw [fin_succ_val p]
          rcases Nat.lt_or_ge (p.val + 1) M with hlt1 | hge
          · rw [Nat.mod_eq_of_lt hlt1]; exact vertLab_succ_le_edgeLab (by omega)
          · rw [show p.val + 1 = M by omega, Nat.mod_self, vertLab_of_even rfl]
            exact base_le_edgeLab (by omega)
        have hv_elb (p : Fin M) : iRose w (vlab (vc p)) ≤ iRose w (elb (ec p)) :=
          (iRose_monotone w) (by rw [hvlab p, helb p]; exact hvle p)
        have hvs_elb (p : Fin M) : iRose w (vlab (vc (p + 1))) ≤ iRose w (elb (ec p)) :=
          (iRose_monotone w) (by rw [hvlab (p + 1), helb p]; exact hvsle p)
        have hcV_bed (p : Fin M) : iCirc w (cVtx w j₀ p) ≤ iRose w (elb (ec p)) :=
          (iCirc_le_iRose_aFun w _).trans ((iRose_monotone w) (by rw [haV p, helb p]; exact hvle p))
        have hcVs_bed (p : Fin M) : iCirc w (cVtx w j₀ (p + 1)) ≤ iRose w (elb (ec p)) :=
          (iCirc_le_iRose_aFun w _).trans ((iRose_monotone w) (by rw [haV (p + 1), helb p]; exact hvsle p))
        rintro x y (rfl | h)
        · exact le_rfl
        · cases x with
          | vtx v =>
              cases y with
              | bed e => rcases h with ⟨i, rfl, rfl | rfl⟩; exacts [hv_elb i, hvs_elb i]
              | dia p => cases h; exact le_rfl
              | gdi p | tr2 p => cases h; exact hv_elb p
              | tr1 p => rcases h with rfl | rfl; exacts [hv_elb p, hvs_elb p]
              | _ => simp [plt] at h
          | cvx q =>
              cases y with
              | ced r =>
                  rcases h with rfl | rfl
                  · refine (iCirc_monotone w) ?_
                    by_cases h : q.val % 2 = 0 <;> simp [cVtx, cEdg, h]
                    exacts [TCirc.cor_le_cedgL w (hhalf q), TCirc.cmid_le_cedgR w (hhalf q)]
                  · refine (iCirc_monotone w) ?_
                    have hlt := r.isLt; have hsucc := fin_succ_val r
                    by_cases h : r.val % 2 = 0
                    · have hval : (r + 1).val = r.val + 1 := by rw [hsucc, Nat.mod_eq_of_lt (by omega)]
                      rw [cVtx, cEdg, if_neg (by rw [hval]; omega), if_pos h, show (r + 1).val / 2 = r.val / 2 by omega]
                      exact TCirc.cmid_le_cedgL w (hhalf r)
                    · rw [cVtx, cEdg, if_neg h]
                      rcases Nat.lt_or_ge (r.val + 1) M with hlt1 | hge
                      · have hval : (r + 1).val = r.val + 1 := by rw [hsucc, Nat.mod_eq_of_lt hlt1]
                        rw [if_pos (by omega), ← show TCirc.csucc w j₀ (r.val / 2) = (r + 1).val / 2 by
                          rw [TCirc.csucc, Nat.mod_eq_of_lt (by omega)]; omega]
                        exact TCirc.cor_csucc_le_cedgR w (hhalf r)
                      · have hval : (r + 1).val = 0 := by rw [hsucc, show r.val + 1 = M by omega, Nat.mod_self]
                        rw [hval, if_pos rfl, Nat.zero_div, ← show TCirc.csucc w j₀ (r.val / 2) = 0 by
                          rw [TCirc.csucc, show r.val / 2 + 1 = (w j₀).length by omega, Nat.mod_self]]
                        exact TCirc.cor_csucc_le_cedgR w (hhalf r)
              | dia r => cases h; dsimp [gLab]; rw [hvlab q, ← haV q]; exact iCirc_le_iRose_aFun w _
              | gdi r | tr1 r => cases h; exact hcVs_bed r
              | rad r | inn r => exact iCirc_le_apexOf w _ (hhalf q)
              | tr2 p => rcases h with rfl | rfl; exacts [hcV_bed q, hcVs_bed p]
              | _ => simp [plt] at h
          | ctr => cases y <;> first | exact le_rfl | simp [plt] at h
          | bed e => cases y <;> first | (cases h; exact le_rfl) | simp [plt] at h
          | ced r =>
              cases y with
              | tr2 p => cases h; dsimp [gLab]; rw [helb r, ← haE r]; exact iCirc_le_iRose_aFun w _
              | inn p => exact iCirc_le_apexOf w _ (hhalf r)
              | _ => simp [plt] at h
          | dia r =>
              cases y with
              | tr1 p => cases h; exact hvs_elb p
              | tr2 p => cases h; exact hv_elb r
              | _ => simp [plt] at h
          | gdi r =>
              cases y with
              | tr1 p | tr2 p => cases h; exact le_rfl
              | _ => simp [plt] at h
          | rad r =>
              cases y with
              | inn p => exact le_rfl
              | _ => simp [plt] at h
          | tr1 p | tr2 p | inn p => simp [plt] at h

variable [DecidableEq κ] [DecidableEq ι]

noncomputable def surfAtt : NeSpx (cmpRel (SCell vc ec hc)) →o PresPos w :=
  nerveAtt (gHom hM hvlab helb hc)
