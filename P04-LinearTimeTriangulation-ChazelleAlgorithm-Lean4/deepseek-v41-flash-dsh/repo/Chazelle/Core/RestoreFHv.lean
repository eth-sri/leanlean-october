module

public import Chazelle.Golf

public import Chazelle.Core.RestoreFTest
public import Chazelle.Core.RestoreTIntKey
public import Chazelle.Core.RestoreTDisp
public import Chazelle.Core.ShootCutShPt

/-!
# WP-E, the search on the RAM (`FindOK`), part 5: the height vertex of a walk vertex

`fHv a`: `81062 :=` the index of a vertex of `Q` at the height of the walk vertex `(e, 0)` of the
host model, `e` in register `a` (`81064` is scratch).  For a chain model the primitive `ptKey`
loads the ordinate record of the walk vertex (a point of the chain lies strictly inside the box,
so the record names a vertex); for the interior model the index is `iIdx bit n e`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim ShootCut

/-- The reversed index `n - 1 - e` of the interior walk. -/
def hvRev (a : ℕ) : Stmt := Stmt.block [.subN 81062 81020 81012, .subN 81062 81062 a]

/-- The interior model: `iIdx bit n e`. -/
def hvInt (a : ℕ) : Stmt :=
  .seq (Stmt.block [.addN 81064 81000 81012, .loadN 81064 81064])
    (.ifLtN 81012 81064 (hvRev a) (.ifLtN 81011 81064 (Stmt.block [.copyN 81062 a]) (hvRev a)))

/-- A chain model: the ordinate record of `ptKey`. -/
def hvChainL (a : ℕ) : List Instr := [.addN 50200 81000 81012, .copyN 50201 a, .constN 50202 0]

def hvChain (a : ℕ) : Stmt :=
  .seq (Stmt.block (hvChainL a)) (.seq ptKey (Stmt.block [.copyN 81062 50215]))

/-- **The height vertex** of the walk vertex in register `a`. -/
def fHv (a : ℕ) : Stmt :=
  .seq (Stmt.block [.loadN 81064 81000]) (.ifLtN 81011 81064 (hvInt a) (hvChain a))

/-- The cost bound of `fHv`. -/
def hvK : ℕ := 15820

variable {E : FEnv} {c₀ c : Config}

theorem fscr_5 {r : ℕ} (h1 : 50000 ≤ r) (h2 : r < 60000) : FScr r := by
  refine Or.inr ?_
  have : bandOf r = bLocate := by unfold bandOf bLocate; omega
  rw [this]; decide

theorem pos_vtx0 (M : Model) (Q : Polygon) (e : ℕ) : M.pos Q ⟨e, 0⟩ = M.wa e := by
  show Geometry.lerp (M.wa e) (M.wb e) (M.param Q ⟨e, 0⟩) = M.wa e
  Ξ show M.param Q ⟨e, 0⟩ = 0 from rfl, Geometry.lerp_zero

/-- **The height vertex** as a run step of the search. -/
theorem fHv_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {a : ℕ} (ha1 : 80000 ≤ a) (ha2 : a < 90000) (ha62 : a ≠ 81062) (ha64 : a ≠ 81064)
    (hea : c.nreg a < E.M.W.n)
    (hset : ∀ C : Chain, E.M = chainModel C → E.M.pos (Qof E.P) ⟨c.nreg a, 0⟩ ∈ C.set)
    (hroom : c.nreg ALLOC + hvK ≤ E.W) :
    FRS B E.P E.W c₀ (fHv a) c hvK (fun c' => c'.nreg 81062 < E.P.n ∧
      ((Qof E.P).vtx (c'.nreg 81062)).2 = (E.M.pos (Qof E.P) ⟨c.nreg a, 0⟩).2 ∧
      ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81062 → q ≠ 81064 → c'.nreg q = c.nreg q) := by
  have hag := hI.agree hE
  have hA := hI.allocA hE
  obtain ⟨hMD, hwf⟩ := Gran.desc_agree' hE.hwf hE.hMD hag
  have hwfc := hwf.mono hA
  have hn3 := hE.hG.1.1
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81000 = E.MD ∧ c'.nreg 81011 = 0 ∧
      c'.nreg 81012 = 1 ∧ c'.nreg 81020 = E.P.n := fun c' hI' =>
    ⟨by rw [hI'.hin _ (by unfold FFix; omega), hE.i0],
      by rw [hI'.hin _ (by unfold FFix; omega), hE.k0],
      by rw [hI'.hin _ (by unfold FFix; omega), hE.k1],
      by rw [hI'.hin _ (by unfold FFix; omega), hE.pn]⟩
  obtain ⟨i0, k0, k1, pn⟩ := fx c hI
  have hAW : c.nreg ALLOC ≤ E.W := hI.hw.1 ALLOC
  have hMD6 : E.MD + 6 ≤ c.nreg ALLOC := le_trans hwf.1 hA
  have ok0 : okB E.W c.nmem [.loadN 81064 81000] c.nreg := by
    simp only [okB, okI]; exact ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), trivial⟩
  refine (FRS.seq (K₂ := 15819) (FRS.block hB _ hI ok0) (fun c₁ hI₁ hA₁' h₁ => ?_)).mono
    (by unfold hvK; simp) (fun _ h => h)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.loadN 81064 81000] c.nreg q := fun q => by rw [h₁]
  have m₁ : c₁.nmem = c.nmem := by rw [h₁]
  have r64 : c₁.nreg 81064 = c.nmem E.MD := by rw [e₁]; simp [regB, regI, upd, i0]
  have f₁ : ∀ q, q ≠ 81064 → c₁.nreg q = c.nreg q := fun q hq => by
    rw [e₁]; simp [regB, regI, upd, hq]
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by unfold ALLOC; omega)
  obtain ⟨j0, j11, j12, j20⟩ := fx c₁ hI₁
  have hfin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → q ≠ 81062 → q ≠ 81064 →
      c'.nreg q = c₁.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81062 → q ≠ 81064 → c'.nreg q = c.nreg q :=
    fun c' h q h1 h2 h3 h4 => (h q h1 h2 h3 h4).trans (f₁ q h4)
  have ea : c₁.nreg a = c.nreg a := f₁ a ha64
  rcases hMD with ⟨h0, H, C, hC, hM⟩ | ⟨h1, hbit, hM⟩
  · -- a chain model: `ptKey`
    refine (FRS.ifF (show ¬ c₁.nreg 81011 < c₁.nreg 81064 by rw [j11, r64, h0]; omega) ?_).mono (K := 15819) (by omega) (fun _ h => h)
    have ok : okB E.W c₁.nmem (hvChainL a) c₁.nreg := by
      simp only [hvChainL, okB, okI]
      exact ⟨⟨fscr_5 (by norm_num) (by norm_num) |> Or.inl, by rw [j0, j12]; omega⟩,
        Or.inl (fscr_5 (by norm_num) (by norm_num)),
        ⟨Or.inl (fscr_5 (by norm_num) (by norm_num)), by omega⟩, trivial⟩
    refine FRS.seq (K₂ := 15814) (FRS.block hB _ hI₁ ok) (fun c₂ hI₂ _ h₂ => ?_)
    have e₂ : ∀ q, c₂.nreg q = regB c₁.nmem (hvChainL a) c₁.nreg q := fun q => by rw [h₂]
    have m₂ : c₂.nmem = c.nmem := by rw [h₂]; exact m₁
    have s00 : c₂.nreg 50200 = E.MD + 1 := by
      rw [e₂]; simp [hvChainL, regB, regI, upd, j0, j12]
    have s01 : c₂.nreg 50201 = c.nreg a := by
      rw [e₂, ← ea]
      simp [hvChainL, regB, regI, upd, show a ≠ 50200 by omega]
    have s02 : c₂.nreg 50202 = 0 := by rw [e₂]; simp [hvChainL, regB, regI, upd]
    have f₂ : ∀ q, 80000 ≤ q → c₂.nreg q = c₁.nreg q := fun q hq => by
      rw [e₂]
      refine regB_other _ _ _ (fun i hi => ?_)
      simp only [hvChainL, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> simp only [dstI] <;> omega
    have hA₂ : c₂.nreg ALLOC = c.nreg ALLOC := by
      rw [e₂, regB_other _ _ _ (fun i hi => ?_), hA₁]
      simp only [hvChainL, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> simp only [dstI] <;> unfold ALLOC <;> omega
    -- the preconditions of `ptKey`
    have hC₂ : ChainDescAt c₂.nmem (c₂.nreg 50200) (Qof E.P) H C := by rw [m₂, s00]; exact hC
    have hwf₂ : ChainWF E.P (c₂.nreg ALLOC) c₂.nmem (c₂.nreg 50200) := by
      rw [m₂, s00, hA₂]; exact hwfc.2 h0
    have h0' : E.m₀ E.MD = 0 := by rw [← hag _ (by have := hE.hwf.1; omega)]; exact h0
    obtain ⟨H₀, C₀, hC₀, -⟩ : ∃ H₀ C₀, ChainDescAt E.m₀ (E.MD + 1) (Qof E.P) H₀ C₀ ∧
        E.M = chainModel C₀ := by
      rcases hE.hMD with ⟨-, H₀, C₀, hC₀, hM₀⟩ | ⟨h1, -, -⟩
      · exact ⟨H₀, C₀, hC₀, hM₀⟩
      · rw [h0'] at h1; exact absurd h1 (by norm_num)
    have hreg₀ := hE.hreg h0' H₀ C₀ hC₀
    obtain ⟨-, -, hEb, -⟩ := (hE.hwf.2 h0').2 H₀ C₀ hC₀
    have hH₀ : HostAt c.nmem (E.m₀ (E.MD + 1)) H₀ := Gran.hostAt_agree' hC₀.1 hEb hag
    have e1 : c.nmem (E.MD + 1) = E.m₀ (E.MD + 1) := hag _ (by have := hE.hwf.1; omega)
    have hregH : ∀ H', HostAt c₂.nmem (c₂.nmem (c₂.nreg 50200)) H' → HostRegular E.P.n H' := by
      intro H' hH'
      rw [m₂, s00, e1] at hH'
      have : H₀ = H' := NFLoc.hostAt_unique hH₀ hH'
      subst this
      rw [show (Qof E.P).n = E.P.n from shear_n _ _] at hreg₀
      exact hreg₀
    have hWn : (chainModel C).W.n = E.M.W.n := by rw [hM]
    have hpos : (chainModel C).pos (Qof E.P) ⟨c.nreg a, 0⟩ ∈ C.set := by
      rw [← hM]; exact hset C hM
    have hpre : PrimPre PtIn E.P E.W c₂ := ⟨hE.hG, hE.hWh, hwf₂, H, C, hC₂,
      by rw [s01, hWn]; exact hea,
      by rw [s01, s02]; exact ⟨le_of_eq rfl, by show (0 : ℝ) < 1; norm_num, Nat.zero_le _⟩,
      Or.inl s02, hregH⟩
    obtain ⟨c₃, k₃, ex₃, hk₃, post₃, hfr₃⟩ := ptKey_meets E.P E.W c₂ hI₂.hw hpre
      (by rw [hA₂]; unfold hvK at hroom; show _ + 15800 ≤ _; omega)
    replace hk₃ : k₃ ≤ 15800 := hk₃
    obtain ⟨pr, -⟩ := post₃ H C hC₂
    rw [s01, s02] at pr
    obtain ⟨-, hy, -⟩ := pr
    have hyR : |((chainModel C).pos (Qof E.P) ⟨c.nreg a, 0⟩).2| < C.radius :=
      lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hpos).2 C.coordBound_lt_radius
    obtain ⟨t14, -, t15, t15e⟩ : c₃.nreg 50214 = 1 ∧ True ∧ c₃.nreg 50215 < E.P.n ∧
        ((chainModel C).pos (Qof E.P) ⟨c.nreg a, 0⟩).2 = ((Qof E.P).vtx (c₃.nreg 50215)).2 := by
      rcases hy with ⟨-, hv⟩ | ⟨-, hv⟩ | ⟨k, -, hl, hv⟩
      · rw [hv, abs_neg, abs_of_pos C.radius_pos] at hyR; exact absurd hyR (lt_irrefl _)
      · rw [hv, abs_of_pos C.radius_pos] at hyR; exact absurd hyR (lt_irrefl _)
      · exact ⟨k, trivial, hl, hv⟩
    have h8 : ∀ q, 80000 ≤ q → q < 90000 → c₃.nreg q = c₂.nreg q := fun q h1 h2 =>
      hfr₃.1 q (by rw [band8 h1 h2]; simp [primBands, bRestore, bSign, bLocate])
        (by unfold ALLOC; omega)
    refine FRS.seq (K₂ := 1) (FRS.prim (Q := fun c' => c' = c₃) hB hI₂ ex₃ hfr₃ le_rfl (by omega) rfl)
      (fun c₄ hI₄ _ h₄ => ?_)
    subst h₄
    have ok' : okB E.W c₄.nmem [.copyN 81062 50215] c₄.nreg := by
      simp only [okB, okI]; exact ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), trivial⟩
    refine (FRS.block hB _ hI₄ ok').mono le_rfl (fun c₅ h₅ => ?_)
    have e₅ : ∀ q, c₅.nreg q = regB c₄.nmem [.copyN 81062 50215] c₄.nreg q := fun q => by
      rw [h₅]
    have v62 : c₅.nreg 81062 = c₄.nreg 50215 := by rw [e₅]; simp [regB, regI, upd]
    refine ⟨by rw [v62]; exact t15, by rw [v62, ← t15e, hM], hfin c₅ fun q h1 h2 h3 _ => ?_⟩
    rw [e₅, show regB c₄.nmem [.copyN 81062 50215] c₄.nreg q = c₄.nreg q by
      simp [regB, regI, upd, h3], h8 q h1 h2, f₂ q h1]
  · -- the interior model: `iIdx bit n e`
    refine (FRS.ifT (show c₁.nreg 81011 < c₁.nreg 81064 by rw [j11, r64, h1]; omega) ?_).mono (K := 15819) (by omega) (fun _ h => h)
    have ok : okB E.W c₁.nmem [.addN 81064 81000 81012, .loadN 81064 81064] c₁.nreg := by
      simp only [okB, okI]
      exact ⟨⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), by rw [j0, j12]; omega⟩,
        Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), trivial⟩
    refine FRS.seq (K₂ := 8) (FRS.block hB _ hI₁ ok) (fun c₂ hI₂ _ h₂ => ?_) |>.mono
      (by simp) (fun _ h => h)
    have e₂ : ∀ q, c₂.nreg q = regB c₁.nmem [.addN 81064 81000 81012, .loadN 81064 81064]
        c₁.nreg q := fun q => by rw [h₂]
    set bit := c.nmem (E.MD + 1) with hbit'
    have b64 : c₂.nreg 81064 = bit := by rw [e₂]; simp [regB, regI, upd, j0, j12, m₁, hbit']
    have f₂ : ∀ q, q ≠ 81064 → c₂.nreg q = c₁.nreg q := fun q hq => by
      rw [e₂]; simp [regB, regI, upd, hq]
    obtain ⟨-, l11, l12, l20⟩ := fx c₂ hI₂
    have he : c.nreg a < E.P.n := by rw [hM, interior_n] at hea; exact hea
    have ha' : c₂.nreg a = c.nreg a := by rw [f₂ a ha64, ea]
    -- the reversed index
    have hrev : ∀ c' : Config, FInv E.W c₀ c' → (∀ q, q ≠ 81064 → c'.nreg q = c₂.nreg q) →
        c'.nreg 81064 = bit → bit ≠ 1 →
        FRS B E.P E.W c₀ (hvRev a) c' 2 (fun c'' => c''.nreg 81062 < E.P.n ∧
          ((Qof E.P).vtx (c''.nreg 81062)).2 = (E.M.pos (Qof E.P) ⟨c.nreg a, 0⟩).2 ∧
          ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81062 → q ≠ 81064 → c''.nreg q = c.nreg q) := by
      intro c' hI' hc' _ hb1
      have okr : okB E.W c'.nmem [.subN 81062 81020 81012, .subN 81062 81062 a] c'.nreg := by
        simp only [okB, okI]
        exact ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩),
          Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), trivial⟩
      refine (FRS.block hB _ hI' okr).mono le_rfl (fun c'' h'' => ?_)
      have e'' : ∀ q, c''.nreg q = regB c'.nmem [.subN 81062 81020 81012, .subN 81062 81062 a]
          c'.nreg q := fun q => by rw [h'']
      have v62 : c''.nreg 81062 = iIdx bit E.P.n (c.nreg a) := by
        have w20 : c'.nreg 81020 = E.P.n := by rw [hc' _ (by norm_num), l20]
        have w12 : c'.nreg 81012 = 1 := by rw [hc' _ (by norm_num), l12]
        have wa : c'.nreg a = c.nreg a := by rw [hc' _ ha64, ha']
        rw [e'']
        unfold iIdx; rw [ite_eq_right hb1]
        simp [regB, regI, upd, ha62, w20, w12, wa]
      refine ⟨by rw [v62]; exact iIdx_lt he, ?_, fun q h1 h2 h3 h4 => ?_⟩
      · rw [v62, hM, pos_vtx0, interior_wa (P := E.P) hbit he]
      · rw [e'', show regB c'.nmem [.subN 81062 81020 81012, .subN 81062 81062 a] c'.nreg q =
          c'.nreg q by simp [regB, regI, upd, h3], hc' q h4, f₂ q h4, f₁ q h4]
    have hI₂' := hI₂
    by_cases hb : 1 < bit
    · exact (FRS.ifT (show c₂.nreg 81012 < c₂.nreg 81064 by rw [l12, b64]; exact hb) (hrev c₂ hI₂ (fun _ _ => rfl) b64
        (by omega))).mono (by omega) (fun _ h => h)
    refine FRS.ifF (show ¬ c₂.nreg 81012 < c₂.nreg 81064 by rw [l12, b64]; exact hb) ?_ |>.mono (K := 8) (by omega) (fun _ h => h)
    by_cases hb0 : 0 < bit
    · have hb1 : bit = 1 := by omega
      refine FRS.ifT (show c₂.nreg 81011 < c₂.nreg 81064 by rw [l11, b64]; exact hb0) ?_ |>.mono (K := 6) (by omega) (fun _ h => h)
      have okc : okB E.W c₂.nmem [.copyN 81062 a] c₂.nreg := by
        simp only [okB, okI]; exact ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), trivial⟩
      refine (FRS.block hB _ hI₂ okc).mono (by simp) (fun c'' h'' => ?_)
      have e'' : ∀ q, c''.nreg q = regB c₂.nmem [.copyN 81062 a] c₂.nreg q := fun q => by
        rw [h'']
      have v62 : c''.nreg 81062 = iIdx bit E.P.n (c.nreg a) := by
        rw [e'']; simp only [regB, regI, upd, ite_true]; rw [ha']
        unfold iIdx; rw [ite_eq_left hb1]
      refine ⟨by rw [v62]; exact iIdx_lt he, ?_, fun q h1 h2 h3 h4 => ?_⟩
      · rw [v62, hM, pos_vtx0, interior_wa (P := E.P) hbit he]
      · rw [e'', show regB c₂.nmem [.copyN 81062 a] c₂.nreg q = c₂.nreg q by
          simp [regB, regI, upd, h3], f₂ q h4, f₁ q h4]
    · exact (FRS.ifF (show ¬ c₂.nreg 81011 < c₂.nreg 81064 by rw [l11, b64]; exact hb0) (hrev c₂ hI₂ (fun _ _ => rfl) b64
        (by omega))).mono (by omega) (fun _ h => h)
end

end Restore

end Chazelle.Core
