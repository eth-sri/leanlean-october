module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvOrg2

/-!
# The sweep (WP-D), stages 2–3: the end of a chord of `N₂` on the RAM, part 3 (height test)

`orgHt`: the symbolic point of the end (`callSym`) and one sign-kernel test against the top of
`C₁`: class `1` iff the end is not above the top of `C₁`, else `0`.
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sidePt)

@[expose] public section

/-- The height test. -/
def orgHt : Stmt :=
  .seq (callSym (sw 21) oE oC oSym)
    (.seq (kbit cT1 oSym cT1 1 oHb) (.ifLtN oHb K1 (.instr (.constN oCl 1)) (.instr (.constN oCl 0))))

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

set_option maxRecDepth 20000 in
theorem orgHt_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c) (hO : OrgK P J c)
    (hctx : ChainCtx P W c (sw 21) J.right) (h6 : 6 ≤ c.nreg oE)
    (he : c.nreg oE < 2 * J.right.m + 6)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg oE, c.nreg oC⟩)
    (hnorm : c.nreg oC = 0 ↔ (chainModel J.right).param (Qof P) ⟨c.nreg oE, c.nreg oC⟩ = 0)
    (hroom : c.nreg ALLOC + 31300 ≤ W) :
    IRS P W c₀ orgHt c 31300 (fun c' =>
      (∃ s : SymPt, SymPtIn c' oSym s ∧ s.Lt P.n ∧
        s.eval (Qof P) = (chainModel J.right).pos (Qof P) ⟨c.nreg oE, c.nreg oC⟩) ∧
      (c'.nreg oCl = 1 ↔
        ((chainModel J.right).pos (Qof P) ⟨c.nreg oE, c.nreg oC⟩).2 ≤ J.left.top.2) ∧
      c'.nreg oCl ≤ 1 ∧
      (∀ r, bandOf r ∉ oracleBands → (r < oSym ∨ oSym + 2 < r) → r ≠ oCl → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  obtain ⟨-, k1, -, -, -, -, -⟩ := hK
  have hG := hctx.1
  have hPW : P.n + 3 ≤ W := by have := hctx.2.1; grind [hostWords]
  set a := (chainModel J.right).pos (Qof P) ⟨c.nreg oE, c.nreg oC⟩ with ha
  refine IRS.seq (K₁ := 31006) (K₂ := 294)
    (callSym_irs (P := P) (C := J.right) hI hctx (by omega_nf)
      (by omega_nf) h6 he hpp hnorm (by omega)) ?_ |>.mono (by norm_num) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨s, hs, hsl, hse⟩, k₁, hA₁'', hm₁⟩
  have hk1₁ : c₁.nreg K1 = 1 := by
    rw [k₁ K1 (band_sw_not (by omega_nf)) (by omega_nf)
      (by omega_nf), k1]
  obtain ⟨t, ht, htl, hte⟩ := hO.t1
  have ht₁ : SymPtIn c₁ cT1 t := symPtIn_transport ht
    (k₁ cT1 (band_sw_not (by omega_nf)) (by omega_nf)
      (by omega_nf))
    (k₁ (cT1 + 1) (band_sw_not (by omega_nf)) (by omega_nf)
      (by omega_nf))
    (k₁ (cT1 + 2) (band_sw_not (by omega_nf)) (by omega_nf)
      (by omega_nf))
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hbit₂⟩ := kbit_exec (op := 1) (dst := oHb) hG hPW c₁ hI₁.hw
    (by omega_nf) (by omega_nf) (by omega_nf)
    (by omega_nf) (by norm_num) htl hsl htl ht₁ hs ht₁
  have hOr : ∀ r, Bkb oHb r = true → bandOf r ∈ oracleBands := by
    intro r hr
    simp only [Bkb, WalkKey.Bk, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, oHb] at hr
    rcases hr with h | h
    · exact band1_oracle (by omega) (by omega)
    · subst h; exact band5_oracle (by norm_num) (by norm_num)
  refine IRS.seq (K₁ := 241) (K₂ := 6) (IRS.ofFrameB hI₁ e₂ hk₂ f₂ hOr rfl) ?_ |>.mono
    (by norm_num) (fun _ h => h)
  rintro c₃ hI₃ hA₃ hA₃' rfl
  have hfr : ∀ r, Bkb oHb r = false → c₂.nreg r = c₁.nreg r := fun r hr => f₂.1 r hr
  have hk1₂ : c₂.nreg K1 = 1 := by
    grind [Bkb, WalkKey.Bk, K1, oHb, sw]
  have hs₂ : SymPtIn c₂ oSym s := symPtIn_transport hs
    (hfr oSym (by simp [Bkb, WalkKey.Bk, oSym, oHb, sw]))
    (hfr (oSym + 1) (by simp [Bkb, WalkKey.Bk, oSym, oHb, sw]))
    (hfr (oSym + 2) (by simp [Bkb, WalkKey.Bk, oSym, oHb, sw]))
  have hbit : c₂.nreg oHb = 1 ↔ J.left.top.2 < a.2 := by
    ram_grind
  have hfinal : ∀ v, v ≤ 1 → (v = 1 ↔ a.2 ≤ J.left.top.2) →
      IRS P W c₀ (.instr (.constN oCl v)) c₂ 3 (fun c' =>
        (∃ s : SymPt, SymPtIn c' oSym s ∧ s.Lt P.n ∧ s.eval (Qof P) = a) ∧
        (c'.nreg oCl = 1 ↔ a.2 ≤ J.left.top.2) ∧ c'.nreg oCl ≤ 1 ∧
        (∀ r, bandOf r ∉ oracleBands → (r < oSym ∨ oSym + 2 < r) → r ≠ oCl → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
    intro v hv hvi
    refine (IRS.reg (P := P) hI₃ (iscr_sw (by omega_nf) (by omega_nf))
      (Exec.constN hI₃.hw oCl v (by omega))).mono
      (by norm_num) ?_
    rintro c' rfl
    simp only [upd_same]
    refine ⟨⟨s, symPtIn_transport hs₂ (by omega_nf)
      (by omega_nf)
      (by omega_nf), hsl, hse⟩, hvi, hv,
      fun r hr h1 h2 hra => ?_, ?_, fun x hx => ?_⟩
    · rw [upd_other _ _ _ h2, hfr r (by
          grind)]
      grind
    · have h3 : c₂.nreg ALLOC = c₁.nreg ALLOC := hfr ALLOC (by
        simp [Bkb, WalkKey.Bk, ALLOC, oHb])
      rw [upd_other _ _ _ (by omega_nf), h3]; exact hA₁''
    · ram_grind
  by_cases hb : c₂.nreg oHb < c₂.nreg K1
  · refine (IRS.ifT hb (hfinal 1 le_rfl ?_)).mono (by norm_num) (fun _ h => h)
    grind
  · refine (IRS.ifF hb (hfinal 0 (by norm_num) ?_)).mono (by norm_num) (fun _ h => h)
    grind

end

end SweepEv

end Chazelle.Core

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sidePt)

@[expose] public section

/-- A tour vertex: its index decides `v` and the top of `C₂`. -/
def orgVtx : Stmt :=
  .seq orgIdx (.ifLtN oJ K1 (.instr (.constN oCl 0))
    (.ifLtN oJ cTop orgHt (.ifLtN cTop oJ orgHt (.instr (.constN oCl 0)))))

/-- **The class of the end** `(oE, oC)`. -/
def orgCls : Stmt :=
  .ifLtN oE K6 (.instr (.constN oCl 2))
    (.ifLtN oE c2m6 (.ifLtN oC K1 orgVtx orgHt)
      (.ifLtN K0 oC (.instr (.constN oCl 2)) orgVtx))

/-- The facts computed by `orgCls` for the point `a` of the end. -/
def ClsOut (P : Polygon) (J : Merge.Junction) (a : Point) (c c' : Config) : Prop :=
  c'.nreg oCl ≤ 2 ∧ (c'.nreg oCl = 2 ↔ a ∉ J.right.set) ∧
    (c'.nreg oCl = 1 ↔ a ∈ J.right.set ∧ a ≠ J.shared ∧ a ≠ J.right.top ∧ a.2 ≤ J.left.top.2) ∧
    (c'.nreg oCl = 1 → ∃ s : SymPt, SymPtIn c' oSym s ∧ s.Lt P.n ∧ s.eval (Qof P) = a) ∧
    (∀ r, bandOf r ∉ oracleBands → (r < oCl ∨ oU < r) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ x, x < c.nreg ALLOC → c'.nmem x = c.nmem x)

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- A constant class. -/
theorem cls_const {J : Merge.Junction} {a : Point} (hI : IInv W c₀ c) (hW : 2 ≤ W)
    {v : ℕ} (hv : v ≤ 2) (h2 : v = 2 ↔ a ∉ J.right.set)
    (h1 : v = 1 ↔ a ∈ J.right.set ∧ a ≠ J.shared ∧ a ≠ J.right.top ∧ a.2 ≤ J.left.top.2)
    (hn1 : v ≠ 1) {K : ℕ} (hK : 1 ≤ K) :
    IRS P W c₀ (.instr (.constN oCl v)) c K (ClsOut P J a c) := by
  refine (IRS.reg (P := P) hI (iscr_sw (by omega_nf) (by omega_nf))
    (Exec.constN hI.hw oCl v (by omega))).mono hK ?_
  rintro c' rfl
  refine ⟨by simp [hv], by simp [h2], by simp [h1], fun h => absurd (by simp_all) hn1,
    fun r _ hr hra => ?_, by omega_nf,
    fun x _ => rfl⟩
  ram_simp 

/-- An `orgHt` leaf: the end is on `C₂`, neither `v` nor the top of `C₂`. -/
theorem cls_ht {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c) (hO : OrgK P J c)
    (hctx : ChainCtx P W c (sw 21) J.right) (h6 : 6 ≤ c.nreg oE)
    (he : c.nreg oE < 2 * J.right.m + 6)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg oE, c.nreg oC⟩)
    (hnorm : c.nreg oC = 0 ↔ (chainModel J.right).param (Qof P) ⟨c.nreg oE, c.nreg oC⟩ = 0)
    {a : Point} (ha : (chainModel J.right).pos (Qof P) ⟨c.nreg oE, c.nreg oC⟩ = a)
    (hmem : a ∈ J.right.set) (hv : a ≠ J.shared) (ht : a ≠ J.right.top)
    (hroom : c.nreg ALLOC + 31300 ≤ W) {K : ℕ} (hK31 : 31300 ≤ K) :
    IRS P W c₀ orgHt c K (ClsOut P J a c) := by
  refine (orgHt_irs hI hK hO hctx h6 he hpp hnorm hroom).mono hK31 ?_
  rintro c' ⟨hsym, hcl, hle, hfr, hA, hm⟩
  grind [Chazelle.Core.SweepEv.ClsOut, oSym, oCl, oU, sw]

end

end SweepEv

end Chazelle.Core

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sidePt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

set_option maxHeartbeats 2000000 in
/-- **The class of the end.** -/
theorem orgCls_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hO₀ : OrgK P J c₀)
    (hctx : ChainCtx P W c (sw 21) J.right) (he : c.nreg oE < 2 * J.right.m + 7)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg oE, c.nreg oC⟩)
    (hnorm : c.nreg oC = 0 ↔ (chainModel J.right).param (Qof P) ⟨c.nreg oE, c.nreg oC⟩ = 0)
    (hroom : c.nreg ALLOC + 31410 ≤ W) :
    IRS P W c₀ orgCls c 31410
      (ClsOut P J ((chainModel J.right).pos (Qof P) ⟨c.nreg oE, c.nreg oC⟩) c) := by
  have hK : Consts c := hK₀.fix hI
  have hO : OrgK P J c := hO₀.fix hI
  have hP : J.right.P.Simple := hctx.2.2.2.2.1
  have hWm : 2 * J.right.m + 7 ≤ W := hctx.2.2.2.2.2
  have k0 : c.nreg K0 = 0 := hK.1
  have k1 : c.nreg K1 = 1 := hK.2.1
  have k6 : c.nreg K6 = 6 := hK.2.2.1
  
  have mtop := hO.top
  have m26 := hO.m26
  set e := c.nreg oE with hedef
  set a := (chainModel J.right).pos (Qof P) ⟨c.nreg oE, c.nreg oC⟩ with ha
  have hn₂ : (chainModel J.right).W.n = 2 * J.right.m + 7 := cm_n J.right
  have hmemiff := pos_mem_set_iff J.right hP (Q := Qof P) (x := ⟨c.nreg oE, c.nreg oC⟩)
    (by omega_nf) hpp.1 hpp.2.1 hnorm
  simp only at hmemiff
  have hvzero : J.shared = J.right.vertex 0 := (Merge.Junction.right_vertex_zero J).symm
  have htop : J.right.top = J.right.vertex J.right.topIdx := rfl
  have hW2 : 2 ≤ W := by omega
  -- the vertex case
  have hvtx : c.nreg oC = 0 → 6 ≤ e → e ≤ 2 * J.right.m + 6 →
      IRS P W c₀ orgVtx c 31398 (ClsOut P J a c) := by
    intro h0 h6 h26
    have hav : a = J.right.vertex (J.right.sideIdx J.right.sideBeta (e - 6)) :=
      pos_vertex J.right (Q := Qof P) (x := ⟨e, c.nreg oC⟩) h6 h26 h0
    have hamem : a ∈ J.right.set := by grind
    refine IRS.seq (K₁ := 12) (K₂ := 31386) (orgIdx_irs hI hK hO h6 h26 hWm) ?_ |>.mono
      (by norm_num) (fun _ h => h)
    rintro c₁ hI₁ hA₁ hA₁' ⟨hm₁, vJ, k₁⟩
    have hle := J.right.sideIdx_le J.right.sideBeta (e - 6)
    set idx := J.right.sideIdx J.right.sideBeta (e - 6) with hidx
    have kk : ∀ r, (r < oT ∨ oU < r) → oJ ≠ r → c₁.nreg r = c.nreg r := fun r hr hj =>
      k₁ r (by unfold oT oU sw at *; omega) (by unfold oT oU sw at *; omega) (Ne.symm hj)
    have k1₁ : c₁.nreg K1 = 1 := by grind [K1, oT, oU, sw, oJ]
    have kt₁ : c₁.nreg cTop = J.right.topIdx := by
      grind [cTop, oT, oU, sw, oJ]
    have kE₁ : c₁.nreg oE = e := kk oE (by omega_nf) (by omega_nf)
    have kC₁ : c₁.nreg oC = c.nreg oC := kk oC (by omega_nf)
      (by omega_nf)
    have lift : ∀ c', ClsOut P J a c₁ c' → ClsOut P J a c c' := by
      rintro c' ⟨h1, h2, h3, h4, h5, h6', h7⟩
      refine ⟨h1, h2, h3, h4, fun r hr hr2 hra => ?_, by omega, fun x hx => ?_⟩
      · rw [h5 r hr hr2 hra]
        exact kk r (by unfold oCl oT oU sw at *; omega) (by unfold oCl oJ oU sw at *; omega)
      grind
    have hv_iff : a = J.shared ↔ idx = 0 := by
      rw [hav, hvzero]
      exact ⟨fun h => J.right.sideVertex_inj hP hle (Nat.zero_le _) h, fun h => by rw [h]⟩
    have ht_iff : a = J.right.top ↔ idx = J.right.topIdx := by
      rw [hav, htop]
      exact ⟨fun h => J.right.sideVertex_inj hP hle J.right.topIdx_le h, fun h => by rw [h]⟩
    have h2m : idx ≠ J.right.topIdx → e < 2 * J.right.m + 6 := by
      intro hne
      by_contra hc
      apply hne
      rw [hidx, show e - 6 = 2 * J.right.m by omega, Chain.sideIdx_two_m]
    have hht : idx ≠ J.right.topIdx → a ≠ J.shared → IRS P W c₀ orgHt c₁ 31300 (ClsOut P J a c) := by
      intro hne hav0
      have hctx₁ : ChainCtx P W c₁ (sw 21) J.right :=
        hctx.transport (kk (sw 21) (by omega_nf) (by omega_nf))
          (fun x _ => by rw [hm₁]) hA₁
      refine (cls_ht hI₁ (hK₀.fix hI₁) (hO₀.fix hI₁) hctx₁ (by omega)
          (by omega) (by grind) (by grind)
          (by grind) hamem hav0 (fun h => hne (ht_iff.1 h)) (by omega) le_rfl).mono le_rfl
          (fun c' h => lift c' h)
    by_cases hj0 : c₁.nreg oJ < c₁.nreg K1
    · rw [vJ, k1₁] at hj0
      refine IRS.ifT (K := 31384) (by omega) ?_ |>.mono (by norm_num)
        (fun c' h => lift c' h)
      refine cls_const (v := 0) hI₁ hW2 (by norm_num) ⟨fun h => by omega, fun h => absurd hamem h⟩
        ⟨fun h => by omega, fun h => absurd (hv_iff.2 (by omega)) h.2.1⟩ (by norm_num)
        (by norm_num)
    · have hj0' : ¬ idx < 1 := by omega
      have hav0 : a ≠ J.shared := fun h => hj0' (by grind)
      refine IRS.ifF (K := 31384) hj0 ?_ |>.mono (by norm_num) (fun _ h => h)
      by_cases hlt : c₁.nreg oJ < c₁.nreg cTop
      · rw [vJ, kt₁] at hlt
        exact (IRS.ifT (by omega) (hht (by omega) hav0)).mono (by norm_num)
          (fun _ h => h)
      · 
        refine IRS.ifF (K := 31382) hlt ?_ |>.mono (by norm_num) (fun _ h => h)
        by_cases hgt : c₁.nreg cTop < c₁.nreg oJ
        · rw [vJ, kt₁] at hgt
          exact (IRS.ifT (by omega) (hht (by omega) hav0)).mono (by norm_num)
            (fun _ h => h)
        · 
          have heq : idx = J.right.topIdx := by omega
          refine (IRS.ifF hgt (cls_const (v := 0) (K := 1) hI₁ hW2 (by norm_num)
            ⟨fun h => by omega, fun h => absurd hamem h⟩
            ⟨fun h => by omega, fun h => absurd (ht_iff.2 heq) h.2.2.1⟩ (by norm_num)
            le_rfl)).mono (by norm_num) (fun c' h => lift c' h)
  by_cases h6 : c.nreg oE < c.nreg K6
  · rw [k6] at h6
    have hna : a ∉ J.right.set := by grind
    exact (IRS.ifT (by omega) (cls_const hI hW2 (v := 2) (K := 1) (by norm_num)
      ⟨fun _ => hna, fun _ => rfl⟩ ⟨fun h => by omega, fun h => absurd h.1 hna⟩
      (by norm_num) (by norm_num))).mono (by norm_num) (fun _ h => h)
  · 
    refine IRS.ifF (K := 31408) h6 ?_ |>.mono (by norm_num) (fun _ h => h)
    by_cases h26 : c.nreg oE < c.nreg c2m6
    · have h26' : e < 2 * J.right.m + 6 := by omega
      refine IRS.ifT (K := 31406) h26 ?_ |>.mono (by norm_num) (fun _ h => h)
      by_cases h0 : c.nreg oC < c.nreg K1
      · rw [k1] at h0
        exact (IRS.ifT (by omega) (hvtx (by omega) (by omega) (by omega))).mono
          (by norm_num) (fun _ h => h)
      · have h0' : c.nreg oC ≠ 0 := by omega
        have hpar : 0 < (chainModel J.right).param (Qof P) ⟨c.nreg oE, c.nreg oC⟩ :=
          lt_of_le_of_ne hpp.1 (fun h => h0' (hnorm.2 h.symm))
        have hne : ∀ k, a ≠ J.right.vertex k := pos_ne_vertex J.right hP (x := ⟨c.nreg oE, c.nreg oC⟩)
          (show 6 ≤ e by omega) (show e ≤ 2 * J.right.m + 5 by omega) hpar hpp.2.1
        have hamem : a ∈ J.right.set := by grind
        exact (IRS.ifF h0 (cls_ht hI hK hO hctx (by omega) h26' hpp hnorm rfl hamem
          (by grind) (by grind) (by omega) le_rfl)).mono
          (by norm_num) (fun _ h => h)
    · 
      refine IRS.ifF (K := 31406) h26 ?_ |>.mono (by norm_num) (fun _ h => h)
      by_cases hc : c.nreg K0 < c.nreg oC
      · rw [k0] at hc
        have hna : a ∉ J.right.set := by grind
        exact (IRS.ifT (by omega) (cls_const hI hW2 (v := 2) (K := 1) (by norm_num)
          ⟨fun _ => hna, fun _ => rfl⟩ ⟨fun h => by omega, fun h => absurd h.1 hna⟩
          (by norm_num) (by norm_num))).mono (by norm_num) (fun _ h => h)
      · have hc' : c.nreg oC = 0 := by omega
        exact (IRS.ifF hc (hvtx hc' (by omega) (by omega))).mono (by norm_num) (fun _ h => h)

end

end SweepEv

end Chazelle.Core
