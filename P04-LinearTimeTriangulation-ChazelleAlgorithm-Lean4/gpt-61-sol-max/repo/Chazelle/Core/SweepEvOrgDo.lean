module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvCand5
public import Chazelle.Core.SweepEvOrg3

/-!
# The sweep (WP-D), stage 3: one origin (RAM)

`orgDo sh g`: the end `oS` of the chord `oK` of `N₂`: read it (`orgHead`), classify it
(`orgCls`), and for a valid origin (class `1`) read its abscissa (`callAbs`) and run the candidate
(`evCand`).  `orgDo_irs`: soundness `CandRes` and completeness `CandComp` for every origin on `C₂`
other than the shared vertex and the top of `C₂` (an origin above the top of `C₁` has its first
hit in `C` on `C₂`, `high_no_hit`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- **One origin**: the end `oS` of the chord `oK` of `N₂`. -/
def orgDo (sh g : Stmt) : Stmt :=
  .seq orgHead (.seq orgCls (.ifLtN oCl K1 .skip (.ifLtN K1 oCl .skip
    (.seq (callAbs (sw 21) oE oC oAbsA) (evCand sh g)))))

/-- The cost of one origin. -/
def orgDoK (Fg K KG : ℕ) : ℕ := evCandK Fg K KG + 60000

/-- The registers an origin may write. -/
def OrgR (r : ℕ) : Prop := CandR r ∨ (sw 2202 ≤ r ∧ r ≤ sw 2232)

theorem loSet_congr {M : Model} {Q : Polygon} {m m' : ℕ → ℕ} {A K : ℕ}
    {hs : List (WPos × WPos)} (h : ∀ x, A ≤ x → x < A + 4 * K → m' x = m x) :
    ShotList.loSet M Q m' A K hs = ShotList.loSet M Q m A K hs := by
  have ha : ∀ j, j < K → ShotList.arcAt m' A j = ShotList.arcAt m A j := fun j hj => by
    grind [ShotList.arcAt]
  ext x
  unfold ShotList.loSet
  grind

section
variable {P : Polygon} {J : Merge.Junction} {S₂ : Set (Set Point)} {T j u d : ℕ} {a : Point} {σ : ℝ}
theorem candComp_lift {lo : Set Point} {c c₃ c' : Config} (hs : SameKB c c₃)
    (hA : c.nreg ALLOC ≤ c₃.nreg ALLOC) (hm : ∀ x, x < c.nreg ALLOC → c₃.nmem x = c.nmem x)
    (h : CandComp P J S₂ T j u d a σ lo c₃ c') : CandComp P J S₂ T j u d a σ lo c c' :=
  fun p t h1 h2 h3 h4 h5 h6 => by
    obtain ⟨hh, e1, e2⟩ := h p t h1 h2 h3 h4 h5 h6
    exact ⟨hh, e1, accAt_lift hs hA hm e2⟩

theorem candRes_lift {c c₃ c' : Config} (hs : SameKB c c₃)
    (hA : c.nreg ALLOC ≤ c₃.nreg ALLOC) (hm : ∀ x, x < c.nreg ALLOC → c₃.nmem x = c.nmem x)
    (h : CandRes P J S₂ T j u d a σ c₃ c') : CandRes P J S₂ T j u d a σ c c' := by
  rcases h with h | ⟨e, hh, h⟩
  · exact Or.inl (rejAt_lift hs hA hm h)
  · exact Or.inr ⟨e, hh, accAt_lift hs hA hm h⟩


end

/-- The ends of a chord record are positions of the walk proper. -/
theorem end_facts {P : Polygon} {J : Merge.Junction} {N₂ : NF}
    (hNF : IsNF (chainModel J.right) (Qof P) N₂) {k : ℕ} (hk : k < N₂.nChords) (s : ℕ) :
    (endPos N₂ k s).edge < (chainModel J.right).W.n ∧
      ProperPos (chainModel J.right) (Qof P) P.n (endPos N₂ k s) ∧
      (farEnd N₂ k s).edge < (chainModel J.right).W.n ∧
      ProperPos (chainModel J.right) (Qof P) P.n (farEnd N₂ k s) := by
  have hA := hNF.2.2.1 k hk
  have hhn := (regOf_spec hNF).2.2.2.2.2.1 k hk
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hpl : ProperPos (chainModel J.right) (Qof P) P.n (N₂.chord k).lpos :=
    ⟨hA.1.2.1, hA.1.2.2.1, by aesop⟩
  have hpr : ProperPos (chainModel J.right) (Qof P) P.n (N₂.chord k).rpos :=
    ⟨hA.2.2.1, hA.2.2.2.1, by aesop⟩
  unfold endPos farEnd
  split_ifs
  · exact ⟨hA.1.1, hpl, hA.2.1, hpr⟩
  · exact ⟨hA.2.1, hpr, hA.1.1, hpl⟩

/-- The origin and the direction of the end `s` of chord `k`. -/
theorem endOrigin_ks {Q : Polygon} {J : Merge.Junction} {N₂ : NF}
    (hNF : IsNF (chainModel J.right) Q N₂) {k s : ℕ} (hk : k < N₂.nChords) (hs : s ≤ 1) :
    endOrigin J Q N₂ (2 * k + s) = (chainModel J.right).pos Q (endPos N₂ k s) ∧
      endDir (2 * k + s) = dirOf (if s = 0 then 1 else 0) ∧
      ((dirOf (if s = 0 then 1 else 0) = 1 ∧
          endOrigin J Q N₂ (2 * k + s) = Merge.lend ((N₂.chord k).toSet (chainModel J.right) Q)) ∨
        (dirOf (if s = 0 then 1 else 0) = -1 ∧
          endOrigin J Q N₂ (2 * k + s) = Merge.rend ((N₂.chord k).toSet (chainModel J.right) Q))) ∧
      (chainModel J.right).pos Q (farEnd N₂ k s) =
        (if (if s = 0 then 1 else 0) = 1 then Merge.rend ((N₂.chord k).toSet (chainModel J.right) Q)
          else Merge.lend ((N₂.chord k).toSet (chainModel J.right) Q)) := by
  have hj : 2 * k + s < 2 * N₂.nChords := by omega
  have h2 : (2 * k + s) / 2 = k := by omega
  have h3 : (2 * k + s) % 2 = s := by omega
  obtain ⟨hO, -⟩ := endOrigin_eq J hNF hj
  have hF := farOrigin_eq J hNF hj
  grind [endDir, dirOf, endOrigin]

/-- **An origin above the top of `C₁`** has its first hit in `C` on `C₂`. -/
theorem high_no_hit {J : Merge.Junction} {a : Point} (haR : a ∈ J.right.set) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hhigh : ¬ a.2 ≤ J.left.top.2) :
    ¬ J.whole.hitParam a σ < J.right.hitParam a σ := by
  have ha₂ : a.2 ≤ J.right.top.2 := J.right.snd_le_top_of_mem_set haR
  have hbox : J.right.hitParam a σ ≤ Merge.rayHit J.whole.radius ∅ a σ := by
    unfold Merge.rayHit
    refine le_csInf (Merge.rayHitSet_nonempty _ _ _ hσ) fun t ht => ?_
    obtain ⟨ht0, hout⟩ := ht
    refine J.right.hitParam_le_of_not_mem_dom a σ ht0 fun hd => ?_
    rcases hout with h | h
    · exact h (J.right.dom_subset_box hd)
    · simp at h
  rw [whole_hit_right ha₂ hσ (fun h => absurd h hhigh) hbox]
  simp_all

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **One origin.** -/
theorem orgDo_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {g : Stmt} {KG : ℕ}
    (hgen : GenOK P W c₀ J g KG) {L : List ℕ} (hL : ∀ a ∈ L, a < N₁.arcs.length)
    (hgK : c.nreg wGK = L.length) (hAB : c.nreg wGB + 4 * L.length ≤ c.nreg ALLOC)
    (harcs : ∀ k, k < L.length → ShotList.arcAt c.nmem (c.nreg wGB) k =
      nArc (chainModel J.left) (Qof P) N₁ (L.getD k 0))
    {k s : ℕ} (hkd : c.nreg oK = k) (hsd : c.nreg oS = s) (hk : k < N₂.nChords) (hs : s ≤ 1)
    (hkey : PosW P J (c.nreg kE) (c.nreg kH))
    (hb : c.nreg bF = 1 → PosW P J (c.nreg bE) (c.nreg bH))
    (hbF : c.nreg bF ≤ 1) (hbN : c.nreg bN ≤ 4)
    (hroom : c.nreg ALLOC + orgDoK (F (c₀.nreg (sw 5))) L.length KG ≤ W) :
    IRS P W c₀ (orgDo sh g) c (orgDoK (F (c₀.nreg (sw 5))) L.length KG) (fun c' =>
      CandRes P J (N₂.F (chainModel J.right) (Qof P)) (c.nreg cTB) (2 * k + s)
        (N₂.chord k).up (N₂.chord k).dn
        (endOrigin J (Qof P) N₂ (2 * k + s)) (endDir (2 * k + s)) c c' ∧
      (endOrigin J (Qof P) N₂ (2 * k + s) ∈ J.right.set →
        endOrigin J (Qof P) N₂ (2 * k + s) ≠ J.shared →
        endOrigin J (Qof P) N₂ (2 * k + s) ≠ J.right.top →
        CandComp P J (N₂.F (chainModel J.right) (Qof P)) (c.nreg cTB) (2 * k + s)
          (N₂.chord k).up (N₂.chord k).dn
          (endOrigin J (Qof P) N₂ (2 * k + s)) (endDir (2 * k + s))
          (ShotList.loSet (chainModel J.left) (Qof P) c.nmem (c.nreg wGB) L.length []) c c') ∧
      (¬ (endOrigin J (Qof P) N₂ (2 * k + s) ∈ J.right.set ∧
        endOrigin J (Qof P) N₂ (2 * k + s) ≠ J.shared ∧
        endOrigin J (Qof P) N₂ (2 * k + s) ≠ J.right.top) → RejAt c c') ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC) := by
  have hNF := E.hNF₂
  obtain ⟨hEe, hEp, hFe, hFp⟩ := end_facts hNF hk s
  obtain ⟨hband, -⟩ := endPos_band hNF hk s
  obtain ⟨hO, hDir, hLR, hFar⟩ := endOrigin_ks hNF hk hs
  have hσ : endDir (2 * k + s) = 1 ∨ endDir (2 * k + s) = -1 := by
    grind
  -- 1. the head
  refine IRS.mono (K := 11100 + (31410 + (4 + (16707 + evCandK (F (c₀.nreg (sw 5))) L.length KG))))
    (IRS.seq (K₁ := 11100) (K₂ := 31410 + (4 + (16707 + evCandK (F (c₀.nreg (sw 5))) L.length KG)))
      (orgHead_irs hI E.hK (E.ctx2' hI) hNF (E.nw₂' hI) le_rfl (by omega)
        (by omega) (by grind [orgDoK])) ?_)
    (by omega_nf) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨-, vUp, vDn, vD, vE, vC, vFE, vFC, fr₁, -, hm₁⟩
  simp only [hkd, hsd] at vUp vDn vD vE vC vFE vFC
  obtain ⟨hpp', -, hpos', hnorm'⟩ := nhgt_facts hEp
  have hE1 : c₁.nreg oE < 2 * J.right.m + 7 := by rw [vE]; have := cm_n J.right; omega
  have hpp1 : ProperPos (chainModel J.right) (Qof P) P.n ⟨c₁.nreg oE, c₁.nreg oC⟩ := by
    grind
  have hnorm1 : c₁.nreg oC = 0 ↔
      (chainModel J.right).param (Qof P) ⟨c₁.nreg oE, c₁.nreg oC⟩ = 0 := by
    grind
  have hpos1 : (chainModel J.right).pos (Qof P) ⟨c₁.nreg oE, c₁.nreg oC⟩ =
      endOrigin J (Qof P) N₂ (2 * k + s) := by
    grind
  -- 2. the class
  refine IRS.seq (K₁ := 31410) (K₂ := 4 + (16707 + evCandK (F (c₀.nreg (sw 5))) L.length KG))
    (orgCls_irs hI₁ E.hK E.hO (E.ctx2' hI₁) hE1 hpp1 hnorm1
      (by grind [orgDoK])) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨cl2, cl2iff, cl1iff, clsym, fr₂, -, hm₂⟩
  rw [hpos1] at cl2iff cl1iff clsym
  have keep2 : ∀ r, bandOf r ∉ oracleBands → (r < sw 2202 ∨ sw 2232 < r) → r ≠ ALLOC →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 =>
    (fr₂ r h1 (by unfold oCl oU sw at *; omega) h3).trans
      (fr₁ r h1 (by grind [sw]) h3)
  have keep21 : ∀ r, bandOf r ∉ oracleBands → r < oCl → r ≠ ALLOC → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => fr₂ r h1 (Or.inl h2) h3
  have hm12 : ∀ x, x < c.nreg ALLOC → c₂.nmem x = c.nmem x := fun x hx =>
    (hm₂ x (by omega)).trans (hm₁ x hx)
  have best2 : ∀ r, BestR r → c₂.nreg r = c.nreg r := fun r hr => keep2 r
    (band_sw_not (by unfold BestR LblR bF bE bH bN bL sw at hr; omega))
    (by unfold BestR LblR bF bE bH bN bL sw at hr; omega_nf)
    (by unfold BestR LblR bF bE bH bN bL sw at hr; omega_nf)
  
  
  
  have k1 : c₂.nreg K1 = 1 := (E.hK.fix hI₂).2.1
  -- the rejection (class `0` or `2`)
  have rejQ : c₂.nreg oCl ≠ 1 →
      CandRes P J (N₂.F (chainModel J.right) (Qof P)) (c.nreg cTB) (2 * k + s)
        (N₂.chord k).up (N₂.chord k).dn
        (endOrigin J (Qof P) N₂ (2 * k + s)) (endDir (2 * k + s)) c c₂ ∧
      (endOrigin J (Qof P) N₂ (2 * k + s) ∈ J.right.set →
        endOrigin J (Qof P) N₂ (2 * k + s) ≠ J.shared →
        endOrigin J (Qof P) N₂ (2 * k + s) ≠ J.right.top →
        CandComp P J (N₂.F (chainModel J.right) (Qof P)) (c.nreg cTB) (2 * k + s)
          (N₂.chord k).up (N₂.chord k).dn
          (endOrigin J (Qof P) N₂ (2 * k + s)) (endDir (2 * k + s))
          (ShotList.loSet (chainModel J.left) (Qof P) c.nmem (c.nreg wGB) L.length []) c c₂) ∧
      (¬ (endOrigin J (Qof P) N₂ (2 * k + s) ∈ J.right.set ∧
        endOrigin J (Qof P) N₂ (2 * k + s) ≠ J.shared ∧
        endOrigin J (Qof P) N₂ (2 * k + s) ≠ J.right.top) → RejAt c c₂) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → r ≠ ALLOC → c₂.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c₂.nreg ALLOC := by
    intro hn1
    refine ⟨Or.inl ⟨hm12, best2 _ (Or.inl rfl), best2 _ (Or.inr (Or.inl rfl)),
      best2 _ (Or.inr (Or.inr (Or.inl rfl))),
      lblOf_congr (fun q hq => best2 q (Or.inr (Or.inr (Or.inr hq)))),
      best2 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩, ?_, fun _ => ⟨hm12, best2 _ (Or.inl rfl),
      best2 _ (Or.inr (Or.inl rfl)), best2 _ (Or.inr (Or.inr (Or.inl rfl))),
      lblOf_congr (fun q hq => best2 q (Or.inr (Or.inr (Or.inr hq)))),
      best2 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩, ?_, by omega⟩
    · intro haR hav hat p t _ _ _ _ h5 _
      have hhigh : ¬ (endOrigin J (Qof P) N₂ (2 * k + s)).2 ≤ J.left.top.2 :=
        fun h => hn1 (cl1iff.2 ⟨haR, hav, hat, h⟩)
      exact absurd h5 (high_no_hit haR hσ hhigh)
    · intro r h1 h2 h3
      exact keep2 r h1 (by unfold OrgR at h2; omega) h3
  by_cases hc0 : c₂.nreg oCl < c₂.nreg K1
  · exact IRS.mono (K := 0 + 2) (IRS.ifT hc0 (IRS.skip hI₂ (rejQ (by omega)))) (by omega)
      (fun _ h => h)
  refine IRS.mono (K := 16707 + evCandK (F (c₀.nreg (sw 5))) L.length KG + 2 + 2)
    (IRS.ifF hc0 ?_) (by omega) (fun _ h => h)
  by_cases hc2 : c₂.nreg K1 < c₂.nreg oCl
  · exact IRS.mono (K := 0 + 2) (IRS.ifT hc2 (IRS.skip hI₂ (rejQ (by omega)))) (by omega)
      (fun _ h => h)
  refine IRS.ifF hc2 ?_
  have hcl : c₂.nreg oCl = 1 := by omega
  obtain ⟨haR, hav, hat, ha₁⟩ := cl1iff.1 hcl
  obtain ⟨sy, hsym, hsl, hse⟩ := clsym hcl
  -- 3. the abscissa
  have eE2 : c₂.nreg oE = c₁.nreg oE := keep21 _ (band_sw_not (by omega_nf))
    (by omega_nf) (by omega_nf)
  have eC2 : c₂.nreg oC = c₁.nreg oC := keep21 _ (band_sw_not (by omega_nf))
    (by omega_nf) (by omega_nf)
  have hpos2 : (chainModel J.right).pos (Qof P) ⟨c₂.nreg oE, c₂.nreg oC⟩ =
      endOrigin J (Qof P) N₂ (2 * k + s) := by rw [eE2, eC2, hpos1]
  have hy2 : |((chainModel J.right).pos (Qof P) ⟨c₂.nreg oE, c₂.nreg oC⟩).2| < J.right.radius := by
    rw [hpos2, hO]; exact hband
  refine IRS.seq (K₁ := 16707) (K₂ := evCandK (F (c₀.nreg (sw 5))) L.length KG)
    (callAbs_irs hI₂ (E.ctx2' hI₂)
      (by omega_nf) (by omega_nf)
      (by omega) (by rw [eE2, eC2]; exact hpp1) hy2
      (by unfold orgDoK at hroom; omega)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨habs3, fr₃, -, hm₃⟩
  rw [hpos2] at habs3
  have keep32 : ∀ r, bandOf r ∉ oracleBands → (r < oAbsA ∨ oAbsA + 3 < r) → r ≠ ALLOC →
      c₃.nreg r = c₂.nreg r := fr₃
  have keep3 : ∀ r, bandOf r ∉ oracleBands → (r < sw 2202 ∨ sw 2232 < r) → r ≠ ALLOC →
      c₃.nreg r = c.nreg r := fun r h1 h2 h3 =>
    (keep32 r h1 (by unfold oAbsA sw at *; omega) h3).trans (keep2 r h1 h2 h3)
  have keep31 : ∀ r, bandOf r ∉ oracleBands → r < oCl → r ≠ ALLOC → c₃.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => (keep32 r h1 (by unfold oAbsA oCl sw at *; omega) h3).trans
      (keep21 r h1 h2 h3)
  have hm3 : ∀ x, x < c.nreg ALLOC → c₃.nmem x = c.nmem x := fun x hx =>
    (hm₃ x (by omega)).trans (hm12 x hx)
  have best3 : ∀ r, BestR r → c₃.nreg r = c.nreg r := fun r hr => keep3 r
    (band_sw_not (by unfold BestR LblR bF bE bH bN bL sw at hr; omega))
    (by unfold BestR LblR bF bE bH bN bL sw at hr; omega_nf)
    (by unfold BestR LblR bF bE bH bN bL sw at hr; omega_nf)
  have r3 : ∀ r, 240000 ≤ r → r < 250000 → (r < sw 2202 ∨ sw 2232 < r) → c₃.nreg r = c.nreg r :=
    fun r h1 h2 h3 => keep3 r (band_sw_not ⟨h1, h2⟩) h3 (by omega_nf)
  have r31 : ∀ r, 240000 ≤ r → r < oCl → c₃.nreg r = c₁.nreg r :=
    fun r h1 h2 => keep31 r (band_sw_not ⟨h1, by unfold oCl sw at h2; omega⟩) h2
      (by omega_nf)
  have same3 : SameKB c c₃ :=
    ⟨r3 _ (by omega_nf) (by omega_nf) (by omega_nf),
      r3 _ (by omega_nf) (by omega_nf) (by omega_nf), best3⟩
  have eGK : c₃.nreg wGK = c.nreg wGK :=
    r3 _ (by omega_nf) (by omega_nf) (by omega_nf)
  have eGB : c₃.nreg wGB = c.nreg wGB :=
    r3 _ (by omega_nf) (by omega_nf) (by omega_nf)
  have eK : c₃.nreg oK = k := by
    rw [r3 _ (by omega_nf) (by omega_nf) (by omega_nf), hkd]
  have eS : c₃.nreg oS = s := by
    rw [r3 _ (by omega_nf) (by omega_nf) (by omega_nf), hsd]
  have eUp : c₃.nreg oUp = (N₂.chord k).up := by
    rw [r31 _ (by omega_nf) (by omega_nf), vUp]
  have eDn : c₃.nreg oDn = (N₂.chord k).dn := by
    rw [r31 _ (by omega_nf) (by omega_nf), vDn]
  have eD : c₃.nreg oD = if s = 0 then 1 else 0 := by
    rw [r31 _ (by omega_nf) (by omega_nf), vD]
  have eFE : c₃.nreg oFE = (farEnd N₂ k s).edge := by
    rw [r31 _ (by omega_nf) (by omega_nf), vFE]
  have eFC : c₃.nreg oFC = (farEnd N₂ k s).hgt := by
    rw [r31 _ (by omega_nf) (by omega_nf), vFC]
  have eTB : c₃.nreg cTB = c.nreg cTB :=
    (hI₃.hin _ (by omega_nf)).trans (hI.hin _ (by omega_nf)).symm
  have hsym3 : SymPtIn c₃ oSym sy := symPtIn_transport hsym
    (keep32 _ (band_sw_not (by omega_nf)) (by omega_nf)
      (by omega_nf))
    (keep32 _ (band_sw_not (by omega_nf)) (by omega_nf)
      (by omega_nf))
    (keep32 _ (band_sw_not (by omega_nf)) (by omega_nf)
      (by omega_nf))
  have hfar3 : (chainModel J.right).pos (Qof P) ⟨c₃.nreg oFE, c₃.nreg oFC⟩ =
      if c₃.nreg oD = 1 then Merge.rend ((N₂.chord k).toSet (chainModel J.right) (Qof P))
      else Merge.lend ((N₂.chord k).toSet (chainModel J.right) (Qof P)) := by
    rw [eFE, eFC, eD]; exact hFar
  have hch : (N₂.chord k).toSet (chainModel J.right) (Qof P) ∈ N₂.F (chainModel J.right) (Qof P) := by
    refine ⟨N₂.chord k, ?_, rfl⟩
    unfold NF.chord
    rw [NFLoc.getD_of_lt _ hk]
    exact List.getElem_mem _
  have hlo : ShotList.loSet (chainModel J.left) (Qof P) c₃.nmem (c₃.nreg wGB) L.length [] =
      ShotList.loSet (chainModel J.left) (Qof P) c.nmem (c.nreg wGB) L.length [] := by
    rw [eGB]; exact loSet_congr (fun x _ hx => hm3 x (by omega))
  -- 4. the candidate
  have hev := evCand_irs E hI₃ hgen hL (by omega) (by omega)
    (fun i hi => by rw [eGB, ← harcs i hi]; unfold ShotList.arcAt
                    rw [hm3 _ (by omega), hm3 _ (by omega), hm3 _ (by omega), hm3 _ (by omega)])
    hch (by rw [eD]; split_ifs <;> omega) (by rw [eD]; exact hLR) hsym3 hsl hse habs3 haR hav ha₁
    (by omega) (by rw [eFE, eFC]; exact hFp) hfar3 (by omega)
    (by rw [same3.1, same3.2.1]; exact hkey)
    (by rw [best3 _ (Or.inl rfl), best3 _ (Or.inr (Or.inl rfl)),
      best3 _ (Or.inr (Or.inr (Or.inl rfl)))]; exact hb)
    (by rw [best3 _ (Or.inl rfl)]; exact hbF)
    (by rw [best3 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact hbN)
    (by unfold orgDoK at hroom; omega)
  refine hev.mono le_rfl ?_
  rintro c' ⟨hres, hcomp, hfr, hA'⟩
  rw [eTB, eK, eS, eUp, eDn, eD, ← hDir] at hres hcomp
  rw [hlo] at hcomp
  refine ⟨candRes_lift same3 (by omega) hm3 hres, fun _ _ _ => candComp_lift same3 (by omega) hm3 hcomp,
    fun hnv => absurd ⟨haR, hav, hat⟩ hnv, fun r h1 h2 h3 => ?_, by omega⟩
  unfold OrgR at h2
  push Not at h2
  rw [hfr r h1 (fun h => h2.1 h) h3]
  exact keep3 r h1 (by omega) h3

end

end SweepEv

end Chazelle.Core
