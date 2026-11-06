module

public import Chazelle.Golf

public import Chazelle.Core.ShootCutShLpA

/-!
# WP-G, part 58: one piece of the loop

`lpBody_exec`: from the invariant of the loop (`LpI`) with a record left, the record is loaded
and its piece shot at (`pieceK0` or `pieceK1`); the best first hit then covers one more piece,
the invariant holds again, and the potential `(end - pointer) (K + 2)` pays for the steps.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim

@[expose] public section

/-! ## Registers -/

/-- The registers the loop keeps across a piece. -/
def LoopR (r : ℕ) : Prop :=
  r = 140008 ∨ r = 140334 ∨ r = 140100 ∨ r = 140110 ∨ (140234 ≤ r ∧ r < 140241) ∨ r = ALLOC

theorem Blpl_env (r : ℕ) (h : envR r) : Blpl r = false := by
  unfold envR at h
  simp only [Blpl, K1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at h ⊢
  omega

theorem Blpl_org (r : ℕ) (h1 : 140234 ≤ r) (h2 : r < 140241) : Blpl r = false := by
  ϴ Blpl, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne
  omega

theorem Bk0_loop (r : ℕ) (h : LoopR r) : Bk0 r = false := by
  unfold LoopR at h
  simp only [Bk0, Bedge, Bmrg, Bk, Bprim, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at h ⊢
  omega

theorem Wk1_loop (r : ℕ) (h : LoopR r) : Wk1 r = false := by
  unfold LoopR at h
  simp only [Wk1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at h ⊢
  omega

theorem Bk0_ob (r : ℕ) (h : Bk0 r = true) :
    (bandOf r = 1 ∨ bandOf r = 5 ∨ bandOf r = 12 ∨ bandOf r = 14) ∧ r ≠ ALLOC := by
  ϴ' Bk0, Bedge, Bmrg, Bk, Bprim, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq at h
  unfold bandOf ALLOC
  omega

theorem Blpl_ob (r : ℕ) (h : Blpl r = true) :
    (bandOf r = 1 ∨ bandOf r = 5 ∨ bandOf r = 12 ∨ bandOf r = 14) ∧ r ≠ ALLOC := by
  ϴ' Blpl, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq at h
  unfold bandOf ALLOC
  omega

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

/-! ## One piece -/

/-- **One piece of the loop.** -/
theorem lpBody_exec {O : OracleIface} {m₀ : ℕ → ℕ} {h γ A₀ : ℕ} {s e : WPos} {ps : List Pc}
    {cs : Config} {K : ℕ} (X : LpCtx O P W C z m₀ h γ A₀ s e ps)
    (hK : O.κ * (rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) + 1) + 600500 ≤ K)
    (c : Config) (hI : LpI P W H C z σ m₀ A₀ ps cs K c) (hlt : c.nreg 140110 < c.nreg 140100) :
    ∃ c' k, Exec P W (lpBody O.query) c c' k ∧ LpI P W H C z σ m₀ A₀ ps cs K c' ∧
      (A₀ + 1 + 9 * ps.length - c'.nreg 140110) * (K + 2) + k + 2 ≤
        (A₀ + 1 + 9 * ps.length - c.nreg 140110) * (K + 2) ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨hw, E, Og, h08, h34, h100, hrec, hm0, hEA, fr, hbud, j, hj, h110, hB⟩ := hI
  have hjq : j < ps.length := by rw [h110, h100] at hlt; omega
  set pc := ps[j]'hjq with hpc
  have hpcm : pc ∈ ps := List.getElem_mem hjq
  have hok := X.ok pc hpcm
  obtain ⟨r0, r1, r2, r3, r4, r58⟩ := hrec j hjq
  set p := A₀ + 1 + 9 * j with hp
  set L := A₀ + 1 + 9 * ps.length with hL
  have hLp : L - p = (L - (p + 9)) + 9 := by omega
  have hbud' : c.nreg ALLOC + ((L - (p + 9)) * (K + 2) + 9 * (K + 2)) ≤ W := by
    rw [h110, hLp, Nat.add_mul] at hbud; exact hbud
  have hAW : c.nreg ALLOC + 9 * (K + 2) ≤ W := by
    have : 0 ≤ (L - (p + 9)) * (K + 2) := Nat.zero_le _
    omega
  have htk : ps.take (j + 1) = ps.take j ++ [pc] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hjq]; rfl
  -- the keys and the subarc
  have hks := key_range X.hsP X.hs1
  have hke := key_range X.heP X.he1
  have hA := arcSet_pieces X.arc hks hke fun q hq => pcOK_keys (X.ok q hq)
  have hzpc : z ∉ pcSetOf C (Qof P) pc := fun hzp => X.hz (by
    rw [hA]; exact Set.mem_biUnion hpcm hzp)
  -- the load
  obtain ⟨c₁, k₁, e₁, hk₁, q10, v50, v51, v52, v53, v54, v55, v56, v57, v58, f₁⟩ :=
    lpLoad_exec (P := P) c hw E.k1 h110 (by omega)
  have w₁ := e₁.wb_right
  have E₁ := E.frame f₁ Blpl_env
  have Og₁ := Og.keep fun r a b => f₁.1 r (Blpl_org r a b)
  have g1 := E₁.k1
  have kl : ∀ r, LoopR r → r ≠ 140110 → c₁.nreg r = c.nreg r := fun r hr hr' =>
    f₁.1 r (by
      unfold LoopR at hr
      simp only [Blpl, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne] at hr ⊢
      omega)
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := kl _ (by unfold LoopR; simp) (by decide)
  have hm₁ := f₁.2.2.1
  have hB₁ : CandAt P C c₁ 140210 (psSet C (Qof P) (ps.take j)) z σ :=
    hB.keep fun i hi => f₁.1 _ (by simp only [Blpl, Bool.or_eq_false_iff,
      decide_eq_false_iff_not, beq_eq_false_iff_ne]; omega)
  have F₁ : Frame oracleBands c c₁ k₁ := frame_of_frameB f₁ (fun r hr =>
    ⟨oracleBands_mem r (by have := (Blpl_ob r hr).1; omega), (Blpl_ob r hr).2⟩) k₁
  -- the ends of the piece
  have hends := X.arc.ends pc hpcm
  have hxe : pc.s.hgt = 0 ∨ |((chainModel C).pos (Qof P) pc.s).2| < C.radius := by
    rcases hends.1 with h' | h'
    · rw [h']; exact X.hsin
    · exact Or.inl h'
  have hye : pc.e.hgt = 0 ∨ |((chainModel C).pos (Qof P) pc.e).2| < C.radius := by
    rcases hends.2 with h' | h'
    · rw [h']; exact X.hein
    · exact Or.inl h'
  have hW₀ := E.hW
  -- the rest of the invariant after the piece
  have finish : ∀ (c₂ : Config) (k₂ : ℕ), Exec P W (.ifLtN 140254 K1 pieceK0 (pieceK1 O.query))
      c₁ c₂ k₂ → k₂ + 20 ≤ K → WordsBounded W c₂ → ShEnv P W H C z σ c₂ →
      Frame oracleBands c₁ c₂ k₂ → (∀ r, LoopR r → r ≠ ALLOC → c₂.nreg r = c₁.nreg r) →
      CandAt P C c₂ 140210 (psSet C (Qof P) (ps.take j) ∪ pcSetOf C (Qof P) pc) z σ →
      ∃ c' k, Exec P W (lpBody O.query) c c' k ∧ LpI P W H C z σ m₀ A₀ ps cs K c' ∧
        (A₀ + 1 + 9 * ps.length - c'.nreg 140110) * (K + 2) + k + 2 ≤
          (A₀ + 1 + 9 * ps.length - c.nreg 140110) * (K + 2) ∧
        c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
    intro c₂ k₂ e₂ hk₂ w₂ E₂ F₂ kr hB₂
    have ex : Exec P W (lpBody O.query) c c₂ (k₁ + k₂) := by unfold lpBody; exact .seq e₁ e₂
    have F := F₁.trans F₂
    rw [Finset.union_self] at F
    obtain ⟨-, -, fm, -, -, fa, fk⟩ := F
    have k2 : ∀ r, LoopR r → r ≠ ALLOC → r ≠ 140110 → c₂.nreg r = c.nreg r := fun r hr ha hr' =>
      (kr r hr ha).trans (kl r hr hr')
    have n10 : c₂.nreg 140110 = p + 9 := by rw [kr _ (by unfold LoopR; simp) (by decide), q10]
    have Og₂ : OrgOK P C z σ c₂ := Og₁.keep fun r a b =>
      kr r (by unfold LoopR; right; right; right; right; left; exact ⟨a, b⟩)
        (by unfold ALLOC; omega)
    refine ⟨c₂, _, ex, ⟨w₂, E₂, Og₂, ?_, ?_, ?_, ?_, ?_, ?_, FrameNK.step fr (F₁.trans F₂ |>.mono
      (by simp) le_rfl), ?_, j + 1, by omega, by rw [n10]; ring, ?_⟩, ?_, by omega⟩
    · rw [k2 _ (by unfold LoopR; simp) (by decide) (by decide)]; exact h08
    · rw [k2 _ (by unfold LoopR; simp) (by decide) (by decide)]; exact h34
    · rw [k2 _ (by unfold LoopR; simp) (by decide) (by decide)]; exact h100
    · intro i hi
      have := hrec i hi
      have hlt' : ∀ f, f < 9 → A₀ + 1 + 9 * i + f < c.nreg ALLOC := fun f hf => by
        have : 9 * i + 9 ≤ 9 * ps.length := by omega
        omega
      have h0' := hlt' 0 (by norm_num)
      rw [Nat.add_zero] at h0'
      refine ⟨by rw [fm _ h0']; exact this.1, by rw [fm _ (hlt' 1 (by norm_num))]; exact this.2.1,
        by rw [fm _ (hlt' 2 (by norm_num))]; exact this.2.2.1,
        by rw [fm _ (hlt' 3 (by norm_num))]; exact this.2.2.2.1,
        by rw [fm _ (hlt' 4 (by norm_num))]; exact this.2.2.2.2.1, fun hk => ?_⟩
      obtain ⟨b5, b6, b7, b8⟩ := this.2.2.2.2.2 hk
      exact ⟨by rw [fm _ (hlt' 5 (by norm_num))]; exact b5,
        by rw [fm _ (hlt' 6 (by norm_num))]; exact b6,
        by rw [fm _ (hlt' 7 (by norm_num))]; exact b7,
        by rw [fm _ (hlt' 8 (by norm_num))]; exact b8⟩
    · intro a ha
      rw [fm a (by omega)]; exact hm0 a ha
    · omega
    · rw [n10]
      show c₂.nreg ALLOC + (L - (p + 9)) * (K + 2) ≤ W
      have : c₂.nreg ALLOC ≤ c.nreg ALLOC + (k₁ + k₂) := fk
      omega
    · rw [htk, psSet_append]; exact hB₂
    · rw [n10, h110]
      show (L - (p + 9)) * (K + 2) + (k₁ + k₂) + 2 ≤ (L - p) * (K + 2)
      rw [hLp, Nat.add_mul]
      omega
  -- the kind of the piece
  rcases hok.2.2.2.2.1 with hk0 | hk1
  · -- kind 0
    have t : c₁.nreg 140254 < c₁.nreg K1 := by rw [v54, r4, hk0, g1]; omega
    obtain ⟨c₂, k₂, e₂, hk₂, hB₂, f₂⟩ := pieceK0_exec (P := P) (W := W) (H := H) (C := C)
      (z := z) (σ := σ) c₁ w₁ E₁ (x := pc.s) (y := pc.e) (by rw [v50, r0]) (by rw [v51, r1])
      (by rw [v52, r2]) (by rw [v53, r3])
      (by rw [kl _ (by unfold LoopR; simp) (by decide)]; exact h34) hok.1 hok.2.1 hok.2.2.1
      hok.2.2.2.1 (hok.2.2.2.2.2.1 hk0) hxe hye hzpc hB₁ X.hnW (by rw [hA₁]; omega)
    exact finish c₂ _ (.ifLtN_true t e₂) (by omega) e₂.wb_right (E₁.frame f₂ Bk0_env)
      (frame_of_frameB f₂ (fun r hr => ⟨oracleBands_mem r (by have := (Bk0_ob r hr).1; omega),
        (Bk0_ob r hr).2⟩) _) (fun r hr _ => f₂.1 r (Bk0_loop r hr)) hB₂
  · -- kind 1
    have t : ¬ c₁.nreg 140254 < c₁.nreg K1 := by rw [v54, r4, hk1, g1]; omega
    obtain ⟨g, b, hg1, hgΛ, hb, hE, hpw, hx0, hbn, hgran, hs0, he0, h6, hee, hem, hdir, hWk⟩ :=
      hok.2.2.2.2.2.2 hk1
    obtain ⟨r5, r6, r7, r8⟩ := r58 hk1
    have hmA : ∀ a, a < A₀ → c₁.nmem a = m₀ a := fun a ha => by rw [hm₁]; exact hm0 a ha
    obtain ⟨hen, hAt, hCα, hgg, hMpw⟩ := kind1_query hok hk1 X.hR hmA
    have hpwγ : pc.pw ≤ γ := kind1_pw_le_γ X.arc X.hsP X.heP X.hs1 X.he1 X.hwt hpcm hok hk1
    have hcost := query_cost_le (κ := O.κ) hgg (show c₁.nmem (c₁.nmem (c₁.nmem (pc.entry + 2)) + 2)
      ≤ γ by rw [hMpw]; exact hpwγ)
    have hw1 : 1 ≤ pc.pw := by rw [hpw]; exact Nat.one_le_two_pow
    have hpp : pc.s.edge + pc.pw ≤ 2 * C.m + 6 := by rw [hpw]; omega
    have hQn : (Qof P).n = P.n := shear_n _ _
    have hPW : P.n ≤ W := by unfold hostWords at hW₀; omega
    have hnW := X.hnW
    obtain ⟨c₂, k₂, e₂, hk₂, hB₂, F₂, keep₂, E₂⟩ := pieceK1_exec (O := O) X.hV c₁ w₁ E₁
      (by rw [kl _ (by unfold LoopR; simp) (by decide)]; exact h08) hB₁
      (p₀ := pc.s.edge) (en := pc.entry) (x0 := pc.x0) (dir := pc.dir) (w := pc.pw)
      (by rw [v50, r0]) (by rw [v55, r5]) (by rw [v56, r6]) (by rw [v57, r7]) (by rw [v58, r8])
      (by rw [hx0, hpw]; exact hWk) hw1 (by rw [hx0, hpw]; exact hbn) h6 hpp hdir hAt hCα
      Og₁.qk (fun h0 => Og₁.q0 h0 _ fun x hx => block_inC hw1 h6 hpp hx) Og₁.q1 X.hQs hcost
      (by rw [hA₁]; omega) (by omega) (by omega) (by rw [hx0, hpw]; omega)
    have hset : pcSetOf C (Qof P) pc =
        (chainModel C).arcSet (pc.s.edge : ℝ) ((pc.s.edge + pc.pw : ℕ) : ℝ) := by
      unfold pcSetOf
      rw [show pc.s = ⟨pc.s.edge, 0⟩ by rw [← hs0], show pc.e = ⟨pc.e.edge, 0⟩ by rw [← he0],
        key_hgt0, key_hgt0, hee, hpw]
    exact finish c₂ _ (.ifLtN_false t e₂) (by omega) e₂.wb_right E₂ (F₂.mono (subset_refl _)
      (by omega))
      (fun r hr ha => keep₂ r (by unfold LoopR ALLOC at hr; unfold ALLOC at ha; omega)
        (by unfold LoopR ALLOC at hr; unfold ALLOC at ha; omega) (Wk1_loop r hr))
      (by rw [hset]; exact hB₂)

/-! ## The loop -/

theorem Blpi_env (r : ℕ) (h : envR r) : Blpi r = false := by
  unfold envR at h
  simp only [Blpi, K1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at h ⊢
  omega

theorem Blpi_ob (r : ℕ) (h : Blpi r = true) :
    (bandOf r = 1 ∨ bandOf r = 5 ∨ bandOf r = 12 ∨ bandOf r = 14) ∧ r ≠ ALLOC := by
  ϴ' Blpi, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq at h
  unfold bandOf ALLOC
  omega

/-- **The loop over the pieces**: the best first hit on all of them. -/
theorem shLoop_exec {O : OracleIface} {m₀ : ℕ → ℕ} {h γ A₀ : ℕ} {s e : WPos} {ps : List Pc}
    {K : ℕ} (X : LpCtx O P W C z m₀ h γ A₀ s e ps)
    (hK : O.κ * (rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) + 1) + 600500 ≤ K)
    (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c) (Og : OrgOK P C z σ c)
    (h08 : dirOf (c.nreg 140008) = σ) (h100 : c.nreg 140100 = A₀ + 1 + 9 * ps.length)
    (h101 : c.nreg 140101 = A₀) (hrec : Rec9 c.nmem A₀ ps)
    (hm0 : ∀ a, a < A₀ → c.nmem a = m₀ a) (hEA : A₀ + 1 + 9 * ps.length ≤ c.nreg ALLOC)
    (hbud : c.nreg ALLOC + 9 * ps.length * (K + 2) ≤ W) :
    ∃ c' k, Exec P W (shLoop O.query) c c' k ∧ k ≤ 9 * ps.length * (K + 2) + 20 ∧
      CandAt P C c' 140210 (psSet C (Qof P) ps) z σ ∧ Frame oracleBands c c' k ∧
      ShEnv P W H C z σ c' := by
  have hD := E.hD
  have hwf := E.hwf
  have hnW := X.hnW
  obtain ⟨c₁, k₁, e₁, hk₁, v34, v10, v210, f₁⟩ := lpInit_exec (P := P) c hw E.k1 rfl
    hD.2.2.2.1 h101 (by have := hwf.1; omega) (by omega) (by omega)
  have E₁ := E.frame f₁ Blpi_env
  have k₁' := f₁.1
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := k₁' _ (by decide)
  have F₁ : Frame oracleBands c c₁ k₁ := frame_of_frameB f₁ (fun r hr =>
    ⟨oracleBands_mem r (by have := (Blpi_ob r hr).1; omega), (Blpi_ob r hr).2⟩) k₁
  have I₁ : LpI P W H C z σ m₀ A₀ ps c K c₁ := by
    refine ⟨e₁.wb_right, E₁, Og.keep fun r a b => k₁' r (by simp only [Blpi,
      Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]; omega),
      by rw [k₁' _ (by decide)]; exact h08, v34, by rw [k₁' _ (by decide)]; exact h100,
      by rw [f₁.2.2.1]; exact hrec, fun a ha => by rw [f₁.2.2.1]; exact hm0 a ha,
      by rw [hA₁]; exact hEA, FrameNK.step (FrameNK.refl c) F₁, ?_, 0, Nat.zero_le _,
      by rw [v10], ?_⟩
    · rw [hA₁, v10, show A₀ + 1 + 9 * ps.length - (A₀ + 1) = 9 * ps.length by omega]
      exact hbud
    · rw [List.take_zero, psSet_nil]
      have h0 : c₁.nreg (140210 : ℕ) ≠ 1 := by rw [v210]; omega
      exact ⟨by rw [v210]; omega, fun _ => noHit_empty, fun h' => absurd h' h0⟩
  obtain ⟨c₂, k₂, e₂, I₂, hx₂, hk₂, hψ⟩ := whileLtN_potential_lb' (P := P) (W := W)
    (a := 140110) (b := 140100) (body := lpBody O.query) (LpI P W H C z σ m₀ A₀ ps c K)
    (fun c' => (A₀ + 1 + 9 * ps.length - c'.nreg 140110) * (K + 2)) (fun c' => c'.nreg ALLOC)
    (fun _ hI => hI.1) (fun c' hI ht => lpBody_exec X hK c' hI ht) I₁
  obtain ⟨-, E₂, -, -, -, h100₂, -, -, -, fr₂, -, j, hj, h110, hB⟩ := I₂
  have hjq : j = ps.length := by rw [h110, h100₂] at hx₂; omega
  rw [hjq, List.take_length] at hB
  have ex : Exec P W (shLoop O.query) c c₂ (k₁ + k₂) := by unfold shLoop; exact .seq e₁ e₂
  refine ⟨c₂, _, ex, ?_, hB, fr₂.frame ?_, E₂⟩
  · rw [v10, show A₀ + 1 + 9 * ps.length - (A₀ + 1) = 9 * ps.length by omega] at hk₂
    omega
  · rw [hA₁] at hψ; omega

end

end ShootCut

end Chazelle.Core
