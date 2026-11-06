module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.GranPzRam
public import Chazelle.Core.NFLocateSpec
public import Chazelle.Core.ShearInv

/-!
# WP-F, init part 3: correctness of `pzStmt`

`pz_exec`: for a model described at `r50000` and a walk edge `e < n`, code `h ≤ n`, the bit in
`r112` is `1` iff the edge `e` is counted and the position `⟨e, h⟩` has a nonzero parameter.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideE)

@[expose] public section

theorem wr_intIdx : wr Bdir intIdx = true := by decide

theorem pz_exec {P : Polygon} {W : ℕ} {M : Model} (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    (c : Config) (hw : WordsBounded W c) {MD e h : ℕ} (h50 : c.nreg 50000 = MD)
    (hMD : ModelDescAt c.nmem MD (Qof P) M) (h23 : c.nreg 90023 = c.nmem MD)
    (h19 : c.nreg 90019 = 1) (h110 : c.nreg 90110 = e) (h111 : c.nreg 90111 = h)
    (he : e < M.W.n) (hh : h ≤ P.n) (hDW : MD + 6 ≤ W) (hCW : LocChainWF P W c.nmem MD) :
    ∃ c' k, Exec P W pzStmt c c' k ∧ k ≤ 6000 ∧ FrameB Bpz c c' ∧ c'.nreg 90112 ≤ 1 ∧
      (c'.nreg 90112 = 1 ↔ M.counted e ∧ M.param (Qof P) ⟨e, h⟩ ≠ 0) := by
  suffices hh' : ∃ c' k, Exec P W pzStmt c c' k ∧ k ≤ 6000 ∧ c'.nreg 90112 ≤ 1 ∧
      (c'.nreg 90112 = 1 ↔ M.counted e ∧ M.param (Qof P) ⟨e, h⟩ ≠ 0) by
    obtain ⟨c', k, ex, hk, h1, h2⟩ := hh'
    exact ⟨c', k, ex, hk, exec_frameB ex wr_pzStmt, h1, h2⟩
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hgs := goodShear_epsOf hG.2
  have hdh : DistinctHeights (Qof P) := hgs.2.1
  have hW1 : 1 ≤ W := by omega
  -- copy the edge
  have e₀ := Exec.copyN (P := P) hw 50002 90110
  set c₀ : Config := { c with nreg := upd c.nreg 50002 (c.nreg 90110) } with hc₀
  have w₀ : WordsBounded W c₀ := e₀.wb_right
  have r₀ : ∀ r, r ≠ 50002 → c₀.nreg r = c.nreg r := fun r hr => by rw [hc₀]; simp [hr]
  have x₀ : c₀.nreg 50002 = e := by rw [hc₀]; simp [h110]
  have m₀ : c₀.nmem = c.nmem := rfl
  have d₀ : c₀.nreg 50000 = MD := by rw [r₀ _ (by omega), h50]
  rcases hMD with ⟨hk0, H, C, hC, rfl⟩ | ⟨hk1, hbit, rfl⟩
  · -- the chain model
    obtain ⟨hlen, hwf, hHW, hs, hNW⟩ := hCW hk0 H C hC
    obtain ⟨hHost, hP, hs', hm', hT', hb'⟩ := hC
    have hNlen : C.P.n = (H.pts P.n).length := by
      rw [hP, ← hQn]
      show ((H.pts (Qof P).n).map (SymPt.eval (Qof P))).length = _
      rw [List.length_map]
    have hmN := C.m_lt
    have hT := C.topIdx_le
    have hen : e < 2 * C.m + 7 := by simpa [chainModel, C.sideWalk_n] using he
    have t0 : c₀.nreg 90023 < c₀.nreg 90019 := by
      rw [r₀ _ (by omega), r₀ _ (by omega), h23, h19, hk0]; omega
    obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W chHead c₀ c₁ k₁ ∧ k₁ = 16 ∧
        (c₁.nreg 50032 = 1 ∧ c₁.nreg 50060 = c.nmem (MD + 1) ∧ c₁.nreg 50052 = C.s ∧
          c₁.nreg 50053 = C.m ∧ c₁.nreg 50054 = C.topIdx ∧ c₁.nreg 50055 = c.nmem (MD + 5) ∧
          c₁.nreg 50081 = 6 ∧ c₁.nreg 50002 = e ∧ c₁.nreg 90111 = h ∧ c₁.nreg 90019 = 1 ∧
          c₁.nmem = c.nmem) := by
      unfold chHead
      exec_block
      all_goals try omega
      all_goals try (config_simp; omega)
      refine ⟨rfl, ?_⟩
      config_simp
      rw [d₀]
      refine ⟨rfl, hs', hm', hT', rfl, x₀, ?_, ?_, m₀⟩
      · rw [r₀ _ (by omega), h111]
      · rw [r₀ _ (by omega), h19]
    obtain ⟨q32, q60, q52, q53, q54, q55, q81, q02, q111, q19, qm⟩ := q
    have w₁ := e₁.wb_right
    by_cases hsm : e < 6
    · refine ⟨_, _, .seq e₀ (.ifLtN_true t0 (.seq e₁ (.ifLtN_true (by rw [q02, q81]; exact hsm)
        (Exec.constN w₁ 90112 0 (by omega))))), by omega, by simp [upd], ?_⟩
      simp only [upd, ite_true, chainModel]
      constructor
      · intro h; exact absurd h (by omega)
      · rintro ⟨⟨h6, -⟩, -⟩; omega
    obtain ⟨c₂, k₂, e₂, hk₂, q56, q57, r₂⟩ : ∃ c₂ k₂, Exec P W
        (block [.subN 50056 50002 50081, .subN 50057 50056 50053]) c₁ c₂ k₂ ∧ k₂ = 2 ∧
        c₂.nreg 50056 = e - 6 ∧ c₂.nreg 50057 = e - 6 - C.m ∧
        ∀ r, r ≠ 50056 → r ≠ 50057 → c₂.nreg r = c₁.nreg r := by
      exec_block
      refine ⟨rfl, by config_simp; rw [q02, q81], by config_simp; rw [q02, q81, q53],
        fun r h1 h2 => by simp [h1, h2]⟩
    have w₂ := e₂.wb_right
    have p53 : c₂.nreg 50053 = C.m := by rw [r₂ _ (by omega) (by omega), q53]
    have ns : ¬ c₁.nreg 50002 < c₁.nreg 50081 := by rw [q02, q81]; exact hsm
    by_cases hg : e - 6 - C.m < C.m
    · have hi : e - 6 < 2 * C.m := by omega
      have f₂ := exec_frameB e₂ (B := Bl [50056, 50057]) (by decide)
      have hH₂ : HostAt c₂.nmem (c.nmem (MD + 1)) H := by rw [f₂.2.2.1, qm]; exact hHost
      obtain ⟨c₃, k₃, e₃, hk₃, -, sp₁, sp₂, hsp₁, hsp₂, a₃, b₃, l₁, l₂⟩ := chPts_exec (P := P) hG
        hW c₂ w₂ hH₂ hwf hHW (by rw [← hNlen]; exact hNW) (by rw [← hNlen]; exact hs)
        (by rw [← hNlen]; exact hmN) hT hi (by rw [r₂ _ (by omega) (by omega), q32])
        (by rw [r₂ _ (by omega) (by omega), q60]) (by rw [r₂ _ (by omega) (by omega), q52]) p53
        (by rw [r₂ _ (by omega) (by omega), q54]) (by rw [r₂ _ (by omega) (by omega), q55]) q56
      have F₃ := exec_frameB e₃ wr_chPts_fine
      have g₃ : ∀ r, Bpts r = false → c₃.nreg r = c₂.nreg r := F₃.1
      have c32 : c₃.nreg 50032 = 1 := by
        rw [g₃ _ (by decide), r₂ _ (by omega) (by omega), q32]
      obtain ⟨c₄, k₄, e₄, hk₄, v₄, r₄, m₄⟩ := hvS_exec (P := P) (dst := 90113) c₃ e₃.wb_right
        c32 a₃
      obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅, m₅⟩ := hvS_exec (P := P) (dst := 90114) c₄ e₄.wb_right
        (by rw [r₄ _ (by omega), c32])
        (symPtIn_copy b₃ (r₄ _ (by omega)) (r₄ _ (by omega)) (r₄ _ (by omega)))
      have h111₅ : c₅.nreg 90111 = h := by
        rw [r₅ _ (by omega), r₄ _ (by omega), g₃ _ (by decide), r₂ _ (by omega) (by omega),
          q111]
      have h19₅ : c₅.nreg 90019 = 1 := by
        rw [r₅ _ (by omega), r₄ _ (by omega), g₃ _ (by decide), r₂ _ (by omega) (by omega),
          q19]
      obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W (block [.constN 90112 0,
          .subN 90115 90111 90019]) c₅ c₆ k₆ ∧ k₆ = 2 ∧ (c₆.nreg 90112 = 0 ∧
          c₆.nreg 90115 = h - 1 ∧ c₆.nreg 90111 = h ∧ c₆.nreg 90113 = hv sp₁ ∧
          c₆.nreg 90114 = hv sp₂ ∧ c₆.nreg 90019 = 1) := by
        have hw₅ := e₅.wb_right
        exec_block
        · omega
        · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp
          · rw [h111₅, h19₅]
          · exact h111₅
          · rw [r₅ _ (by omega), v₄]
          · exact v₅
          · exact h19₅
      obtain ⟨q112, q115, q111', q113, q114, q19'⟩ := q
      obtain ⟨c₇, k₇, e₇, hk₇, b₇, i₇, -, -⟩ := tail3_exec (P := P) c₆ e₆.wb_right hW1
        90113 90114 90115 90113 q19' q112
      refine ⟨c₇, _, .seq e₀ (.ifLtN_true t0 (.seq e₁ (.ifLtN_false ns (.seq e₂
        (.ifLtN_true (by rw [q57, p53]; exact hg)
          (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))))))), ?_, b₇, ?_⟩
      · 
        omega
      rw [i₇, q111', q113, q114, q115]
      -- the mathematics
      have hS : (if c.nmem (MD + 5) = 1 then C.topIdx else 2 * C.m - C.topIdx) =
          C.sideS C.sideBeta := by
        unfold Chain.sideS
        by_cases hb : C.sideBeta = true
        · rw [ite_eq_left (hb'.2 hb), ite_eq_left hb]
        · rw [ite_eq_right (mt hb'.1 hb), ite_eq_right hb]
      obtain ⟨i1, i2⟩ := sideIdx_pair C (e - 6)
      rw [hS, ← hNlen, ← i1] at hsp₁
      rw [hS, ← hNlen, ← i2] at hsp₂
      have v1 := chain_vertex_host C hP _ (by rw [hQn]; exact hsp₁)
      have v2 := chain_vertex_host C hP _ (by rw [hQn]; exact hsp₂)
      have key := pz_chain C hdh hi (h := h) (by rw [hQn]; exact hh) v1 v2
        (by rw [hQn]; exact l₁) (by rw [hQn]; exact l₂)
      rw [show e - 6 + 6 = e by omega] at key
      rw [key]
      simp only [chainModel]
      constructor
      · intro h'; exact ⟨⟨by omega, by omega⟩, h'⟩
      · intro h'; exact h'.2
    · have hlast : e = 2 * C.m + 6 := by omega
      refine ⟨_, _, .seq e₀ (.ifLtN_true t0 (.seq e₁ (.ifLtN_false ns (.seq e₂
        (.ifLtN_false (by rw [q57, p53]; exact hg) (Exec.constN w₂ 90112 0 (by omega))))))),
        by omega, by simp [upd], ?_⟩
      simp only [upd, ite_true, chainModel]
      constructor
      · intro h; exact absurd h (by omega)
      · rintro ⟨⟨-, h6⟩, -⟩; omega
  · -- the interior model
    have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
    have hen : e < P.n := by
      have := interiorWalk_n (Qof P)
      simp only [interiorModel] at he
      rw [this, hQn] at he
      exact he
    have t0 : ¬ c₀.nreg 90023 < c₀.nreg 90019 := by
      rw [r₀ _ (by omega), r₀ _ (by omega), h23, h19, hk1]; omega
    obtain ⟨c₁, k₁, e₁, hk₁, i41, -⟩ := intIdx_exec (P := P) hW c₀ w₀ (by rw [x₀]; exact hen)
      (by rw [d₀]; omega)
    have F₁ := exec_frameB e₁ wr_intIdx
    obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W (block [.constN 90112 0,
        .subN 90115 90111 90019]) c₁ c₂ k₂ ∧ k₂ = 2 ∧ (c₂.nreg 90112 = 0 ∧
        c₂.nreg 90115 = h - 1 ∧ c₂.nreg 90111 = h ∧ c₂.nreg 50041 = c₁.nreg 50041 ∧
        c₂.nreg 90019 = 1) := by
      have hw₁ := e₁.wb_right
      have a : c₁.nreg 90111 = h := by
        rw [F₁.1 _ (by decide), r₀ _ (by omega), h111]
      have b : c₁.nreg 90019 = 1 := by rw [F₁.1 _ (by decide), r₀ _ (by omega), h19]
      exec_block
      · omega
      · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp
        · rw [a, b]
        · exact a
        · exact b
    obtain ⟨q112, q115, q111', q41, q19'⟩ := q
    obtain ⟨c₃, k₃, e₃, hk₃, b₃, i₃, -, -⟩ := tail3_exec (P := P) c₂ e₂.wb_right hW1
      90115 50041 90115 50041 q19' q112
    refine ⟨c₃, _, .seq e₀ (.ifLtN_false t0 (.seq e₁ (.seq e₂ e₃))), by omega, b₃, ?_⟩
    rw [i₃, q111', q115, q41, i41, x₀, d₀, m₀]
    have key := pz_int hQ hdh (e := e) (h := h) (by rw [hQn]; exact hen) (by rw [hQn]; exact hh)
    have hwv : OutWalk.wv (OutWalk.revOf (Qof P)) (Qof P).n e =
        (if c.nmem (MD + 1) = 1 then e else P.n - 1 - e) := by
      unfold OutWalk.wv OutWalk.revOf
      rw [hQn]
      by_cases hl : Mountain.LeftInside (Qof P)
      · rw [ite_eq_left (hbit.2 hl)]; simp [hl]
      · rw [ite_eq_right (fun h' => hl (hbit.1 h'))]; simp [hl]
    rw [hwv] at key
    rw [key]
    simp only [interiorModel, true_and, and_self]
end

end Gran

end Chazelle.Core
