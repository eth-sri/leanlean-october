module

public import Chazelle.Core.GranMain
public import Chazelle.Core.NFDecompMain
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 4000000

/-!
# WP-F: granularity enforcement (`GranularizeSpec`)

The procedure `granStmt sB sD`: read the number `K` of chords; if `K = 0` the chord list is
empty, else run the worklist algorithm (`mainStmt`: initialisation, removals of
light chords, output of the surviving chords); then build the normal form of the chord list
(`sB`, `BuildNFSpec`) and decompose it (`sD`, `DecompSpec`).  `granularize` proves
`GranularizeSpec` from the two specifications; `granularize'` uses the proved `decomp`.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The empty chord list. -/
def emptyS : Stmt := block [.constN 90095 0, .constN 90028 0]

/-- **Granularity enforcement.** -/
def granStmt (sB sD : Stmt) : Stmt :=
  .seq (block [.constN 90019 1, .loadN 90010 90001])
    (.seq (.ifLtN 90010 90019 emptyS mainStmt) (bdStmt sB sD))

theorem GF.frame {c c' : Config} {k : ℕ} (h : GF (c.nreg ALLOC) c c' k) :
    Frame granBands c c' k := h

theorem gran_ne_alloc : bandOf ALLOC ∉ ({bGran} : Finset ℕ) := by decide

theorem band9_not {r : ℕ} (h1 : 90000 ≤ r) (h2 : r < 100000) : ¬ bandOf r ∉ ({bGran} : Finset ℕ) := by
  ufs bandOf bGran; omega

theorem pre_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (block [.constN 90019 1, .loadN 90010 90001]) c c' k ∧ k = 2 ∧
      c'.nreg 90019 = 1 ∧ c'.nreg 90010 = c.nmem (c.nreg 90001) ∧
      (∀ r, r ≠ 90019 → r ≠ 90010 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  · exact hW
  · refine ⟨rfl, ?_, ?_, fun r x1 x2 => ?_, rfl, rfl, rfl, rfl⟩ <;>
      simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

theorem empty_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W emptyS c c' k ∧ k = 2 ∧
      c'.nreg 90095 = 0 ∧ c'.nreg 90028 = 0 ∧
      (∀ r, r ≠ 90095 → r ≠ 90028 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold emptyS
  exec_block
  · omega
  · omega
  · refine ⟨rfl, ?_, ?_, fun r x1 x2 => ?_, rfl, rfl, rfl, rfl⟩ <;>
      simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

theorem granular_empty {M : Model} {F : Set (Set Point)} {γ : ℕ} (hF : F = ∅)
    (h : M.Semigranular F γ) : M.Granular F γ := by
  refine ⟨h, ?_⟩
  have : Merge.ContractionCondIn M.D M.weight F γ := by
    rw [Merge.contractionCondIn_iff]
    intro c hc
    have := hc.1
    rw [hF] at this
    exact this
  exact this

/-- **WP-F: granularity enforcement**, from the construction of normal forms and the
decomposition. -/
theorem granularize (hB : BuildNFSpec) (hD : DecompSpec) : GranularizeSpec := by
  obtain ⟨sB, κB, hsB⟩ := buildOK_of hB
  obtain ⟨sD, κD, hsD⟩ := decompOK_of hD
  refine ⟨granStmt sB sD, κGran κB κD, ?_⟩
  intro P W c hw ⟨hG, hWh, hD1, hwf, M, N, hMD, hGM, hNW, hNF, hdeg, hsemi⟩ hroom
  beta_reduce at hroom ⊢
  have e0 : rd c bGran 0 = c.nreg 90000 := rfl
  have e1 : rd c bGran 1 = c.nreg 90001 := rfl
  have e2 : rd c bGran 2 = c.nreg 90002 := rfl
  have e3 : rd c bGran 3 = c.nreg 90003 := rfl
  rw [e0] at hwf hMD
  rw [e1] at hNW hroom
  rw [e2] at hdeg hroom
  rw [e3] at hsemi
  rw [e0, e1, e2, e3]
  set MD := c.nreg 90000 with hMDd
  set NFH := c.nreg 90001 with hNFHd
  set D := c.nreg 90002 with hDd
  set γ := c.nreg 90003 with hγd
  have hK : c.nmem NFH = N.nChords := hNW.nfAt.1
  rw [hK] at hroom ⊢
  set K := N.nChords with hKd
  set X := K * (Nat.clog 2 K + 1) + 1 with hXd
  have hX1 : 1 ≤ X := by omega
  have hκ : 12 + κB + κD * (D + 1) ≤ κGran κB κD D := by
    ufnl κGran
  have hκX : κGran κB κD D ≤ κGran κB κD D * X := Nat.le_mul_of_pos_right _ hX1
  -- the post-condition, from the result of `bdStmt`
  have post : ∀ (c' : Config) (L : List (ℕ × ℕ × ℕ)) (N' : NF),
      lset M (Qof P) L ⊆ N.F M (Qof P) → M.DegLe (lset M (Qof P) L) D →
      M.Granular (lset M (Qof P) L) γ → c.nreg ALLOC ≤ c'.nreg 90004 →
      NFWithin c'.nmem (c'.nreg 90004) (c'.nreg ALLOC) N' → IsNF M (Qof P) N' →
      N'.F M (Qof P) = lset M (Qof P) L → IsDecomp N' (decDepth D N'.nChords) →
      ∀ M₀ N₀, ModelDescAt c.nmem MD (Qof P) M₀ → NFAt c.nmem NFH N₀ →
        ∃ N'', c.nreg ALLOC ≤ rd c' bGran 4 ∧
          NFWithin c'.nmem (rd c' bGran 4) (c'.nreg ALLOC) N'' ∧
          N''.F M₀ (Qof P) ⊆ N₀.F M₀ (Qof P) ∧ IsCanonicalNF M₀ (Qof P) N'' γ D := by
    intro c' L N' hsub hdg hgr hA hW hN hF hdec M₀ N₀ hM₀ hN₀
    have := NFLoc.modelDesc_unique hMD hM₀
    subst this
    have hch := NFLoc.nfAt_chords_eq hNW.nfAt hN₀
    refine ⟨N', hA, hW, ?_, hN, ?_, ?_, hdec⟩
    · rwx [F_congr hch, hF]
    · rwx [hF]
    · rwx [hF]
  obtain ⟨c₁, k₁, e₁, hk₁, p19, p10, R₁, rr₁, m₁, rm₁, o₁⟩ :=
    pre_exec (P := P) c hw (le_trans (by ufo hostWords) hWh)
  have w₁ := e₁.wb_right
  have A₁ : c₁.nreg ALLOC = c.nreg ALLOC := R₁ _ (by decide) (by decide)
  have F₁ : Frame {bGran} c c₁ k₁ := frame_of (fun r hr => R₁ r
    (fun h => band9_not (by omega) (by omega) hr) (fun h => band9_not (by omega) (by omega) hr))
    rr₁ m₁ rm₁ o₁ gran_ne_alloc
  rw [← hNFHd, hK] at p10
  have q0 : c₁.nreg 90000 = MD := R₁ _ (by decide) (by decide)
  have q1 : c₁.nreg 90001 = NFH := R₁ _ (by decide) (by decide)
  have q2 : c₁.nreg 90002 = D := R₁ _ (by decide) (by decide)
  have q3 : c₁.nreg 90003 = γ := R₁ _ (by decide) (by decide)
  rcases Nat.lt_or_ge K 1 with hK0 | hK1
  · -- no chords
    have hnil : N.chords = [] :=
      List.eq_nil_of_length_eq_zero (by have h' : N.chords.length = K := rfl; omega)
    have hFe : N.F M (Qof P) = ∅ := by
      ext x; simp [NF.F, hnil]
    have hl : lset M (Qof P) [] = N.F M (Qof P) := by
      rw [hFe]; ext x; simp [lset]
    obtain ⟨c₂, k₂, e₂, hk₂, s95, s28, R₂, rr₂, m₂, rm₂, o₂⟩ := empty_exec (P := P) c₁ w₁
    have F₂ : Frame {bGran} c₁ c₂ k₂ := frame_of (fun r hr => R₂ r
      (fun h => band9_not (by omega) (by omega) hr) (fun h => band9_not (by omega) (by omega) hr))
      rr₂ m₂ rm₂ o₂ gran_ne_alloc
    have A₂ : c₂.nreg ALLOC = c.nreg ALLOC := by rw [R₂ _ (by decide) (by decide), A₁]
    have hm₂ : c₂.nmem = c.nmem := by rw [m₂, m₁]
    obtain ⟨c₃, k₃, e₃, hk₃, ⟨N', hA', hW', hN', hF', hdec'⟩, F₃⟩ := bd_exec (L := []) hsB hsD
      e₂.wb_right hG hWh (by rw [R₂ _ (by decide) (by decide), q0])
      (by rw [R₂ _ (by decide) (by decide), q2]) s28 s95 (by rwx [A₂, hm₂])
      (by rwx [hm₂]) hGM (fun i hi => by simp at hi) (by rws [A₂])
      ⟨by rw [show {c | ∃ x ∈ ([] : List (ℕ × ℕ × ℕ)), c = (recOf x).toSet M (Qof P)} =
          N.F M (Qof P) from hl]; exact hNF.1, List.nodup_nil, fun x hx => by simp at hx,
        fun x hx => by simp at hx⟩
      (by rwx [hl])
      (by rw [A₂]; ufs costBD; omega)
    have e₁₂ : Exec P W (.ifLtN 90010 90019 emptyS mainStmt) c₁ c₂ (k₂ + 1) :=
      .ifLtN_true (by rwo [p10, p19]) e₂
    refine ⟨c₃, _, .seq e₁ (.seq e₁₂ e₃), ?_, ?_, ?_⟩
    · unfold costBD at hk₃; sio at hk₃
    · rw [A₂] at hA'
      exact post c₃ [] N' (by rw [hl]) (by rwx [hl])
        (by rw [hl]; exact granular_empty hFe hsemi) hA' hW' hN' hF' hdec'
    · exact ((F₁.trans (F₂.mono (le_refl _) (by omega : k₂ ≤ k₂ + 1))).trans F₃).mono
        (by decide) (by omega)
  · -- the worklist
    have hne : (N.F M (Qof P)).Nonempty :=
      ⟨cs M (Qof P) N 0, mem_F_iff.2 ⟨0, by omega, rfl⟩⟩
    have hWA := walkAx_of_goodModel hGM
    have hAr := arcs_le hNF hWA hne
    have hRr := nRegions_eq hNF hWA
    have hct := cost_total (κB := κB) (κD := κD) (D := D) hAr hRr (le_refl K)
    rw [← hXd] at hct
    obtain ⟨c₂, k₂, L, e₂, hk₂, s00, s02, s95, hLK, hlist, hLB, hok, hsub, hdg, hgr, G₂⟩ :=
      main_exec (P := P) w₁ q0 q1 q2 q3 hG hWh (by rwx [A₁, m₁])
        (by rwx [m₁]) hGM (by rwx [A₁, m₁]) hNF hne hdeg hsemi
        (by rwnl [A₁])
    have hmono : costBD κB κD D L.length ≤ costBD κB κD D K := costBD_mono hLK
    have A₂ := G₂.2.2.2.2.2.2
    have hlow : ∀ a, a < c.nreg ALLOC → c₂.nmem a = c.nmem a := fun a ha => by
      rw [G₂.2.2.1 a (by omega), m₁]
    obtain ⟨hMD₂, hwf₂⟩ := desc_agree' hwf hMD hlow
    obtain ⟨c₃, k₃, e₃, hk₃, ⟨N', hA', hW', hN', hF', hdec'⟩, F₃⟩ := bd_exec hsB hsD
      e₂.wb_right hG hWh s00 s02 rfl s95 (hwf₂.mono (by rw [← A₁]; exact G₂.2.2.2.2.2.1))
      hMD₂ hGM hlist hLB hok hdg (by rwnl [A₁] at A₂)
    have e₁₂ : Exec P W (.ifLtN 90010 90019 emptyS mainStmt) c₁ c₂ (k₂ + 2) :=
      .ifLtN_false (by rwo [p10, p19]) e₂
    have hA₂ : c.nreg ALLOC ≤ c₂.nreg ALLOC := by rw [← A₁]; exact G₂.2.2.2.2.2.1
    refine ⟨c₃, _, .seq e₁ (.seq e₁₂ e₃), ?_, ?_, ?_⟩
    · omega
    · exact post c₃ L N' hsub hdg hgr (le_trans hA₂ hA') hW' hN' hF' hdec'
    · have F₂ : Frame granBands c₁ c₂ k₂ := GF.frame G₂
      exact ((F₁.trans (F₂.mono (le_refl _) (by omega : k₂ ≤ k₂ + 2))).trans F₃).mono
        (by decide) (by omega)

/-- **WP-F: granularity enforcement**, from the construction of normal forms alone. -/
theorem granularize' (hB : BuildNFSpec) : GranularizeSpec := granularize hB DecR.decomp

end

end Gran

end Chazelle.Core
