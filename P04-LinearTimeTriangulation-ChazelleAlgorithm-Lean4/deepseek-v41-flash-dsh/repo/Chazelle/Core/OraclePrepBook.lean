module

public import Chazelle.Golf

public import Chazelle.Core.OraclePrepPhB2
public import Chazelle.Core.OracleQueryMeets

/-!
# Lemma 3.6 (WP-H), preprocessing part 33: the clusters of the book

`ClFacts`: the cluster facts of the structure (flags of `D*` at `FL`, labels at `LAB`, the
parameter `k`).  `trivS`: when there is no chord (`K = 0`, so at most `8` nodes), every node is in
`D*` and `k = 2`.  `bookS`: `mapS; clStage` when `0 < K`, else `trivS`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleBook OracleBook.BookData

@[expose] public section

/-- **The cluster facts.** -/
structure ClFacts (m : ℕ → ℕ) (B : BookData) (FL LAB k : ℕ) : Prop where
  k_pos : 1 ≤ k
  μ_le : B.N ≤ k ^ 3
  k_min : k = 1 ∨ (k - 1) ^ 3 < B.N
  card : ((Finset.range B.N).filter fun v => m (FL + v) = 1).card ≤ 7 * k ^ 2
  hlab : ∀ u v (w : (OracleQ.bookGraph B).Walk u v), (∀ x ∈ w.support, m (FL + x) ≠ 1) →
    m (LAB + u) = m (LAB + v)
  clus : ∀ l, ((Finset.range B.N).filter fun v => m (FL + v) ≠ 1 ∧ m (LAB + v) = l).card ≤ k ^ 2

theorem ClFacts.mono {m m' : ℕ → ℕ} {B : BookData} {FL LAB k X : ℕ} (h : ClFacts m B FL LAB k)
    (hX : ∀ a, a < X → m' a = m a) (hFL : FL + B.N ≤ X) (hLAB : LAB + B.N ≤ X) :
    ClFacts m' B FL LAB k where
  k_pos := h.k_pos
  μ_le := h.μ_le
  k_min := h.k_min
  card := by
    refine le_trans (le_of_eq ?_) h.card
    congr 1; ext v
    ϴ Finset.mem_filter, Finset.mem_range
    constructor
    · rintro ⟨hv, e⟩; exact ⟨hv, by rw [← hX _ (⋄)]; exact e⟩
    · rintro ⟨hv, e⟩; exact ⟨hv, by rw [hX _ (⋄)]; exact e⟩
  hlab u v w hw := by
    Ξ hX _ (by have := u.2; omega), hX _ (by have := v.2; omega)
    exact h.hlab u v w fun x hx => by
      have := hw x hx; rwa [hX _ (by have := x.2; omega)] at this
  clus l := by
    refine le_trans (le_of_eq ?_) (h.clus l)
    congr 1; ext v
    ϴ Finset.mem_filter, Finset.mem_range
    constructor
    · rintro ⟨hv, e1, e2⟩
      exact ⟨hv, by rw [← hX _ (⋄)]; exact e1, by rw [← hX _ (⋄)]; exact e2⟩
    · rintro ⟨hv, e1, e2⟩
      exact ⟨hv, by rw [hX _ (⋄)]; exact e1, by rw [hX _ (⋄)]; exact e2⟩

/-- The trivial cluster facts: every node in `D*`, `k = 2` (at most `8` nodes, at least `2`). -/
theorem ClFacts.triv {m : ℕ → ℕ} {B : BookData} {FL LAB : ℕ} (h2 : 2 ≤ B.N) (h8 : B.N ≤ 8)
    (hfl : ∀ v, v < B.N → m (FL + v) = 1) : ClFacts m B FL LAB 2 where
  k_pos := ⊛
  μ_le := by norm_num; omega
  k_min := Or.inr (by norm_num; omega)
  card := by
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp; omega
  hlab u v w hw := absurd (hfl u u.2) (hw u w.start_mem_support)
  clus l := by
    Ξ Finset.card_eq_zero.2
    · exact Nat.zero_le _
    · ext v
      ϴ Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and
      intro hv e; exact absurd (hfl v hv) e

/-! ## The trivial decomposition -/

/-- The fill body: address `base + v`, value in `rv0`. -/
def fillBody (rb rv0 : ℕ) : Stmt := block [.addN 60094 rb 60093, .copyN 60095 rv0]

/-- **The trivial decomposition**: `FL[v] := 1`, `LAB[v] := 0`, `k := 2`. -/
def trivS : Stmt :=
  .seq (block [.copyN 130004 9999, .addN 9999 9999 60034, .copyN 130005 9999,
      .addN 9999 9999 60034, .constN 60090 2])
    (.seq (scatS 60093 60034 120011 60094 60095 (fillBody 130004 120011))
      (scatS 60093 60034 120011 60094 60095 (fillBody 130005 120012)))

theorem fill_exec {P : Polygon} {W : ℕ} {rb rv0 : ℕ} (hrb : rb = 130004 ∨ rb = 130005)
    (hrv : rv0 = 120011 ∨ rv0 = 120012) {c : Config} (hw : WordsBounded W c) {μ b v0 : ℕ}
    (hμ : c.nreg 60034 = μ) (h1 : c.nreg 120011 = 1) (hb : c.nreg rb = b) (hv : c.nreg rv0 = v0)
    (hW : b + μ ≤ W) :
    ∃ c' k, Exec P W (scatS 60093 60034 120011 60094 60095 (fillBody rb rv0)) c c' k ∧
      k ≤ μ * 6 + 3 ∧ (∀ r, r ≠ 60093 → r ≠ 60094 → r ≠ 60095 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = scat c.nmem (fun i => b + i) (fun _ => v0) μ ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, r', rr', mm, rm, o, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60093) (rn := 60034) (r1 := 120011) (ra := 60094) (rv := 60095) (body := fillBody rb rv0)
    (B := fun r => decide (r = 60094 ∨ r = 60095)) (⌖) (⌖) (⌖) (⌖)
    (⌖) (fun d => d.nreg rb = b ∧ d.nreg rv0 = v0) 0
    (fun d d' hJ hr _ => ⟨by rw [hr rb (by rcases hrb with rfl | rfl <;> decide)
        (by rcases hrb with rfl | rfl <;> decide)]; exact hJ.1,
      by rw [hr rv0 (by rcases hrv with rfl | rfl <;> decide)
        (by rcases hrv with rfl | rfl <;> decide)]; exact hJ.2⟩)
    (n := μ) (κ := 2) (fun i => b + i) (fun _ => v0) (fun i _ => Nat.zero_le _)
    (fun i d hi hJ hwd hri => by
      obtain ⟨d', k, e, hk, v1, v2⟩ : ∃ d' k, Exec P W (fillBody rb rv0) d d' k ∧ k = 2 ∧
          d'.nreg 60094 = b + i ∧ d'.nreg 60095 = v0 := by
        unfold fillBody
        rcases hrb with rfl | rfl <;> rcases hrv with rfl | rfl <;>
        · exec_block
          · rw [hJ.1, hri]; omega
          · exact ⟨rfl, by config_simp; rw [hJ.1, hri],
              by config_simp; exact hJ.2⟩
      have hwr : wr (fun r => decide (r = 60094 ∨ r = 60095)) (fillBody rb rv0) = true := by
        rcases hrb with rfl | rfl <;> rcases hrv with rfl | rfl <;> decide
      exact ⟨d', k, e, ⋄, exec_frameB e hwr, v1, v2⟩)
    hw ⟨hb, hv⟩ hμ h1 (⋄)
  refine ⟨c', k, ex, ⊞, fun r a b' d => r' r (by simp; omega) a, ?_, mm, rm, o⟩
  exact funext fun r => exec_rframeS ex (B := fun _ => false)
    (by rcases hrb with rfl | rfl <;> rcases hrv with rfl | rfl <;> decide) r rfl

theorem trivS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {μ A : ℕ}
    (hμ : c.nreg 60034 = μ) (h1 : c.nreg 120011 = 1) (h0 : c.nreg 120012 = 0)
    (hAl : c.nreg 9999 = A) (hW : A + 2 * μ ≤ W) (h2W : 2 ≤ W) :
    ∃ c' k, Exec P W trivS c c' k ∧ k ≤ 12 * μ + 12 ∧ c'.nreg 130004 = A ∧
      c'.nreg 130005 = A + μ ∧ c'.nreg 60090 = 2 ∧ c'.nreg 9999 = A + 2 * μ ∧
      (∀ v, v < μ → c'.nmem (A + v) = 1) ∧ (∀ a, a < A → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 130004 → r ≠ 130005 → r ≠ 9999 → r ≠ 60090 → r ≠ 60093 → r ≠ 60094 →
        r ≠ 60095 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a4, a5, a9, a90, R₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 130004 9999, .addN 9999 9999 60034, .copyN 130005 9999,
        .addN 9999 9999 60034, .constN 60090 2]) c c₁ k₁ ∧ k₁ = 5 ∧
      c₁.nreg 130004 = A ∧ c₁.nreg 130005 = A + μ ∧ c₁.nreg 9999 = A + 2 * μ ∧
      c₁.nreg 60090 = 2 ∧
      (∀ r, r ≠ 130004 → r ≠ 130005 → r ≠ 9999 → r ≠ 60090 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals first
      | (config_simp; rw [hAl, hμ]; omega)
      | (config_simp; omega)
      | omega
      | skip
    · refine ⟨rfl, by config_simp; exact hAl, by config_simp; rw [hAl, hμ],
        by config_simp; rw [hAl, hμ]; ring, by config_simp, fun r a b d e => ?_, rfl, rfl, rfl, rfl⟩
      config_simp; simp only [upd_apply, a, b, d, e, ite_false]
  obtain ⟨c₂, k₂, e₂, hk₂, R₂, rr₂, m₂, rm₂, o₂⟩ := fill_exec (P := P) (rb := 130004) (rv0 := 120011)
    (Or.inl rfl) (Or.inl rfl) e₁.wb_right (by rw [R₁ _ (by decide) (by decide) (by decide)
      (by decide), hμ]) (by rw [R₁ _ (by decide) (by decide) (by decide) (by decide), h1]) a4
    (by rw [R₁ _ (by decide) (by decide) (by decide) (by decide), h1]) (by omega)
  obtain ⟨c₃, k₃, e₃, hk₃, R₃, rr₃, m₃, rm₃, o₃⟩ := fill_exec (P := P) (rb := 130005) (rv0 := 120012)
    (Or.inr rfl) (Or.inr rfl) e₂.wb_right (by rw [R₂ _ (by decide) (by decide) (by decide),
      R₁ _ (by decide) (by decide) (by decide) (by decide), hμ])
    (by rw [R₂ _ (by decide) (by decide) (by decide), R₁ _ (by decide) (by decide) (by decide)
      (by decide), h1]) (by rw [R₂ _ (by decide) (by decide) (by decide), a5])
    (by rw [R₂ _ (by decide) (by decide) (by decide), R₁ _ (by decide) (by decide) (by decide)
      (by decide), h0]) (by omega)
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, ?_, ?_, ?_, ?_, fun v hv => ?_, fun a ha => ?_,
    fun r a b d e f g h => ?_, by rw [rr₃, rr₂, rr₁], by rw [rm₃, rm₂, rm₁], by rw [o₃, o₂, o₁]⟩
  · rw [R₃ _ (by decide) (by decide) (by decide), R₂ _ (by decide) (by decide) (by decide), a4]
  · rw [R₃ _ (by decide) (by decide) (by decide), R₂ _ (by decide) (by decide) (by decide), a5]
  · rw [R₃ _ (by decide) (by decide) (by decide), R₂ _ (by decide) (by decide) (by decide), a90]
  · rw [R₃ _ (by decide) (by decide) (by decide), R₂ _ (by decide) (by decide) (by decide), a9]
  · rw [m₃, scat_other (fun i _ => by omega), m₂]
    exact scat_at (g := fun i => A + i) hv (fun j _ hj => by omega)
  · rw [m₃, scat_below (fun i _ => by omega) ha, m₂, scat_below (fun i _ => by omega) ha, m₁]
  · rw [R₃ r f g h, R₂ r f g h, R₁ r a b d e]

/-! ## The clusters of the book -/

/-- **The clusters of the book**: the planar map and the cluster decomposition when there are
chords, the trivial decomposition otherwise. -/
def bookS : Stmt := .ifLtN 120012 120039 (.seq mapS clStage) trivS

/-- The bands of `bookS`. -/
def kBands : Finset ℕ := {bSort, bDecomp, bOPrep, bCluster}


theorem bookS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hG : GoodEnv P)
    {C : Chain} {N : NF} (hCQ : C.P = Qof P) {γ : ℕ}
    (hcan : IsCanonicalNF (chainModel C) (Qof P) N γ 4)
    {B : BookData} (hgok : OracleQ.GraphOK C (Qof P) N B) (hBN : B.N = N.arcs.length + 3)
    {CH1 CH2 A₅ : ℕ} (h1r : c.nreg 60001 = CH1) (h2r : c.nreg 60002 = CH2)
    (hI : c.nreg 60008 = B.I.length) (hμ : c.nreg 60034 = B.N) (hE : c.nreg 60037 = B.E)
    (hone : c.nreg 120011 = 1) (hzero : c.nreg 120012 = 0) (htwo : c.nreg 120048 = 2)
    (hK : c.nreg 120039 = N.chords.length) (hAl : c.nreg 9999 = A₅)
    (hP : PairsAt c.nmem CH1 CH2 (B.I ++ B.O)) (hC1 : CH1 + (B.I ++ B.O).length ≤ A₅)
    (hC2 : CH2 + (B.I ++ B.O).length ≤ A₅)
    (hroom : A₅ + 10 * B.E + SortR.sortCost 20 (2 * B.E) + 3 * B.N + 3 + clCost B.N B.E ≤ W)
    (hPW : P.n + 3 ≤ W) (hNW : 8 * B.N + 8 ≤ W) :
    ∃ c' k, Exec P W bookS c c' k ∧
      k ≤ 400 * B.E + SortR.sortCost 20 (2 * B.E) + 30 * B.N + 150 + clCost B.N B.E ∧
      GF kBands A₅ c c' ∧ (∀ r, 120010 ≤ r → r ≤ 120049 → c'.nreg r = c.nreg r) ∧
      c'.nreg 60034 = B.N ∧ A₅ ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₅ + 10 * B.E + SortR.sortCost 20 (2 * B.E) + 3 * B.N + 3 + k ∧
      A₅ ≤ c'.nreg 130004 ∧ A₅ ≤ c'.nreg 130005 ∧ c'.nreg 130004 + B.N ≤ c'.nreg ALLOC ∧
      c'.nreg 130005 + B.N ≤ c'.nreg ALLOC ∧
      ClFacts c'.nmem B (c'.nreg 130004) (c'.nreg 130005) (c'.nreg 60090) := by
  have hAL : ALLOC = 9999 := rfl
  have hN := hcan.1
  have hsimp : C.P.Simple := by rw [hCQ]; exact (shearInvariance (epsOf P) P).1 hG.1
  have hBE : B.E = B.N + (B.I ++ B.O).length := by
    unfold BookData.E; simp only [List.length_append]; omega
  by_cases hK0 : 0 < N.chords.length
  · -- the planar map and the clusters
    have hne : (N.F (chainModel C) (Qof P)).Nonempty := by
      apply Set.nonempty_of_ncard_ne_zero
      rw [OracleR.chords_ncard hN]; omega
    have hV := OracleQ.valid_of_graphOK hsimp hN hne hgok
    obtain ⟨c₁, k₁, e₁, hk₁, F₁, al1a, al1b, h71, MP, hR⟩ := mapS_exec (P := P) hw hV hμ hI h1r h2r
      hone htwo hE hAl hP hC1 hC2 (by unfold clCost at hroom; omega)
      (by omega)
    have mp : ∀ r, (r = 60034 ∨ r = 60037 ∨ r = 120011) → MPres r := fun r hr => by
      rcases hr with rfl | rfl | rfl
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inr (by unfold bandOf; omega)
    obtain ⟨c₂, k₂, e₂, hk₂, F₂, al2a, al2b, K6₂, kpos, kcube, kmin, p4, p5, p4', p5', pcard, pwalk,
        pclus⟩ := clStage_exec (P := P) e₁.wb_right (B := B) rfl (by rw [MP _ (mp _ (by omega)), hμ])
      (by rw [MP _ (mp _ (by omega)), hE]) (by rw [MP _ (mp _ (by omega)), hone]) rfl hR hPW hNW
      (by omega)
    refine ⟨c₂, _, .ifLtN_true (by rw [hzero, hK]; exact hK0) (.seq e₁ e₂), ?_, ?_, ?_, ?_, ?_, ?_,
      by omega, by omega, p4', p5', ⟨kpos, kcube, kmin, pcard, pwalk, pclus⟩⟩
    · rw [hAL] at al1b; omega
    · refine (FrameN.gf (FrameN.mono F₁ (by decide)) (by rw [hAL, hAl])).trans
        (FrameN.gf (FrameN.mono F₂ (by decide)) (by rw [hAL] at al1a ⊢; omega))
    · intro r a b
      rw [F₂.1 r (by simp [bDecomp, bCluster, bandOf]; omega) (by rw [hAL]; omega),
        F₁.1 r (by simp [dBands, bSort, bDecomp, bOPrep, bandOf]; omega) (by rw [hAL]; omega)]
    · rw [K6₂ _ (by unfold bandOf; norm_num) (by omega), MP _ (mp _ (by omega)), hμ]
    · rw [hAL] at al1a al2a ⊢; omega
    · rw [hAL] at al1b al2b ⊢; omega
  · -- the trivial decomposition
    have hK00 : N.chords.length = 0 := by omega
    have hA5 : N.arcs.length ≤ 5 := by
      have h1 := arcs_le_regions hsimp hcan
      rw [regions_eq hsimp hN, hK00] at h1
      omega
    obtain ⟨c₁, k₁, e₁, hk₁, v4, v5, v90, v9, hfl, mem₁, R₁, rr₁, rm₁, o₁⟩ := trivS_exec (P := P) hw
      hμ hone hzero hAl (by unfold clCost at hroom; omega) (by omega)
    have hB8 : B.N ≤ 8 := by omega
    refine ⟨c₁, _, .ifLtN_false (by rw [hzero, hK]; omega) e₁, by omega, ?_, ?_, ?_, ?_, ?_,
      by rw [v4], by rw [v5]; omega, by rw [v4, hAL, v9]; omega, by rw [v5, hAL, v9]; omega, ?_⟩
    · refine ⟨fun r hr hra => R₁ r ?_ ?_ (by rw [hAL] at hra; exact hra) ?_ ?_ ?_ ?_,
        fun r _ => by rw [rr₁], fun a ha => mem₁ a ha, fun a _ => by rw [rm₁], o₁⟩ <;>
      · intro h; subst h; apply hr; simp [kBands, bDecomp, bCluster, bandOf]
    · intro r a b; exact R₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
    · rw [R₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hμ]
    · rw [hAL, v9]; omega
    · rw [hAL, v9]; omega
    · rw [v4, v5, v90]
      exact ClFacts.triv (by omega) hB8 (fun v hv => hfl v (by omega))

end

end OracleR

end Chazelle.Core
