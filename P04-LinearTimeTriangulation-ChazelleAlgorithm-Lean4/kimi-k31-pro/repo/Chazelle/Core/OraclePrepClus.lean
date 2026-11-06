module

public import Chazelle.Core.OraclePrepMap
public import Chazelle.Core.ClusterMeets
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ConfigTactics
set_option maxHeartbeats 2000000

/-!
# Lemma 3.6 (WP-H), preprocessing part 24: the cluster decomposition of the book

`kS`: the least `k ≥ 1` with `μ ≤ k³` (`μ` in `60034`), by incremental squares and cubes
(`60090 … 60092`); `clSet`: the inputs of the cluster decomposition (handle, `μ`, `E`, `k`) in band
`bCluster`; `clStage := kS; clSet; clusterProg` (`clStage_exec`): the flags of `D*` and the labels
of the clusters, with the walk property on the book graph.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleBook OracleBook.BookData

@[expose] public section

/-! ## The cube root -/

/-- One step: `(k, k², k³) ↦ (k + 1, (k + 1)², (k + 1)³)`. -/
def kBody : Stmt :=
  block [.addN 60092 60092 60091, .addN 60092 60092 60091, .addN 60092 60092 60091,
    .addN 60092 60092 60090, .addN 60092 60092 60090, .addN 60092 60092 60090,
    .addN 60092 60092 120011, .addN 60091 60091 60090, .addN 60091 60091 60090,
    .addN 60091 60091 120011, .addN 60090 60090 120011]

/-- **The least `k ≥ 1` with `μ ≤ k³`.** -/
def kS : Stmt :=
  .seq (block [.constN 60090 1, .constN 60091 1, .constN 60092 1]) (.whileLtN 60092 60034 kBody)

/-- The registers written by `kS`. -/
def BK3 (r : ℕ) : Bool := decide (60090 ≤ r ∧ r ≤ 60092)

theorem kBody_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {j μ : ℕ}
    (h0 : c.nreg 60090 = j) (h1 : c.nreg 60091 = j ^ 2) (h2 : c.nreg 60092 = j ^ 3)
    (hone : c.nreg 120011 = 1) (hj : 1 ≤ j) (hlt : j ^ 3 < μ) (hW : 8 * μ ≤ W) :
    ∃ c' k, Exec P W kBody c c' k ∧ k = 11 ∧ FrameB BK3 c c' ∧ c'.nreg 60090 = j + 1 ∧
      c'.nreg 60091 = (j + 1) ^ 2 ∧ c'.nreg 60092 = (j + 1) ^ 3 := by
  have hwr : wr BK3 kBody = true := by decide
  suffices H : ∃ c' k, Exec P W kBody c c' k ∧ k = 11 ∧ c'.nreg 60090 = j + 1 ∧
      c'.nreg 60091 = (j + 1) ^ 2 ∧ c'.nreg 60092 = (j + 1) ^ 3 by
    obtain ⟨c', k, ex, hk, a, b, d⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, a, b, d⟩
  have e3 : (j + 1) ^ 3 = j ^ 3 + 3 * j ^ 2 + 3 * j + 1 := by ring
  have hb : (j + 1) ^ 3 ≤ 8 * j ^ 3 := by nlinarith [sq_nonneg j, pow_pos (by omega : 0 < j) 2]
  have hsq : 0 ≤ j ^ 2 := Nat.zero_le _
  unfold kBody
  exec_block
  all_goals (try config_simp)
  all_goals (try rw [h0, h1, h2, hone])
  all_goals (try nlinarith)
  all_goals (try (refine ⟨rfl, ?_, ?_⟩ <;> ring))

theorem kS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {μ : ℕ}
    (hμ : c.nreg 60034 = μ) (hone : c.nreg 120011 = 1) (hW : 8 * μ + 8 ≤ W) :
    ∃ c' k, Exec P W kS c c' k ∧ k ≤ 16 * μ + 5 ∧ FrameB BK3 c c' ∧
      1 ≤ c'.nreg 60090 ∧ μ ≤ c'.nreg 60090 ^ 3 ∧
      (c'.nreg 60090 = 1 ∨ (c'.nreg 60090 - 1) ^ 3 < μ) := by
  have hwr : wr BK3 kS = true := by decide
  obtain ⟨c₁, k₁, e₁, hk₁, a0, a1, a2, R₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 60090 1, .constN 60091 1, .constN 60092 1]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 60090 = 1 ∧ c₁.nreg 60091 = 1 ∧ c₁.nreg 60092 = 1 ∧
      (∀ r, BK3 r = false → c₁.nreg r = c.nreg r) := by
    exec_block
    · omega
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp, fun r hr => ?_⟩
      unfold BK3 at hr; simp only [decide_eq_false_iff_not] at hr
      config_simp; simp only [upd_apply]; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  let I : Config → Prop := fun d => WordsBounded W d ∧ d.nreg 60034 = μ ∧ d.nreg 120011 = 1 ∧
    ∃ j, 1 ≤ j ∧ d.nreg 60090 = j ∧ d.nreg 60091 = j ^ 2 ∧ d.nreg 60092 = j ^ 3 ∧
      (j = 1 ∨ (j - 1) ^ 3 < μ)
  have hI₁ : I c₁ := ⟨e₁.wb_right, by rw [R₁ _ (by decide), hμ], by rw [R₁ _ (by decide), hone],
    1, le_rfl, a0, by rwn [a1], by rwn [a2], Or.inl rfl⟩
  obtain ⟨c₂, k₂, e₂, ⟨-, -, -, j, hj1, b0, -, b2, hjm⟩, hn, hk₂, -⟩ :=
    SortR.whileLtN_potential_lb (P := P) (W := W) (a := 60092) (b := 60034) (body := kBody) I
      (fun d => 16 * (μ - d.nreg 60090)) (fun _ => 0) (fun d h => h.1)
      (fun d ⟨hwd, dμ, d1, j, hj1, d0, dsq, dcu, _⟩ ht => by
        rw [dcu, dμ] at ht
        obtain ⟨d', k, ex, hk, F, v0, v1, v2⟩ := kBody_exec (P := P) hwd d0 dsq dcu d1 hj1 ht (by omega)
        have hjμ : j < μ := lt_of_le_of_lt (by nlinarith [pow_pos (by omega : 0 < j) 2]) ht
        refine ⟨d', k, ex, ⟨ex.wb_right, by rw [F.1 _ (by decide), dμ], by rw [F.1 _ (by decide), d1],
          j + 1, by omega, v0, v1, v2, Or.inr (by simpa using ht)⟩, ?_, Nat.zero_le _⟩
        rwo [v0, d0]) hI₁
  refine ⟨c₂, _, .seq e₁ e₂, ?_, exec_frameB (.seq e₁ e₂) hwr, by rwx [b0], ?_, ?_⟩
  · rwo [a0] at hk₂
  · rw [b0]; rw [b2] at hn
    have : c₂.nreg 60034 = μ := by
      rw [(exec_frameB e₂ (B := BK3) (by decide)).1 _ (by decide), R₁ _ (by decide), hμ]
    rwo [this] at hn
  · rwx [b0]

/-! ## The call -/

/-- The inputs of the cluster decomposition. -/
def clSet : Stmt :=
  block [.copyN 130000 60071, .copyN 130001 60034, .copyN 130002 60037, .copyN 130003 60090]

/-- **The cluster stage.** -/
def clStage : Stmt := .seq kS (.seq clSet Cluster.clusterProg)

/-- The cost of the cluster decomposition for `μ` nodes and `E` edges. -/
def clCost (μ E : ℕ) : ℕ := Cluster.clusterK * ((μ + E) * (Nat.clog 2 (μ + E) + 1) + 1)

theorem card_fin_filter (n : ℕ) (p : ℕ → Prop) [DecidablePred p]
    [DecidablePred (fun v : Fin n => p v)] :
    (Finset.univ.filter (fun v : Fin n => p v)).card = ((Finset.range n).filter p).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v.2, hv⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨x, h⟩, hp, rfl⟩

open Classical in
theorem clStage_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {B : BookData}
    {Bh A : ℕ} (hBh : c.nreg 60071 = Bh) (hμ : c.nreg 60034 = B.N) (hE : c.nreg 60037 = B.E)
    (hone : c.nreg 120011 = 1) (hA : c.nreg ALLOC = A)
    (hR : Robust A c.nmem (fun m => PlanarMapAt m Bh B.N B.E ∧
      memGraph m Bh B.N B.E = OracleQ.bookGraph B))
    (hPW : P.n + 3 ≤ W) (hW : 8 * B.N + 8 ≤ W) (hroom : A + clCost B.N B.E ≤ W) :
    ∃ c' k, Exec P W clStage c c' k ∧ k ≤ 16 * B.N + 9 + clCost B.N B.E ∧
      FrameN {bDecomp, bCluster} c c' ∧ A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + k ∧
      (∀ r, bandOf r = 6 → (r < 60090 ∨ 60092 < r) → c'.nreg r = c.nreg r) ∧
      1 ≤ c'.nreg 60090 ∧ B.N ≤ c'.nreg 60090 ^ 3 ∧
      (c'.nreg 60090 = 1 ∨ (c'.nreg 60090 - 1) ^ 3 < B.N) ∧
      A ≤ c'.nreg 130004 ∧ A ≤ c'.nreg 130005 ∧
      c'.nreg 130004 + B.N ≤ c'.nreg ALLOC ∧ c'.nreg 130005 + B.N ≤ c'.nreg ALLOC ∧
      ((Finset.range B.N).filter (fun v => c'.nmem (c'.nreg 130004 + v) = 1)).card ≤
        7 * c'.nreg 60090 ^ 2 ∧
      (∀ u v (w : (OracleQ.bookGraph B).Walk u v),
        (∀ x ∈ w.support, c'.nmem (c'.nreg 130004 + x) ≠ 1) →
          c'.nmem (c'.nreg 130005 + u) = c'.nmem (c'.nreg 130005 + v)) ∧
      (∀ l, ((Finset.range B.N).filter (fun v => c'.nmem (c'.nreg 130004 + v) ≠ 1 ∧
        c'.nmem (c'.nreg 130005 + v) = l)).card ≤ c'.nreg 60090 ^ 2) := by
  have hAL : ALLOC = 9999 := rfl
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, kpos, kcube, kmin⟩ := kS_exec (P := P) hw hμ hone (by omega)
  set kk := c₁.nreg 60090 with hkk
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, s0, s1, s2, s3⟩ : ∃ c₂ k₂, Exec P W clSet c₁ c₂ k₂ ∧ k₂ = 4 ∧
      FrameB (fun r => decide (130000 ≤ r ∧ r ≤ 130003)) c₁ c₂ ∧ c₂.nreg 130000 = Bh ∧
      c₂.nreg 130001 = B.N ∧ c₂.nreg 130002 = B.E ∧ c₂.nreg 130003 = kk := by
    have hwr : wr (fun r => decide (130000 ≤ r ∧ r ≤ 130003)) clSet = true := by decide
    suffices H : ∃ c₂ k₂, Exec P W clSet c₁ c₂ k₂ ∧ k₂ = 4 ∧ c₂.nreg 130000 = Bh ∧
        c₂.nreg 130001 = B.N ∧ c₂.nreg 130002 = B.E ∧ c₂.nreg 130003 = kk by
      obtain ⟨c₂, k₂, ex, hk, a, b, d, e⟩ := H
      exact ⟨c₂, k₂, ex, hk, exec_frameB ex hwr, a, b, d, e⟩
    have w₁ := e₁.wb_right
    unfold clSet
    exec_block
    exact ⟨rfl, by config_simp; rw [F₁.1 _ (by decide), hBh],
      by config_simp; rw [F₁.1 _ (by decide), hμ], by config_simp; rw [F₁.1 _ (by decide), hE],
      by csr⟩
  have m₂ : c₂.nmem = c.nmem := F₂.2.2.1.trans F₁.2.2.1
  have A₂ : c₂.nreg ALLOC = A := by
    rwx [hAL, F₂.1 _ (by decide), F₁.1 _ (by decide)]
  have r0 : rd c₂ bCluster 0 = Bh := s0
  have r1 : rd c₂ bCluster 1 = B.N := s1
  have r2 : rd c₂ bCluster 2 = B.E := s2
  have r3 : rd c₂ bCluster 3 = kk := s3
  have hcost : c₂.nreg ALLOC + Cluster.clusterK * ((rd c₂ bCluster 1 + rd c₂ bCluster 2) *
      (Nat.clog 2 (rd c₂ bCluster 1 + rd c₂ bCluster 2) + 1) + 1) ≤ W := by
    rwx [A₂, r1, r2]
  obtain ⟨c₃, k₃, e₃, hk₃, post, F₃⟩ := clusterProg_meets P W c₂ e₂.wb_right
    ⟨hPW, by rw [r3]; exact kpos, by rw [r1, r3]; exact kcube, fun m' hm' => by
      rw [r0, r1, r2]
      exact (hR m' (fun a ha => by rw [hm' a (by rwx [A₂]), m₂])).1⟩ hcost
  beta_reduce at hk₃
  rw [r1, r2] at hk₃
  obtain ⟨p4, p5, p4', p5', pcard, pwalk, pclus⟩ := post
  have hG : memGraph c₂.nmem Bh B.N B.E = OracleQ.bookGraph B :=
    (hR c₂.nmem (fun a _ => by rw [m₂])).2
  revert p4' p5' pcard pwalk pclus
  rw [r0, r1, r2, r3, hG]
  intro p4' p5' pcard pwalk pclus
  have K6 : ∀ r, bandOf r = 6 → c₃.nreg r = c₂.nreg r := fun r hr =>
    F₃.1 r (by simp [hr, bCluster]) (by rw [hAL]; intro h; rw [h] at hr; simp [bandOf] at hr)
  have k3 : c₃.nreg 60090 = kk := by
    rw [K6 _ (by ufn bandOf), F₂.1 _ (by decide)]
  have A₃a : A ≤ c₃.nreg ALLOC := by have := F₃.2.2.2.2.2.1; omega
  have A₃b : c₃.nreg ALLOC ≤ A + k₃ := by have := F₃.2.2.2.2.2.2; omega
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by ufo clCost, ?_, A₃a, by omega, ?_,
    by rw [k3]; exact kpos, by rw [k3]; exact kcube, by rw [k3]; exact kmin,
    by rwx [← A₂], by rwx [← A₂], p4', p5', ?_, pwalk, ?_⟩
  · have FA : FrameN {bDecomp, bCluster} c c₂ :=
      PF.frameN (B := fun r => BK3 r || decide (130000 ≤ r ∧ r ≤ 130003))
        ⟨fun r hr => by
          simp only [Bool.or_eq_false_iff] at hr
          rw [F₂.1 r hr.2, F₁.1 r hr.1],
        fun r hr => by
          simp only [Bool.or_eq_false_iff] at hr
          rw [F₂.2.1 r hr.2, F₁.2.1 r hr.1],
        fun a _ => by rw [m₂], fun a _ => by rw [F₂.2.2.2.1, F₁.2.2.2.1],
        by rw [F₂.2.2.2.2, F₁.2.2.2.2]⟩
        (fun r hr => by
          simp only [BK3, Bool.or_eq_true, decide_eq_true_eq] at hr
          left
          rcases hr with h | h
          · sio [bDecomp, bandOf]
          · sio [bCluster, bandOf])
        (by rw [hAL, F₂.2.1 _ (by decide), F₁.2.1 _ (by decide)])
    exact FA.trans (FrameN.mono (Frame.toN F₃) (by decide)) (by rw [A₂, ← hA])
  · intro r hr hr'
    rw [K6 r hr, F₂.1 r (by simp only [decide_eq_false_iff_not]; ufo bandOf at hr),
      F₁.1 r (by unfold BK3; sio only [decide_eq_false_iff_not])]
  · rw [k3]; refine le_trans (le_of_eq ?_) pcard
    refine Eq.trans ?_ (card_fin_filter B.N (fun v => c₃.nmem (c₃.nreg 130004 + v) = 1)).symm
    congr 1
  · intro l; rw [k3]; refine le_trans (le_of_eq ?_) (pclus l)
    refine Eq.trans ?_ (card_fin_filter B.N (fun v => c₃.nmem (c₃.nreg 130004 + v) ≠ 1 ∧
      c₃.nmem (c₃.nreg 130005 + v) = l)).symm
    congr 1

end

end OracleR

end Chazelle.Core
