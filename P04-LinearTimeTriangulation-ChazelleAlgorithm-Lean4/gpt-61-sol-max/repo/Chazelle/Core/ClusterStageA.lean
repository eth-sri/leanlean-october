module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterSetupRam
public import Chazelle.Core.ClusterFirst

/-!
# WP-I, part 44: stage A — the first darts, the primal search and the level-ancestor table

After the setup: `ZERO := 0` (slot `1`, `N` cells), `LAB := μ` (slot `2`), `FIRST` (slot `0`),
the primal breadth-first search from vertex `0` (levels in slot `3`, parent darts in slot `4`,
queue in slot `5`), the parent array `PV` (slot `6`) and the table `UPT` of its powers.

* `fillWith`: fill `[b, b + n)` with a value, all three read from registers;
* `primalEnv_enc`: the stored input map with its `first` array encodes `M`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs
open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- Fill `[nreg rb, nreg rb + nreg rn)` with `nreg rv`. -/
def fillWith (rb rn rv : ℕ) : Stmt :=
  .seq (block [.copyN 130150 rb, .copyN 130151 rn, .copyN 130152 rv]) fillStmt

/-- The registers of `fillWith`. -/
def FillRG (r : ℕ) : Prop := 130150 ≤ r ∧ r ≤ 130154

section proofs

variable {P : Polygon} {W : ℕ}

theorem fillWith_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {rb rn rv b n x : ℕ} (hb : c.nreg rb = b) (hn : c.nreg rn = n) (hx : c.nreg rv = x)
    (_hrb : ¬ FillRG rb) (hrn : ¬ FillRG rn) (hrv : ¬ FillRG rv)
    (hwb : b + n ≤ W) (hwn : n + 1 ≤ W) :
    ∃ c' k, Exec P W (fillWith rb rn rv) c c' k ∧ k ≤ 5 * n + 6 ∧ WordsBounded W c' ∧
      PFr FillRG (fun a => b ≤ a ∧ a < b + n) c c' ∧ ∀ i, i < n → c'.nmem (b + i) = x := by
  unfold fillWith
  unfold FillRG at _hrb hrn hrv
  obtain ⟨c3, k3, e3, hk3, hw3, r150, r151, r152, hone3, hf3⟩ : ∃ c3 k3, Exec P W
      (block [.copyN 130150 rb, .copyN 130151 rn, .copyN 130152 rv]) c c3 k3 ∧ k3 = 3 ∧
      WordsBounded W c3 ∧ c3.nreg 130150 = b ∧ c3.nreg 130151 = n ∧ c3.nreg 130152 = x ∧
      c3.nreg 130001 = 1 ∧ PFr FillRG (fun a => b ≤ a ∧ a < b + n) c c3 := by
    exec_block
    refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    all_goals (grind [Machine.upd_apply, FillRG])
  obtain ⟨c', k, e, hk, hf', hv⟩ := fillStmt_exec (P := P) hw3 hone3
    (by omega) (by omega)
  rw [r150, r151] at hf'
  rw [r150, r151, r152] at hv
  rw [r151] at hk
  have hf'' : PFr FillRG (fun a => b ≤ a ∧ a < b + n) c3 c' :=
    hf'.mono (fun r h => by omega_nf) (fun a h => h)
  exact ⟨c', k3 + k, .seq e3 e, by omega, e.wb_right, hf3.trans hf'', hv⟩

end proofs

/-! ## The input map as a rotation system -/

section enc

variable {μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)}

/-- **The stored input map encodes `M`.** -/
theorem primalEnv_enc {m : ℕ → ℕ} {bO bR bV bF bDB bVB : ℕ}
    (h : MapArrays m bO bR bV μ N M) (hF : ∀ u, u < μ → m (bF + u) < N ∧ m (bV + m (bF + u)) = u) :
    EnvEnc (primalEnv m bO bR bV bF bDB bVB μ N) M (fun v => (v : ℕ)) (fun d => (d : ℕ)) := by
  refine ⟨fun v => v.2, fun v w h => Fin.ext h, fun u hu => ⟨⟨u, hu⟩, rfl⟩, fun d => d.2,
    fun d e h => Fin.ext h, fun e he => ⟨⟨e, he⟩, rfl⟩, fun d => ?_, fun d => ?_, fun d => ?_,
    fun v => ?_⟩
  · show view m bO N d = _
    rw [view_lt d.2, h.opp d.2]
  · show view m bR N d = _
    rw [view_lt d.2, h.rot d.2]
  · show view m bV N d = _
    rw [view_lt d.2, h.vert d.2]
  · obtain ⟨h1, h2⟩ := hF v v.2
    refine ⟨⟨m (bF + v), h1⟩, by show view m bF μ v = _; rw [view_lt v.2], ?_⟩
    apply Fin.ext
    rw [← h.vert h1]; exact h2

end enc

/-! ## The phases -/

/-- The first darts. -/
def firstP : Stmt := .seq (block [.copyN 130221 130023, .copyN 130222 130030, .copyN 130223 130014])
  firstStmt

/-- The primal search from `0` with label `0`. -/
def bfsP : Stmt := .seq (block [.copyN 130100 130021, .copyN 130101 130022, .copyN 130102 130023,
  .copyN 130103 130030, .copyN 130104 130031, .copyN 130105 130031, .copyN 130106 130032,
  .copyN 130107 130033, .copyN 130108 130034, .copyN 130109 130035, .copyN 130110 130011,
  .constN 130111 0, .constN 130112 0]) bfsStmt

/-- The parent array `PV` (slot `6`). -/
def parP : Stmt := .seq (block [.copyN 130500 130023, .copyN 130501 130034, .copyN 130502 130036,
  .copyN 130503 130011]) parStmt

/-- The level-ancestor table `UPT`. -/
def upP : Stmt := .seq (block [.copyN 130510 130036, .copyN 130511 130084, .copyN 130512 130011,
  .copyN 130513 130017]) upStmt

/-- **Stage A.** -/
def stageA : Stmt := .seq (fillWith 130031 130014 130009) (.seq (fillWith 130032 130011 130011)
  (.seq firstP (.seq bfsP (.seq parP upP))))

/-- The registers written by stage A. -/
def StARG (r : ℕ) : Prop := (130100 ≤ r ∧ r ≤ 130130) ∨ (130150 ≤ r ∧ r ≤ 130154) ∨
  (130221 ≤ r ∧ r ≤ 130226) ∨ (130500 ≤ r ∧ r ≤ 130519)

/-- The primal parent as a function on `ℕ`. -/
def upTf {μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)} (T : SpanTree M) : ℕ → ℕ :=
  fun y => if h : y < μ then (T.parent ⟨y, h⟩ : ℕ) else 0

section phases

variable {P : Polygon} {W : ℕ}

theorem firstP_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hvlt : ∀ d, d < g.N → c.nmem (g.bV + d) < g.μ)
    (hsurj : ∀ u, u < g.μ → ∃ d, d < g.N ∧ c.nmem (g.bV + d) = u)
    (hV : g.bV + g.N ≤ g.A0) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W firstP c c' k ∧ k ≤ 7 * g.N + 6 ∧ WordsBounded W c' ∧
      PFr StARG (fun a => g.base 0 ≤ a ∧ a < g.base 0 + g.μ) c c' ∧
      ∀ u, u < g.μ → c'.nmem (g.base 0 + u) < g.N ∧ c.nmem (g.bV + c'.nmem (g.base 0 + u)) = u := by
  have hU := g.U_ge
  have hEND := g.END_eq
  have hb0 : g.base 0 = g.A0 := by rw [g.base_eq]; ring
  have hb00 := hG.rbase 0 (by omega)
  unfold firstP
  obtain ⟨c1, k1, e1, hk1, hw1, r1, r2, r3, hone1, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130221 130023, .copyN 130222 130030, .copyN 130223 130014]) c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 130221 = g.bV ∧ c1.nreg 130222 = g.base 0 ∧
      c1.nreg 130223 = g.N ∧ c1.nreg 130001 = 1 ∧
      PFr StARG (fun a => g.base 0 ≤ a ∧ a < g.base 0 + g.μ) c c1 := by
    exec_block
    refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    · config_simp; exact hG.rV
    · simp_all
    · config_simp; exact hG.rN
    · config_simp; exact hG.one
    grind [Machine.upd_apply, StARG]
  obtain ⟨c', k, e, hk, hf', hI⟩ := firstStmt_exec (P := P) hw1 hone1 (bV := g.bV)
    (bF := g.base 0) (N := g.N) r1 r2 r3
    (nv := g.μ) (fun d hd => by rw [hf1.2.2.2.2 _ (by omega)]; simp_all)
    (fun u hu => by
      obtain ⟨d, hd, hdu⟩ := hsurj u hu
      exact ⟨d, hd, by ram_grind⟩)
    (by right; omega) (by omega) (by omega) (by omega)
  refine ⟨c', k1 + k, .seq e1 e, by omega, e.wb_right,
    hf1.trans (hf'.mono (fun r h => by grind [FirstRG, StARG]) (fun a h => h)),
    fun u hu => ⟨(hI u hu).1, ?_⟩⟩
  ram_grind

/-- The layout of the primal search. -/
def primalLay (g : GV) : Lay := ⟨g.bO, g.bR, g.bV, g.base 0, g.base 1, g.base 1, g.base 2,
  g.base 3, g.base 4, g.base 5, g.μ, g.N⟩

theorem primalLay_good {g : GV} (hμ : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0)
    (hR : g.bR + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0) (hW : g.END ≤ W) :
    (primalLay g).Good W := by
  have hU := g.U_ge
  have hE := g.END_eq
  have b0 := g.base_eq 0; have b1 := g.base_eq 1; have b2 := g.base_eq 2; have b3 := g.base_eq 3
  have b4 := g.base_eq 4; have b5 := g.base_eq 5
  refine ⟨fun b n h => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [primalLay, Disj] at *
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  all_goals first | omega

open Classical in
theorem bfsP_exec {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap (Fin g.μ) F (Fin g.N)} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hmap : MapArrays c.nmem g.bO g.bR g.bV g.μ g.N M) (hM : M.Connected) (hμ : 0 < g.μ)
    (hμN : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0)
    (hV : g.bV + g.N ≤ g.A0)
    (hfirst : ∀ u, u < g.μ → c.nmem (g.base 0 + u) < g.N ∧
      c.nmem (g.bV + c.nmem (g.base 0 + u)) = u)
    (hzero : ∀ d, d < g.N → c.nmem (g.base 1 + d) = 0)
    (hlab : ∀ v, v < g.μ → c.nmem (g.base 2 + v) = g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W bfsP c c' k ∧ k ≤ 70 * g.μ + 50 * g.N + 30 ∧ WordsBounded W c' ∧
      PFr StARG (fun a => g.base 2 ≤ a ∧ a < g.base 6) c c' ∧
      ∃ T : SpanTree M, (T.root : ℕ) = 0 ∧ (∀ v : Fin g.μ, c'.nmem (g.base 3 + v) = T.level v) ∧
        (∀ v, T.level v < g.μ) ∧
        (∀ v, v ≠ T.root → c'.nmem (g.base 4 + v) < g.N ∧
          (T.par v : ℕ) = c.nmem (g.bO + c'.nmem (g.base 4 + v)) ∧
          (T.parent v : ℕ) = c.nmem (g.bV + c'.nmem (g.base 4 + v))) ∧
        (∀ d : Fin g.N, T.level (M.head d) ≤ T.level (M.vert d) + 1) := by
  have hU := g.U_ge
  have hE := g.END_eq
  have b0 := g.base_eq 0; have b1 := g.base_eq 1; have b2 := g.base_eq 2; have b3 := g.base_eq 3
  have b4 := g.base_eq 4; have b5 := g.base_eq 5; have b6 := g.base_eq 6
  set Y := primalLay g with hY
  have hYg : Y.Good W := primalLay_good hμN hO hR hV hW
  unfold bfsP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hR1, hf1⟩ : ∃ c1 k1, Exec P W (block [.copyN 130100 130021,
      .copyN 130101 130022, .copyN 130102 130023, .copyN 130103 130030, .copyN 130104 130031,
      .copyN 130105 130031, .copyN 130106 130032, .copyN 130107 130033, .copyN 130108 130034,
      .copyN 130109 130035, .copyN 130110 130011, .constN 130111 0, .constN 130112 0]) c c1 k1 ∧
      k1 = 13 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ Regs Y 0 0 c1 ∧
      PFr StARG (fun a => g.base 2 ≤ a ∧ a < g.base 6) c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨fun r hr => ?fr, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    case fr =>
      simp only
      unfold StARG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    all_goals try (config_simp <;>
                   first
                   | exact hG.one
                   | exact hG.rO
                   | exact hG.rR
                   | exact hG.rV
                   | exact hG.rμ
                   | exact hG.rN
                   | exact hG.rbase 0 (by omega)
                   | exact hG.rbase 1 (by omega)
                   | exact hG.rbase 2 (by omega)
                   | exact hG.rbase 3 (by omega)
                   | exact hG.rbase 4 (by omega)
                   | exact hG.rbase 5 (by omega))
  have hm1' : MapArrays c1.nmem g.bO g.bR g.bV g.μ g.N M := by grind
  have henv : Y.env c1.nmem = primalEnv c1.nmem g.bO g.bR g.bV (g.base 0) (g.base 1) (g.base 1)
      g.μ g.N := rfl
  have hF1 : ∀ u, u < g.μ → c1.nmem (g.base 0 + u) < g.N ∧
      c1.nmem (g.bV + c1.nmem (g.base 0 + u)) = u := by grind
  have hok : (Y.env c1.nmem).OK := by rw [henv]; exact primalEnv_ok hm1' hF1
  have hpre : (Y.env c1.nmem).Pre 0 0 (labV Y c1.nmem) := by
    refine ⟨hok, hμ, ?_, hμ, fun w hw' _ => ?_⟩
    · show view c1.nmem (g.base 1) g.μ 0 ≠ 1
      rw [view_lt hμ, hm1, hzero 0 (by omega)]; omega
    · show view c1.nmem (g.base 2) g.μ w = g.μ
      rw [view_lt (show w < g.μ from hw'), hm1]; exact hlab w hw'
  obtain ⟨c', k, e, hk, ⟨hw', hfr', hI⟩, hht⟩ := bfs_exec (P := P) hYg hR1 hpre hw1
  rw [hht] at hI
  have hGenc := primalEnv_enc (bDB := g.base 1) (bVB := g.base 1) hm1' hF1
  rw [← henv] at hGenc
  have hdb : ∀ d, d < g.N → (Y.env c1.nmem).db d ≠ 1 := by
    intro d hd
    show view c1.nmem (g.base 1) g.N d ≠ 1
    rw [view_lt hd, hm1, hzero d hd]; omega
  have hvb : ∀ v, v < g.μ → (Y.env c1.nmem).vb v ≠ 1 := by
    intro v hv
    show view c1.nmem (g.base 1) g.μ v ≠ 1
    rw [view_lt hv, hm1, hzero v (by omega)]; omega
  obtain ⟨T, hroot, hlev, hpar, hhead, hlt⟩ := primal_tree hM hμ rfl hGenc hdb hvb hI
  -- the cost
  have hsum := hI.sum_deg_le hok (le_refl _)
  have htn := hI.tn
  refine ⟨c', k1 + k, .seq e1 e, ?_, hw', hf1.trans ⟨fun r hr => hfr'.1 r (fun h => hr (by
      grind [Scr, StARG])), hfr'.2.1, hfr'.2.2.1, hfr'.2.2.2.1,
      fun a ha => hfr'.2.2.2.2 a (fun h => ha (by
        unfold Lay.Written at h; simp only [hY, primalLay] at h; omega))⟩, T, hroot,
      fun v => ?_, hlt, fun v hv => ?_, hhead⟩
  · have : (Y.env c1.nmem).N = g.N := rfl
    have : (Y.env c1.nmem).nv = g.μ := rfl
    omega
  · rw [hlev v]
    show _ = view c'.nmem (g.base 3) g.μ v
    rw [view_lt v.2]
  · obtain ⟨h1, h2, h3⟩ := hpar v hv
    have hpv : parV Y c'.nmem v = c'.nmem (g.base 4 + v) := by
      show view c'.nmem (g.base 4) g.μ v = _; rw [view_lt v.2]
    rw [hpv] at h1 h2 h3
    refine ⟨h1, ?_, ?_⟩
    · rw [h2]; show view c1.nmem g.bO g.N _ = _; rw [view_lt h1, hm1]
    · rw [h3]; show view c1.nmem g.bV g.N _ = _; rw [view_lt h1, hm1]

section
variable {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c) (hμ : 0 < g.μ)
include hw hG hμ
theorem parP_exec
    (hV : g.bV + g.N ≤ g.A0) (hpar : ∀ x, 1 ≤ x → x < g.μ → c.nmem (g.base 4 + x) < g.N)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W parP c c' k ∧ k ≤ 9 * g.μ + 8 ∧ WordsBounded W c' ∧
      PFr StARG (fun a => g.base 6 ≤ a ∧ a < g.base 6 + g.μ) c c' ∧ c'.nmem (g.base 6) = 0 ∧
      ∀ x, 1 ≤ x → x < g.μ → c'.nmem (g.base 6 + x) = c.nmem (g.bV + c.nmem (g.base 4 + x)) := by
  have hU := g.U_ge
  have hE := g.END_eq
  have b4 := g.base_eq 4; have b6 := g.base_eq 6
  unfold parP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hone1, hzero1, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130500 130023, .copyN 130501 130034, .copyN 130502 130036,
        .copyN 130503 130011]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130500 = g.bV ∧ c1.nreg 130501 = g.base 4 ∧ c1.nreg 130502 = g.base 6 ∧
      c1.nreg 130503 = g.μ ∧ c1.nreg 130001 = 1 ∧ c1.nreg 130009 = 0 ∧
      PFr StARG (fun a => g.base 6 ≤ a ∧ a < g.base 6 + g.μ) c c1 := by
    exec_block <;> (config_simp; grind [Chazelle.upd, Chazelle.WordsBounded, Chazelle.Core.Cluster.PFr, Chazelle.Core.Cluster.StARG, Chazelle.Core.Cluster.GR])
  obtain ⟨c', k, e, hk, hw', hf', h0, hx⟩ := parStmt_exec (P := P) hw1 hone1 hzero1 r0 r1 r2 r3
    hμ (by omega) (by omega) (by omega) (fun x h1 h2 => by
      grind)
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw',
    hf1.trans (hf'.mono (fun r h => by omega_nf) (fun a h => h)),
    by omega,
    fun x h1 h2 => by grind⟩

theorem upP_exec
    (hL : 0 < g.L) (hpv : ∀ x, x < g.μ → c.nmem (g.base 6 + x) < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W upP c c' k ∧ k ≤ 12 * g.μ * g.L + 7 * g.L + 16 ∧ WordsBounded W c' ∧
      PFr StARG (fun a => g.A0 + 54 * g.U ≤ a ∧ a < g.A0 + 54 * g.U + g.L * g.μ) c c' ∧
      ∀ j, j < g.L → ∀ x, x < g.μ → c'.nmem (g.A0 + 54 * g.U + j * g.μ + x) =
        (fun y => c.nmem (g.base 6 + y))^[2 ^ j] x := by
  have hU := g.U_ge
  have hE := g.END_eq
  have b6 := g.base_eq 6
  have hLU := g.L_le_U
  have hLμ : g.L * g.μ ≤ g.L * g.U := Nat.mul_le_mul_left _ (by omega)
  unfold upP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hone1, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130510 130036, .copyN 130511 130084, .copyN 130512 130011,
        .copyN 130513 130017]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130510 = g.base 6 ∧ c1.nreg 130511 = g.A0 + 54 * g.U ∧ c1.nreg 130512 = g.μ ∧
      c1.nreg 130513 = g.L ∧ c1.nreg 130001 = 1 ∧
      PFr StARG (fun a => g.A0 + 54 * g.U ≤ a ∧ a < g.A0 + 54 * g.U + g.L * g.μ) c c1 := by
    exec_block
    refine ⟨rfl, ‹_›, rfl, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    all_goals try (config_simp;
                   first
                   | exact hG.one
                   | exact hG.rL
                   | exact hG.rμ
                   | exact hG.rbase 6 (by omega)
                   | (rw [hG.rbase 54 (by omega)]; rfl))
    simp only
    unfold StARG at hr
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  obtain ⟨c', k, e, hk, hw', hf', htab⟩ := upStmt_exec (P := P) hw1 hone1 r0 r1 r2 r3 hL
    (fun x hx => by simp_all) (by omega) (by omega) (by omega) (by omega) hμ
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw',
    hf1.trans (hf'.mono (fun r h => by grind [UpRG, StARG]) (fun a h => h)),
    fun j hj x hx => by rw [htab j hj x hx, hm1]⟩


end

/-- Iterates of functions agreeing on an invariant range agree there. -/
theorem iterate_congr_lt {f f' : ℕ → ℕ} {n : ℕ} (h : ∀ x, x < n → f x = f' x)
    (hf : ∀ x, x < n → f' x < n) (k : ℕ) : ∀ x, x < n → f^[k] x = f'^[k] x ∧ f'^[k] x < n := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    simp_all

theorem upTf_lt {μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)} (T : SpanTree M) {x : ℕ}
    (hx : x < μ) : upTf T x < μ := by
  simp_all [upTf]

/-- **The facts of stage A.** -/
structure AF (g : GV) {F : Type} (M : CombMap (Fin g.μ) F (Fin g.N)) (T : SpanTree M)
    (m : ℕ → ℕ) : Prop where
  map : MapArrays m g.bO g.bR g.bV g.μ g.N M
  zero : ∀ d, d < g.N → m (g.base 1 + d) = 0
  first_lt : ∀ u, u < g.μ → m (g.base 0 + u) < g.N
  first_v : ∀ u, u < g.μ → m (g.bV + m (g.base 0 + u)) = u
  root : (T.root : ℕ) = 0
  lev : ∀ v : Fin g.μ, m (g.base 3 + v) = T.level v
  lev_lt : ∀ v : Fin g.μ, T.level v < g.μ
  par_lt : ∀ v : Fin g.μ, v ≠ T.root → m (g.base 4 + v) < g.N
  par_eq : ∀ v : Fin g.μ, v ≠ T.root → (T.par v : ℕ) = m (g.bO + m (g.base 4 + v))
  pv : ∀ v : Fin g.μ, m (g.base 6 + v) = T.parent v
  upt : ∀ j, j < g.L → ∀ x, x < g.μ →
    m (g.A0 + 54 * g.U + j * g.μ + x) = (upTf T)^[2 ^ j] x
  head_le : ∀ d : Fin g.N, T.level (M.head d) ≤ T.level (M.vert d) + 1

/-- The addresses read by the facts of stage A. -/
def KeepA (g : GV) (a : ℕ) : Prop :=
  a < g.A0 + 2 * g.U ∨ (g.base 3 ≤ a ∧ a < g.base 5) ∨ (g.base 6 ≤ a ∧ a < g.base 7) ∨
    (g.A0 + 54 * g.U ≤ a ∧ a < g.A0 + 54 * g.U + g.L * g.U)

theorem AF.congr {g : GV} {F : Type} {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M}
    {m m' : ℕ → ℕ} (h : AF g M T m) (hA : g.bO + g.N ≤ g.A0 ∧ g.bR + g.N ≤ g.A0 ∧
      g.bV + g.N ≤ g.A0) (he : ∀ a, KeepA g a → m' a = m a) : AF g M T m' := by
  have hU := g.U_ge
  have b0 := g.base_eq 0; have b1 := g.base_eq 1; have b3 := g.base_eq 3; have b4 := g.base_eq 4
  have b5 := g.base_eq 5; have b6 := g.base_eq 6; have b7 := g.base_eq 7
  have hLμ : ∀ j, j < g.L → j * g.μ + g.μ ≤ g.L * g.U := by
    intro j hj
    have : (j + 1) * g.μ ≤ g.L * g.U := Nat.mul_le_mul (by omega) (by omega)
    grind
  refine ⟨fun d => ?_, fun d hd => ?_, fun u hu => ?_, fun u hu => ?_, h.root, fun v => ?_,
    h.lev_lt, fun v hv => ?_, fun v hv => ?_, fun v => ?_, fun j hj x hx => ?_, h.head_le⟩
  · have hd := d.2
    rw [he _ (by unfold KeepA; omega), he (g.bR + d) (by unfold KeepA; omega),
      he (g.bV + d) (by unfold KeepA; omega)]
    exact h.map d
  · rw [he _ (by unfold KeepA; omega)]; exact h.zero d hd
  · rw [he _ (by unfold KeepA; omega)]; exact h.first_lt u hu
  · grind [Chazelle.Core.Cluster.AF.first_lt, Chazelle.Core.Cluster.AF.first_v, KeepA]
  · have := v.2; rw [he _ (by unfold KeepA; omega)]; exact h.lev v
  · have := v.2; rw [he _ (by unfold KeepA; omega)]; exact h.par_lt v hv
  · have := v.2; have := h.par_lt v hv
    rw [he (g.base 4 + v) (by unfold KeepA; omega), he _ (by unfold KeepA; omega)]
    exact h.par_eq v hv
  all_goals (grind [Chazelle.Core.Cluster.AF.pv, Chazelle.Core.Cluster.AF.upt, KeepA])

/-- The memory written by stage A. -/
def WrA (g : GV) (a : ℕ) : Prop :=
  (g.A0 ≤ a ∧ a < g.A0 + 7 * g.U) ∨ (g.A0 + 54 * g.U ≤ a ∧ a < g.A0 + 54 * g.U + g.L * g.U)

set_option maxHeartbeats 4000000 in
theorem stageA_exec {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap (Fin g.μ) F (Fin g.N)} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hmap : MapArrays c.nmem g.bO g.bR g.bV g.μ g.N M) (hM : M.Connected) (hμ : 0 < g.μ)
    (hμN : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0)
    (hV : g.bV + g.N ≤ g.A0) (hL : 0 < g.L) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stageA c c' k ∧ k ≤ 62 * g.N + 84 * g.μ + 12 * g.μ * g.L + 7 * g.L + 72 ∧
      WordsBounded W c' ∧ GR g c' ∧ PFr StARG (WrA g) c c' ∧ ∃ T, AF g M T c'.nmem := by
  have hU := g.U_ge
  have hE := g.END_eq
  
  have hLμ : g.L * g.μ ≤ g.L * g.U := Nat.mul_le_mul_left _ (by omega)
  have b0 := g.base_eq 0; have b1 := g.base_eq 1; have b2 := g.base_eq 2; have b3 := g.base_eq 3
  have b4 := g.base_eq 4; have b5 := g.base_eq 5; have b6 := g.base_eq 6; have b7 := g.base_eq 7
  have hGR : ∀ {c1 : Config} {Am : ℕ → Prop}, PFr StARG Am c c1 → GR g c1 := fun hf =>
    hG.frame (fun r hr => hf.1 r (by omega_nf))
  have hmono : ∀ {c0 c1 : Config} {Am : ℕ → Prop}, PFr StARG Am c0 c1 → (∀ a, Am a → WrA g a) →
      PFr StARG (WrA g) c0 c1 := fun hf hA => hf.mono (fun r h => h) hA
  -- `ZERO := 0`
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hz1⟩ := fillWith_exec (P := P) hw hG.one
    (hG.rbase 1 (by omega)) hG.rN hG.zero (by omega_nf) (by omega_nf)
    (by omega_nf) (by omega) (by omega)
  have hf1' : PFr StARG (WrA g) c c1 := hmono (hf1.mono (fun r h => by
    grind [FillRG, StARG]) (fun a h => h)) (fun a h => by unfold WrA; omega)
  have hG1 := hGR hf1'
  -- `LAB := μ`
  obtain ⟨c2, k2, x2, hk2, hw2, hf2, hl2⟩ := fillWith_exec (P := P) hw1 hG1.one
    (hG1.rbase 2 (by omega)) hG1.rμ hG1.rμ (by omega_nf) (by omega_nf)
    (by omega_nf) (by omega) (by omega)
  have hf2' : PFr StARG (WrA g) c1 c2 := hmono (hf2.mono (fun r h => by
    grind [FillRG, StARG]) (fun a h => h)) (fun a h => by unfold WrA; omega)
  have hG2 := hGR (hf1'.trans hf2')
  have m2 : ∀ a, a < g.A0 → c2.nmem a = c.nmem a := fun a ha =>
    (hf1'.trans hf2').2.2.2.2 a (by unfold WrA; omega)
  have hmap2 : MapArrays c2.nmem g.bO g.bR g.bV g.μ g.N M := fun d => by
    have := d.2
    rw [m2 _ (by omega), m2 (g.bR + d) (by omega), m2 (g.bV + d) (by omega)]; exact hmap d
  -- the first darts
  obtain ⟨c3, k3, x3, hk3, hw3, hf3, hF3⟩ := firstP_exec (P := P) hw2 hG2
    (fun d hd => by rw [hmap2.vert hd]; omega)
    (fun u hu => by
      obtain ⟨d, hd⟩ := M.vert_surj ⟨u, hu⟩
      exact ⟨d, d.2, by rw [hmap2.vert d.2, hd]⟩) hV hW
  have hf3' : PFr StARG (WrA g) c2 c3 := hmono hf3 (fun a h => by unfold WrA; omega)
  have hG3 := hGR ((hf1'.trans hf2').trans hf3')
  have m3 : ∀ a, a < g.A0 → c3.nmem a = c.nmem a := fun a ha =>
    ((hf1'.trans hf2').trans hf3').2.2.2.2 a (by unfold WrA; omega)
  have hmap3 : MapArrays c3.nmem g.bO g.bR g.bV g.μ g.N M := fun d => by
    have := d.2
    rw [m3 _ (by omega), m3 (g.bR + d) (by omega), m3 (g.bV + d) (by omega)]; exact hmap d
  have hF3' : ∀ u, u < g.μ → c3.nmem (g.base 0 + u) < g.N ∧
      c3.nmem (g.bV + c3.nmem (g.base 0 + u)) = u := by
    grind
  have hz3 : ∀ d, d < g.N → c3.nmem (g.base 1 + d) = 0 := fun d hd => by
    rw [hf3.2.2.2.2 _ (by omega), hf2.2.2.2.2 _ (by omega)]; grind
  have hl3 : ∀ v, v < g.μ → c3.nmem (g.base 2 + v) = g.μ := fun v hv => by
    rw [hf3.2.2.2.2 _ (by omega)]; grind
  -- the primal search
  obtain ⟨c4, k4, x4, hk4, hw4, hf4, T, hroot, hlev, hlt, hpar, hhead⟩ :=
    bfsP_exec (P := P) hw3 hG3 hmap3 hM hμ hμN hO hR hV hF3' hz3 hl3 hW
  have hf4' : PFr StARG (WrA g) c3 c4 := hmono hf4 (fun a h => by unfold WrA; omega)
  have hG4 := hGR (((hf1'.trans hf2').trans hf3').trans hf4')
  have hrootv : ∀ x (_ : 1 ≤ x) (h2 : x < g.μ), (⟨x, h2⟩ : Fin g.μ) ≠ T.root := by
    grind
  have m4 : ∀ a, a < g.A0 → c4.nmem a = c.nmem a := fun a ha =>
    (((hf1'.trans hf2').trans hf3').trans hf4').2.2.2.2 a (by unfold WrA; omega)
  -- the parent array
  obtain ⟨c5, k5, x5, hk5, hw5, hf5, hp0, hp5⟩ := parP_exec (P := P) hw4 hG4 hμ hV
    (fun x h1 h2 => (hpar ⟨x, h2⟩ (hrootv x h1 h2)).1) hW
  have hf5' : PFr StARG (WrA g) c4 c5 := hmono hf5 (fun a h => by unfold WrA; omega)
  have hG5 := hGR ((((hf1'.trans hf2').trans hf3').trans hf4').trans hf5')
  have hpv5 : ∀ v : Fin g.μ, c5.nmem (g.base 6 + v) = T.parent v := by
    intro v
    by_cases hv : v = T.root
    · subst hv
      rw [SpanTree.parent_root, hroot]
      omega
    · have h1 : 1 ≤ (v : ℕ) := by
        omega
      rw [hp5 v h1 v.2, (hpar v hv).2.2]
      have := (hpar v hv).1
      rw [m4 _ (by omega), m3 _ (by omega)]
  -- the table
  obtain ⟨c6, k6, x6, hk6, hw6, hf6, ht6⟩ := upP_exec (P := P) hw5 hG5 hμ hL
    (fun x hx => by rw [hpv5 ⟨x, hx⟩]; omega) hW
  have hf6' : PFr StARG (WrA g) c5 c6 := hmono hf6 (fun a h => by unfold WrA; omega)
  have hfall := ((((hf1'.trans hf2').trans hf3').trans hf4').trans hf5').trans hf6'
  refine ⟨c6, k1 + (k2 + (k3 + (k4 + (k5 + k6)))),
    .seq x1 (.seq x2 (.seq x3 (.seq x4 (.seq x5 x6)))), by omega, hw6, hGR hfall, hfall, T, ?_⟩
  have m6 : ∀ a, a < g.A0 → c6.nmem a = c.nmem a := fun a ha =>
    hfall.2.2.2.2 a (by unfold WrA; omega)
  refine ⟨fun d => ?_, fun d hd => ?_, fun u hu => ?_, fun u hu => ?_, hroot, fun v => ?_, hlt,
    fun v hv => ?_, fun v hv => ?_, fun v => ?_, fun j hj x hx => ?_, hhead⟩
  · have := d.2
    rw [m6 _ (by omega), m6 (g.bR + d) (by omega), m6 (g.bV + d) (by omega)]; exact hmap d
  · rw [hf6.2.2.2.2 _ (by omega), hf5.2.2.2.2 _ (by omega), hf4.2.2.2.2 _ (by omega)]
    exact hz3 d hd
  · rw [hf6.2.2.2.2 _ (by omega), hf5.2.2.2.2 _ (by omega), hf4.2.2.2.2 _ (by omega)]
    exact (hF3' u hu).1
  · have := (hF3' u hu).1
    rw [hf6.2.2.2.2 (g.base 0 + u) (by omega), hf5.2.2.2.2 (g.base 0 + u) (by omega),
      hf4.2.2.2.2 (g.base 0 + u) (by omega), m6 _ (by omega), ← m3 _ (by omega)]
    exact (hF3' u hu).2
  · have := v.2
    rw [hf6.2.2.2.2 _ (by omega), hf5.2.2.2.2 _ (by omega)]; exact hlev v
  · have := v.2
    rw [hf6.2.2.2.2 _ (by omega), hf5.2.2.2.2 _ (by omega)]; exact (hpar v hv).1
  · have := v.2; have := (hpar v hv).1
    rw [hf6.2.2.2.2 (g.base 4 + v) (by omega), hf5.2.2.2.2 (g.base 4 + v) (by omega),
      m6 _ (by omega), (hpar v hv).2.1, m3 _ (by omega)]
  · have := v.2
    rw [hf6.2.2.2.2 _ (by omega)]; exact hpv5 v
  · rw [ht6 j hj x hx]
    have hagree : ∀ y, y < g.μ → c5.nmem (g.base 6 + y) = upTf T y := by
      intro y hy
      rw [hpv5 ⟨y, hy⟩]; unfold upTf; grind
    exact (iterate_congr_lt (n := g.μ) hagree (fun y hy => upTf_lt T hy) (2 ^ j) x hx).1

end phases

end

end Chazelle.Core.Cluster
