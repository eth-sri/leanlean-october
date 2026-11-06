module

public import Chazelle.Golf

public import Chazelle.Core.BruteRam8
public import Chazelle.Core.Granularize
public import Chazelle.Core.NFBuildMain

/-!
# WP-K: brute-force canonical submaps (`BruteSpec`)

The procedure `bruteStmt sB sG`:

1. `setupS`: constants, top index, orientation bit, tour start, the host and the model descriptor
   of the chain `v_a … v_{a+m}` at the allocator `A₀`;
2. `loopS`: the full vertex-chord map as the chord list `bruteList C` at `A₀ + 10` (naive
   `O(m)` scans per chord, `O(m²)` in all);
3. `finS`: the allocator past the list, and the arguments of the normal-form construction;
4. `sB` (`BuildNFSpec`): the normal form of the full map;
5. `midS`, `sG` (`GranularizeSpec`, degree cap `4`, target `γ`): a `γ`-canonical normal form
   (the full map has degree `≤ 4`, `fullDegLe_chain`, and is `γ`-semigranular,
   `fullMap_semigranular`, for `m = 1` or `γ ≥ 2`);
6. `outS`: the handle to register `3` of band `bBrute`.

Main result: **`brute : BruteSpec`**.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace Brute

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- The allocator past the list, and the arguments of the normal-form construction. -/
def finS : Stmt :=
  block [.copyN 9999 180024, .copyN 40000 180017, .copyN 40001 180018, .copyN 40002 180019]

/-- The arguments of granularity enforcement. -/
def midS : Stmt := block [.copyN 90000 180017, .copyN 90001 40003, .constN 90002 4, .copyN 90003 180002]

/-- The output. -/
def outS : Stmt := .instr (.copyN 180003 90004)

/-- **The brute-force procedure.** -/
def bruteStmt (sB sG : Stmt) : Stmt :=
  .seq (.seq setupS (.seq loopS finS)) (.seq sB (.seq midS (.seq sG outS)))

theorem bandOf_of_bm {r : ℕ} (h : Bm r = true) : bandOf r = bSign ∨ bandOf r = bBrute := by
  unfold Bm Bk at h
  ϴ' Bool.or_eq_true, decide_eq_true_eq at h
  unfold bandOf bSign bBrute
  omega

theorem bm_false_of_band {r : ℕ} (h : bandOf r ∉ bruteBands) : Bm r = false := by
  by_contra h'
  ϴ' Bool.not_eq_false at h'
  rcases bandOf_of_bm h' with e | e <;> Ξ' e at h <;> exact h (⌖)

theorem bbd_bm {r : ℕ} (h : Bm r = false) : Bbd r = false := by
  unfold Bm Bk at h; unfold Bbd Bk
  ϴ' Bool.or_eq_false_iff, decide_eq_false_iff_not at h ⊢
  omega


/-- **Set-up, loop and hand-over.** -/
theorem prep_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) (c : Config) (hw : WordsBounded W c)
    (h0 : c.nreg 180000 = C.s) (h1 : c.nreg 180001 = C.m)
    (hroom : c.nreg ALLOC + 10 + 6 * (2 * C.m + 1) + 3 ≤ W) :
    ∃ c' k, Exec P W (.seq setupS (.seq loopS finS)) c c' k ∧
      k ≤ 260 * C.m + 1900 + ((3300 * C.m + 1402) * (2 * C.m + 1) + 10) + 4 ∧
      c'.nreg 40000 = c.nreg ALLOC + 4 ∧ c'.nreg 40001 = c.nreg ALLOC + 10 ∧
      c'.nreg 40002 = (bruteList C).length ∧ c'.nreg 180017 = c.nreg ALLOC + 4 ∧
      c'.nreg 180002 = c.nreg 180002 ∧
      c'.nreg ALLOC = c.nreg ALLOC + 10 + 3 * (bruteList C).length ∧
      ChordListAt c'.nmem (c.nreg ALLOC + 10) (bruteList C) ∧
      DescMem P C c'.nmem (c.nreg ALLOC) ∧ Frame bruteBands c c' k := by
  have hWn : P.n + 2 * C.m + 8 ≤ W := by unfold hostWords at hWh; omega
  set A₀ := c.nreg ALLOC with hA₀
  obtain ⟨c₁, k₁, e₁, hk₁, lb₁, X₁, D₁, low₁, s19, s24, R₁, RR₁, RM₁, O₁⟩ := setup_exec (P := P) hG
    (⋄) (⋄) hC hsn c hw h0 h1 (⋄)
  obtain ⟨c₂, k₂, e₂, hk₂, lb₂, X₂, t19, t24, tL, tM, R₂, RR₂, RM₂, O₂⟩ := loopS_exec (P := P) hG
    hWn (by unfold hostWords at hWh; omega) hC hsn (γ := c.nreg 180002) (A₀ := A₀) (⋄) c₁
    e₁.wb_right X₁ s19 s24
  have hlen := pre_length_le C (2 * C.m + 1)
  Ξ' pre_full at hlen
  obtain ⟨c₃, k₃, e₃, hk₃, q9999, q0, q1, q2, R₃, RR₃, M₃, RM₃, O₃⟩ : ∃ c₃ k₃, Exec P W finS c₂ c₃ k₃ ∧ k₃ = 4 ∧
      c₃.nreg 9999 = A₀ + 10 + 3 * (bruteList C).length ∧ c₃.nreg 40000 = A₀ + 4 ∧
      c₃.nreg 40001 = A₀ + 10 ∧ c₃.nreg 40002 = (bruteList C).length ∧
      (∀ r, r ≠ 9999 → r ≠ 40000 → r ≠ 40001 → r ≠ 40002 → c₃.nreg r = c₂.nreg r) ∧
      c₃.rreg = c₂.rreg ∧ c₃.nmem = c₂.nmem ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have w := e₂.wb_right
    unfold finS
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩ <;>
      simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
    · exact t24
    · exact X₂.2.2.2.2.2.2.2.2.2.1
    · exact X₂.2.2.2.2.2.2.2.2.2.2.1
    · exact t19
  have x17 := X₂.2.2.2.2.2.2.2.2.2.1
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), ⋄, q0, q1, q2, ?_, ?_, q9999, ?_, ?_, ?_⟩
  · Ξ R₃ _ (⌖) (⌖) (⌖) (⌖), x17
  · Ξ R₃ _ (⌖) (⌖) (⌖) (⌖), X₂.2.2.1
  · rw [M₃]; exact tL
  · rw [M₃]; exact descMem_agree D₁ fun a ha => tM a ha
  · refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
    · have hb := bm_false_of_band hr
      have h4 : r ≠ 40000 ∧ r ≠ 40001 ∧ r ≠ 40002 := by
        refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact hr (⌖)
      Ξ R₃ r hra h4.1 h4.2.1 h4.2.2, R₂ r (bbd_bm hb), R₁ r hb
    · have hb := bm_false_of_band hr
      Ξ RR₃, RR₂ r (bbd_bm hb), RR₁ r hb
    · Ξ M₃, tM a (⋄), low₁ a ha
    · Ξ RM₃, RM₂, RM₁
    · Ξ O₃, O₂, O₁
    · have : c₃.nreg ALLOC = A₀ + 10 + 3 * (bruteList C).length := q9999
      rw [this]; omega
    · have : c₃.nreg ALLOC = A₀ + 10 + 3 * (bruteList C).length := q9999
      rw [this]; omega

/-! ## Cost arithmetic -/

theorem f_le {m K : ℕ} (hK : K ≤ 2 * (2 * m + 1)) :
    K * (Nat.clog 2 K + 1) + 1 ≤ 30 * (m + 1) ^ 2 := by
  have hc := Cost.clog_two_le_self K
  have h1 : K * (Nat.clog 2 K + 1) ≤ K * (K + 1) := Nat.mul_le_mul_left _ (⋄)
  have h2 : K * (K + 1) ≤ (4 * m + 2) * (4 * m + 3) :=
    Nat.mul_le_mul (⋄) (⋄)
  nlinarith

theorem cost_ok {m K κB κG : ℕ} (hm : 1 ≤ m) (hK : K ≤ 2 * (2 * m + 1)) :
    260 * m + 1900 + ((3300 * m + 1402) * (2 * m + 1) + 10) + 4 + 10 + 3 * K +
      κB * (K * (Nat.clog 2 K + 1) + 1) + 4 + κG * (K * (Nat.clog 2 K + 1) + 1) + 1 ≤
      (20000 + 30 * κB + 30 * κG) * (m + 1) ^ 3 := by
  have hf := f_le hK
  have hsq : (m + 1) ^ 2 ≤ (m + 1) ^ 3 := Nat.pow_le_pow_right (⋄) (⋄)
  have hB : κB * (K * (Nat.clog 2 K + 1) + 1) ≤ 30 * κB * (m + 1) ^ 3 := by
    calc κB * (K * (Nat.clog 2 K + 1) + 1) ≤ κB * (30 * (m + 1) ^ 2) := Nat.mul_le_mul_left _ hf
      _ ≤ κB * (30 * (m + 1) ^ 3) := Nat.mul_le_mul_left _ (⋄)
      _ = 30 * κB * (m + 1) ^ 3 := ⋆
  have hG : κG * (K * (Nat.clog 2 K + 1) + 1) ≤ 30 * κG * (m + 1) ^ 3 := by
    calc κG * (K * (Nat.clog 2 K + 1) + 1) ≤ κG * (30 * (m + 1) ^ 2) := Nat.mul_le_mul_left _ hf
      _ ≤ κG * (30 * (m + 1) ^ 3) := Nat.mul_le_mul_left _ (⋄)
      _ = 30 * κG * (m + 1) ^ 3 := ⋆
  have hsmall : 260 * m + 1900 + ((3300 * m + 1402) * (2 * m + 1) + 10) + 4 + 10 + 3 * K + 4 + 1 ≤
      20000 * (m + 1) ^ 3 := ⊞
  nlinarith

/-- The chord family of a normal form built from a list is the family of the list. -/
theorem nfF_eq {M : Model} {Q : Polygon} {N : NF} {L : List (ℕ × ℕ × ℕ)}
    (h : N.chords.map (fun r => (r.h, r.lp, r.rp)) = L) :
    N.F M Q = {c | ∃ x ∈ L, c = (recOf x).toSet M Q} := by
  ext c
  ϴ NF.F, Set.mem_ofPred_eq, ← h, List.mem_map
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨_, ⟨r, hr, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩; exact ⟨r, hr, rfl⟩

end

end Brute

open Brute Machine Machine.Stmt Programs in
set_option maxHeartbeats 8000000 in
/-- **WP-K: `BruteSpec`** — brute-force `γ`-canonical normal forms of chains. -/
public theorem brute : BruteSpec := by
  obtain ⟨sB, κB, hB⟩ := buildNF
  obtain ⟨sG, κG, hGr⟩ := granularize
  refine ⟨bruteStmt sB sG, 20000 + 30 * κB + 30 * κG 4, ?_⟩
  intro P W c hw ⟨hG, hWh, hm1, hsn, hγ1, hγ⟩ hroom
  beta_reduce at hroom
  have r0 : rd c bBrute 0 = c.nreg 180000 := rfl
  have r1 : rd c bBrute 1 = c.nreg 180001 := rfl
  have r2 : rd c bBrute 2 = c.nreg 180002 := rfl
  rw [r0, r1] at hsn
  rw [r1] at hm1 hroom
  rw [r1] at hγ
  rw [r2] at hγ1 hγ
  have hQn : (Qof P).n = P.n := shear_n _ _
  let C : Chain := ⟨Qof P, c.nreg 180000, c.nreg 180001, hm1, by rw [hQn]; omega⟩
  have hC : C.P = Qof P := rfl
  have hP : C.P.Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hDH : DistinctHeights C.P := (goodShear_epsOf hG.2).2.1
  have hsnC : C.s + C.m + 1 ≤ P.n := hsn
  set A₀ := c.nreg ALLOC with hA₀
  set m := c.nreg 180001 with hmd
  set γ := c.nreg 180002 with hγd
  set K := (bruteList C).length with hKd
  have hK : K ≤ 2 * (2 * m + 1) := by
    have := pre_length_le C (2 * C.m + 1); rw [pre_full] at this; exact this
  set f := K * (Nat.clog 2 K + 1) + 1 with hfd
  have hcost := cost_ok (κB := κB) (κG := κG 4) hm1 hK
  rw [← hfd] at hcost
  have hWn : P.n + 3 ≤ W := by unfold hostWords at hWh; omega
  -- 1. set-up, loop, hand-over
  obtain ⟨c₃, k₃, e₃, hk₃, q0, q1, q2, q17, q2γ, qA, qL, qD, F₃⟩ := prep_exec (P := P) hG hWh hC
    hsnC c hw rfl rfl (by nlinarith)
  have hn1 : 1 ≤ P.n := by omega
  have hsP : C.s < P.n := by omega
  -- 2. the normal form of the full map
  obtain ⟨hMD₃, hWF₃⟩ := descMem_model hC hn1 hsP qD (E := c₃.nreg ALLOC) (by rw [qA]; omega)
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  obtain ⟨c₄, k₄, e₄, hk₄, post₄, F₄⟩ := hB P W c₃ e₃.wb_right
    ⟨hG, hWh, by show ModelDescWF P (c₃.nreg ALLOC) c₃.nmem (c₃.nreg 40000); rw [q0]; exact hWF₃,
      chainModel C, bruteList C, by show ModelDescAt c₃.nmem (c₃.nreg 40000) _ _; rw [q0]; exact hMD₃,
      hGM, q2, by show c₃.nreg 40001 + 3 * K ≤ c₃.nreg ALLOC; rw [q1, qA],
      by show ChordListAt c₃.nmem (c₃.nreg 40001) _; rw [q1]; exact qL, bruteList_ok hP hDH⟩
    (by show c₃.nreg ALLOC + κB * (c₃.nreg 40002 * (Nat.clog 2 (c₃.nreg 40002) + 1) + 1) ≤ W
        rw [q2, qA]; nlinarith)
  obtain ⟨N, hA₄, hNW₄, hNF, hmap, -⟩ := post₄ (chainModel C) (bruteList C)
    (by show ModelDescAt c₃.nmem (c₃.nreg 40000) _ _; rw [q0]; exact hMD₃) q2
    (by show ChordListAt c₃.nmem (c₃.nreg 40001) _; rw [q1]; exact qL)
  have hNlen : N.chords.length = K := by
    have := congrArg List.length hmap; rwa [List.length_map] at this
  -- the band-18 registers survive the construction
  have k17 : c₄.nreg 180017 = A₀ + 4 := by
    rw [F₄.1 _ (by decide) (by decide), q17]
  have k2 : c₄.nreg 180002 = γ := by rw [F₄.1 _ (by decide) (by decide), q2γ]
  have hk4 : k₄ ≤ κB * f := by
    beta_reduce at hk₄
    have : rd c₃ bBuild 2 = K := q2
    rw [this] at hk₄; exact hk₄
  have hA4 : c₄.nreg ALLOC ≤ c₃.nreg ALLOC + κB * f := by have := F₄.2.2.2.2.2.2; omega
  -- 3. the arguments of granularity enforcement
  obtain ⟨c₅, k₅, e₅, hk₅, p0, p1, p2, p3, R₅, RR₅, M₅, RM₅, O₅⟩ : ∃ c₅ k₅, Exec P W midS c₄ c₅ k₅ ∧
      k₅ = 4 ∧ c₅.nreg 90000 = A₀ + 4 ∧ c₅.nreg 90001 = rd c₄ bBuild 3 ∧ c₅.nreg 90002 = 4 ∧
      c₅.nreg 90003 = γ ∧
      (∀ r, r ≠ 90000 → r ≠ 90001 → r ≠ 90002 → r ≠ 90003 → c₅.nreg r = c₄.nreg r) ∧
      c₅.rreg = c₄.rreg ∧ c₅.nmem = c₄.nmem ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    have w := e₄.wb_right
    unfold midS
    exec_block
    · omega
    · refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩ <;>
        simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
      · exact k17
      · rfl
      · exact k2
  have A₅ : c₅.nreg ALLOC = c₄.nreg ALLOC := R₅ _ (by decide) (by decide) (by decide) (by decide)
  have hlow₅ : ∀ x, x < c₃.nreg ALLOC → c₅.nmem x = c₃.nmem x := fun x hx => by
    rw [M₅]; exact F₄.2.2.1 x hx
  have qD₅ : DescMem P C c₅.nmem A₀ := descMem_agree qD fun x hx => hlow₅ x (by rw [qA]; omega)
  obtain ⟨hMD₅, hWF₅⟩ := descMem_model hC hn1 hsP qD₅ (E := c₅.nreg ALLOC)
    (by rw [A₅]; have := F₄.2.2.2.2.2.1; rw [qA] at this; omega)
  have hNW₅ : NFWithin c₅.nmem (c₅.nreg 90001) (c₅.nreg ALLOC) N := by
    rw [p1, A₅, M₅]; exact hNW₄
  have hF : N.F (chainModel C) (Qof P) = C.chords := by rw [nfF_eq hmap]; exact bruteList_set hP hDH
  have hdeg : (chainModel C).DegLe (N.F (chainModel C) (Qof P)) 4 := by
    rw [hF]
    have := fullDegLe_chain hP hDH (Qof P) ∅ ⟨Set.finite_empty, Set.empty_subset _,
      fun c hc => hc.elim⟩
    rwa [Set.union_empty] at this
  have hsemi : (chainModel C).Semigranular (N.F (chainModel C) (Qof P)) γ := by
    rw [hF]
    exact fullMap_semigranular hP hDH (by rcases hγ with h | h; exact Or.inl ⟨h, hγ1⟩; exact Or.inr h)
  have hK₅ : c₅.nmem (c₅.nreg 90001) = K := by rw [← hNlen]; exact hNW₅.nfAt.1
  -- 4. granularity enforcement
  obtain ⟨c₆, k₆, e₆, hk₆, post₆, F₆⟩ := hGr P W c₅ e₅.wb_right
    ⟨hG, hWh, by show 1 ≤ c₅.nreg 90002; rw [p2]; omega,
      by show ModelDescWF P (c₅.nreg ALLOC) c₅.nmem (c₅.nreg 90000); rw [p0]; exact hWF₅,
      chainModel C, N, by show ModelDescAt c₅.nmem (c₅.nreg 90000) _ _; rw [p0]; exact hMD₅, hGM,
      hNW₅, hNF, by show (chainModel C).DegLe _ (c₅.nreg 90002); rw [p2]; exact hdeg,
      by show (chainModel C).Semigranular _ (c₅.nreg 90003); rw [p3]; exact hsemi⟩
    (by show c₅.nreg ALLOC + κG (c₅.nreg 90002) * (c₅.nmem (c₅.nreg 90001) *
          (Nat.clog 2 (c₅.nmem (c₅.nreg 90001)) + 1) + 1) ≤ W
        rw [p2, hK₅, A₅, ← hfd]; rw [qA] at hA4; nlinarith)
  obtain ⟨N', hA₆, hNW₆, -, hcan⟩ := post₆ (chainModel C) N
    (by show ModelDescAt c₅.nmem (c₅.nreg 90000) _ _; rw [p0]; exact hMD₅) hNW₅.nfAt
  have hk6 : k₆ ≤ κG 4 * f := by
    beta_reduce at hk₆
    have e : rd c₅ bGran 2 = 4 := p2
    have e' : c₅.nmem (rd c₅ bGran 1) = K := hK₅
    rw [e, e', ← hfd] at hk₆; exact hk₆
  -- 5. the output
  have e₇ := Exec.copyN (P := P) e₆.wb_right 180003 90004
  set c₇ : Config := { c₆ with nreg := upd c₆.nreg 180003 (c₆.nreg 90004) } with hc₇
  have ex : Exec P W (bruteStmt sB sG) c c₇ (k₃ + (k₄ + (k₅ + (k₆ + 1)))) :=
    .seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))
  refine ⟨c₇, _, ex, ?_, ⟨C, N', rfl, rfl, rfl, ?_, ?_⟩, ?_⟩
  · show _ ≤ (20000 + 30 * κB + 30 * κG 4) * (m + 1) ^ 3
    nlinarith
  · show Robust (c₇.nreg ALLOC) c₇.nmem fun m' => NFAt m' (c₇.nreg 180003) N'
    have e1 : c₇.nreg ALLOC = c₆.nreg ALLOC := by rw [hc₇]; simp [ALLOC]
    have e2 : c₇.nreg 180003 = c₆.nreg 90004 := by rw [hc₇]; simp
    rw [e1, e2]; exact hNW₆
  · have e3 : rd c₅ bGran 3 = γ := p3
    have e2 : rd c₅ bGran 2 = 4 := p2
    rw [e3, e2] at hcan; rw [r2]; exact hcan
  · -- the frame
    have F₅ : Frame {bGran} c₄ c₅ k₅ := ⟨fun r hr _ => R₅ r (by rintro rfl; exact hr (by decide))
      (by rintro rfl; exact hr (by decide)) (by rintro rfl; exact hr (by decide))
      (by rintro rfl; exact hr (by decide)), fun r _ => by rw [RR₅], fun a _ => by rw [M₅],
      fun a _ => by rw [RM₅], O₅, by rw [A₅], by rw [A₅]; omega⟩
    have F₇ : Frame {bBrute} c₆ c₇ 1 := ⟨fun r hr _ => by
        rw [hc₇]; simp only [Config.nreg_mk]; rw [upd_other _ _ _ (by rintro rfl; exact hr (by decide))],
      fun r _ => rfl, fun a _ => rfl, fun a _ => rfl, rfl, by rw [hc₇]; simp [ALLOC],
      by rw [hc₇]; simp [ALLOC]⟩
    have := ((((F₃.trans F₄).trans F₅).trans F₆).trans F₇).mono (B' := bruteBands) (by decide)
      (k' := k₃ + (k₄ + (k₅ + (k₆ + 1)))) (by omega)
    exact this

end Chazelle.Core
