module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseOracleRamA

/-!
# WP-M (E7-B, RAM part 2): index helpers, the origin, the normalized query

* `ivS d p`, `iEdgeS d p`: the vertex of `Q` at walk vertex `p`, the walk edge carrying the edge
  `p` of `Q` (`iv`, `iEdge`), from the orientation bit `170014`;
* `originI`: the origin of the query as a symbolic point of `Q` (`oSym`) in `170020 … 170022`;
  `oSym_spec`: it is in range, evaluates to the origin, and lies within the coordinate bound.
-/


namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK

@[expose] public section

variable {Q : Polygon}

/-! ## The origin as a symbolic point -/

/-- **The symbolic origin**: a walk position of the interior walk as a symbolic point of `Q`. -/
noncomputable def oSym (Q : Polygon) : Origin → SymPt
  | .sym p => p
  | .walk ⟨e, 0⟩ => .vtx (iv Q e)
  | .walk ⟨e, h + 1⟩ => .onEdge (iEdge Q e) h

/-- The edge of `Q` carrying the walk edge `e` (as `ShootCut.edgeOf` names it). -/
theorem edgeOf_iv (hn : 3 ≤ Q.n) {e : ℕ} (he : e < Q.n) :
    ShootCut.edgeOf Q.n (.vtx (iv Q e)) (.vtx (iv Q ((e + 1) % Q.n))) = iEdge Q e := by
  unfold iv iEdge
  by_cases hL : Mountain.LeftInside Q
  · simp only [hL, ↓reduceIte, ShootCut.edgeOf]
  · simp only [hL, ↓reduceIte, ShootCut.edgeOf]
    by_cases h1 : e + 1 < Q.n
    · rw [Nat.mod_eq_of_lt h1, ite_eq_left h1]
      rw [ite_eq_right]
      · omega
      · intro hc
        rcases (show Q.n - 1 - e + 1 < Q.n ∨ Q.n - 1 - e + 1 = Q.n by omega) with h2 | h2
        · rw [Nat.mod_eq_of_lt h2] at hc; omega
        simp_all [Nat.mod_self] <;> omega_nf
    · rw [show e + 1 = Q.n by omega, Nat.mod_self]
      simp only [lt_irrefl, ↓reduceIte]
      rw [ite_eq_right]
      · omega
      · intro hc
        rw [show Q.n - 1 - e = 0 by omega, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hc
        omega

/-- **The symbolic origin** is in range, evaluates to the origin and lies within the coordinate
bound (so it is an inner point of every chain model of `Q`). -/
theorem oSym_spec (hD : DistinctHeights Q) (hn : 3 ≤ Q.n) {o : Origin}
    (hol : o.Lt Q.n (interiorModel Q))
    (hof : (∃ p, o = .walk ⟨p, 0⟩) ∨ ((interiorModel Q).InnerPt (o.eval (interiorModel Q) Q) ∧
      ∀ x, o = .walk x → ProperPos (interiorModel Q) Q Q.n x)) :
    (oSym Q o).Lt Q.n ∧ (oSym Q o).eval Q = o.eval (interiorModel Q) Q ∧
      |(o.eval (interiorModel Q) Q).1| ≤ Jordan.coordBound Q ∧
      |(o.eval (interiorModel Q) Q).2| ≤ Jordan.coordBound Q := by
  have hbd : (interiorModel Q).InnerPt (o.eval (interiorModel Q) Q) →
      |(o.eval (interiorModel Q) Q).1| ≤ Jordan.coordBound Q ∧
      |(o.eval (interiorModel Q) Q).2| ≤ Jordan.coordBound Q := innerPt_interior_bound
  cases o with
  | sym p =>
    aesop
  | walk x =>
    obtain ⟨e, h⟩ := x
    have he : e < Q.n := by have := hol.1; simp_all [mi_n] <;> omega_nf
    cases h with
    | zero =>
      have hv : Origin.eval (interiorModel Q) Q (.walk ⟨e, 0⟩) = Q.vtx (iv Q e) := by
        show Chazelle.Geometry.lerp _ _ 0 = _
        rw [Chazelle.Geometry.lerp_zero, mi_wa he]
      rw [hv]
      exact ⟨iv_lt he, rfl, Jordan.abs_fst_vtx_le_coordBound Q (iv_lt he),
        Jordan.abs_snd_vtx_le_coordBound Q (iv_lt he)⟩
    | succ h =>
      rcases hof with ⟨q, hq⟩ | ⟨hin, hpp⟩
      · ram_all
      have hpp' := hpp ⟨e, h + 1⟩ rfl
      have hh : h < Q.n := by have := hpp'.2.2; simp_all
      have hnh : ((interiorModel Q).wa e).2 ≠ ((interiorModel Q).wb e).2 := by
        rw [mi_wa he, mi_wb he]
        refine hD _ _ (iv_lt he) (iv_lt (Nat.mod_lt _ (by omega))) ?_
        unfold iv
        split_ifs
        · intro hc
          rcases (show e + 1 < Q.n ∨ e + 1 = Q.n by omega) with h3 | h3
          · rw [Nat.mod_eq_of_lt h3] at hc; omega
          grind [Nat.mod_self]
        · intro hc
          rcases (show e + 1 < Q.n ∨ e + 1 = Q.n by omega) with h3 | h3
          · rw [Nat.mod_eq_of_lt h3] at hc; omega
          simp_all [Nat.mod_self] <;> omega_nf
      have hok : HostEdgeOK Q.n (.vtx (iv Q e)) (.vtx (iv Q ((e + 1) % Q.n))) := by
        simp only [HostEdgeOK, iv]
        split_ifs
        · left; rfl
        · right
          rcases (show e + 1 < Q.n ∨ e + 1 = Q.n by omega) with h3 | h3
          · rw [Nat.mod_eq_of_lt h3]; rw [Nat.mod_eq_of_lt (by omega)]; omega
          · rw [h3, Nat.mod_self, show Q.n - 1 - 0 + 1 = Q.n by omega, Nat.mod_self]; omega
      have hpos := ShootCut.pos_eq_onEdge (interiorModel Q) hD (by omega) (p := e) (h := h)
        (sp₁ := .vtx (iv Q e)) (sp₂ := .vtx (iv Q ((e + 1) % Q.n))) (mi_wa he) (mi_wb he)
        (iv_lt he) (iv_lt (Nat.mod_lt _ (by omega))) hok hnh
      rw [edgeOf_iv hn he] at hpos
      refine ⟨⟨iEdge_lt (by omega) he, hh⟩, hpos.symm, hbd hin⟩

/-! ## Index helpers on the RAM (input `170095`, output `170096`, scratch `170092`) -/

/-- `170096 := iv 170095` (the vertex of `Q` at a walk vertex). -/
def ivF : Stmt :=
  .ifLtN 170014 170011 (.instr (.subN 170096 170019 170095)) (.instr (.copyN 170096 170095))

/-- The value `ivF` computes, from the orientation bit `b` and `n - 1`. -/
def ivV (b n1 p : ℕ) : ℕ := if b < 1 then n1 - p else p

theorem ivF_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h11 : c.nreg 170011 = 1) :
    ∃ c' k, Exec P W ivF c c' k ∧ k ≤ 3 ∧
      c' = { c with nreg := upd c.nreg 170096 (ivV (c.nreg 170014) (c.nreg 170019) (c.nreg 170095)) } := by
  unfold ivF ivV
  by_cases h : c.nreg 170014 < c.nreg 170011
  · exact ⟨_, _, .ifLtN_true h (Exec.subN hw 170096 170019 170095), by omega,
      by ram_grind⟩
  · exact ⟨_, _, .ifLtN_false h (Exec.copyN hw 170096 170095), by omega,
      by ram_grind⟩

/-- `ivV` is `iv` for the orientation bit of `Q`. -/
theorem ivV_eq {b : ℕ} (hb : b = 1 ↔ Mountain.LeftInside Q) (hb1 : b ≤ 1) (p : ℕ) :
    ivV b (Q.n - 1) p = iv Q p := by
  core_grind

/-- `170096 := iEdge 170095` (the walk edge carrying an edge of `Q`). -/
def iEdgeF : Stmt :=
  .ifLtN 170014 170011
    (.seq (block [.addN 170092 170095 170011])
      (.ifLtN 170092 170010 (block [.subN 170096 170019 170095, .subN 170096 170096 170011])
        (block [.copyN 170096 170019])))
    (block [.copyN 170096 170095])

/-- The value `iEdgeF` computes. -/
def iEdgeV (b n p : ℕ) : ℕ := if b < 1 then (if p + 1 < n then n - 1 - p - 1 else n - 1) else p

theorem iEdgeF_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h11 : c.nreg 170011 = 1) (h10 : c.nreg 170010 = P.n) (h19 : c.nreg 170019 = P.n - 1)
    (hp : c.nreg 170095 + 1 ≤ W) :
    ∃ c' k, Exec P W iEdgeF c c' k ∧ k ≤ 7 ∧
      c'.nreg 170096 = iEdgeV (c.nreg 170014) P.n (c.nreg 170095) ∧
      (∀ r, r ≠ 170096 → r ≠ 170092 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold iEdgeF iEdgeV
  by_cases h : c.nreg 170014 < c.nreg 170011
  · refine spec_ifLtN_true h ?_
    refine spec_seq ?_
    exec_block
    · omega
    by_cases h2 : c.nreg 170095 + 1 < P.n
    · refine spec_ifLtN_true (by ram_simp) ?_
      exec_block
      refine ⟨by omega, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; grind
      · ram_simp
    · refine spec_ifLtN_false (by ram_simp) ?_
      exec_block
      simp_all
  · refine spec_ifLtN_false h ?_
    exec_block
    simp_all

/-- `iEdgeV` is `iEdge` for the orientation bit of `Q`. -/
theorem iEdgeV_eq {b : ℕ} (hb : b = 1 ↔ Mountain.LeftInside Q) (hb1 : b ≤ 1) (p : ℕ) :
    iEdgeV b Q.n p = iEdge Q p := by
  grind [iEdgeV, iEdge]

/-! ## The static environment -/

/-- The static data of an interior query. -/
structure Stat where
  /-- The entry allocator (the host record). -/
  A₀ : ℕ
  /-- The entry memory. -/
  m₀ : ℕ → ℕ
  /-- The context handle. -/
  h : ℕ
  /-- The weight bound. -/
  γ : ℕ
  /-- The subarc ends. -/
  e₁ : ℕ
  h₁ : ℕ
  e₂ : ℕ
  h₂ : ℕ
  /-- The direction code. -/
  dir : ℕ
  /-- The symbolic origin. -/
  o : SymPt

/-- The host record `Host.whole n` at `A`: one run item `0 … n - 1`. -/
theorem hostAt_whole {m : ℕ → ℕ} {A n : ℕ} (h0 : m A = 1) (h1 : m (A + 1) = 0) (h2 : m (A + 2) = 0)
    (h3 : m (A + 3) = n - 1) : HostAt m A (Host.whole n) := by
  refine ⟨by core_grind, fun i hi => ?_⟩
  simp_all [Host.whole, List.length_cons, List.length_nil, List.getD_cons_zero] <;> omega_nf

/-- **The static environment** of the adapter at `c`: the saved inputs and constants in band
`17`, the symbolic origin, the entry memory below `A₀`, the host record at `A₀`, the grade
table and the weight bound. -/
structure SEnv (P : Polygon) (W : ℕ) (O : OracleIface) (s : Stat) (c : Config) : Prop where
  good : GoodEnv P
  hW : hostWords P.n ≤ W
  r1 : c.nreg 170001 = s.e₁
  r2 : c.nreg 170002 = s.h₁
  r3 : c.nreg 170003 = s.e₂
  r4 : c.nreg 170004 = s.h₂
  r8 : c.nreg 170008 = s.dir
  r9 : c.nreg 170009 = s.γ
  r13 : c.nreg 170013 = s.h
  r10 : c.nreg 170010 = P.n
  r11 : c.nreg 170011 = 1
  r12 : c.nreg 170012 = 0
  r18 : c.nreg 170018 = 2
  r19 : c.nreg 170019 = P.n - 1
  lb : c.nreg 170014 = 1 ↔ Mountain.LeftInside (Qof P)
  lb1 : c.nreg 170014 ≤ 1
  r15 : c.nreg 170015 = s.A₀
  r16 : c.nreg 170016 = s.m₀ (s.h + 2)
  r17 : c.nreg 170017 = s.m₀ (s.h + 3)
  org : SymPtIn c 170020 s.o
  mem : ∀ a, a < s.A₀ → c.nmem a = s.m₀ a
  host0 : c.nmem s.A₀ = 1
  host1 : c.nmem (s.A₀ + 1) = 0
  host2 : c.nmem (s.A₀ + 2) = 0
  host3 : c.nmem (s.A₀ + 3) = P.n - 1
  alloc : s.A₀ + 8 ≤ c.nreg ALLOC
  grade : Robust s.A₀ s.m₀ (fun m => GradeRaw O P m s.h s.A₀)
  cap : s.γ ≤ 2 ^ (s.m₀ s.h - 1)

namespace SEnv

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat} {c c' : Config}

section
variable (h : SEnv P W O s c)
include h
/-- **The static environment survives** every step that keeps the registers `170000 … 170029`,
the memory below the allocator, and does not lower the allocator. -/
theorem keep (hr : ∀ r, 170000 ≤ r → r < 170030 → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    SEnv P W O s c' := by
  have k : ∀ r, 170000 ≤ r → r < 170030 → c'.nreg r = c.nreg r := hr
  have hal := h.alloc
  refine ⟨h.good, h.hW, (k _ (by omega) (by omega)).trans h.r1, (k _ (by omega) (by omega)).trans h.r2,
    (k _ (by omega) (by omega)).trans h.r3, (k _ (by omega) (by omega)).trans h.r4,
    (k _ (by omega) (by omega)).trans h.r8, (k _ (by omega) (by omega)).trans h.r9,
    (k _ (by omega) (by omega)).trans h.r13, (k _ (by omega) (by omega)).trans h.r10,
    (k _ (by omega) (by omega)).trans h.r11, (k _ (by omega) (by omega)).trans h.r12,
    (k _ (by omega) (by omega)).trans h.r18, (k _ (by omega) (by omega)).trans h.r19,
    by ram_grind, by ram_grind,
    (k _ (by omega) (by omega)).trans h.r15, (k _ (by omega) (by omega)).trans h.r16,
    (k _ (by omega) (by omega)).trans h.r17,
    NFLoc.symPtIn_copy h.org (k _ (by omega) (by omega)) (k _ (by omega) (by omega))
      (k _ (by omega) (by omega)),
    fun a ha => (hm a (by omega)).trans (h.mem a ha), (hm _ (by omega)).trans h.host0,
    (hm _ (by omega)).trans h.host1, (hm _ (by omega)).trans h.host2,
    (hm _ (by omega)).trans h.host3, by omega, h.grade, h.cap⟩

theorem n3 : 3 ≤ P.n := Chazelle.Jordan.simple_three_le h.good.1

theorem nW : P.n + 3 ≤ W := by have := h.hW; grind [hostWords]

theorem hostAt : HostAt c.nmem s.A₀ (Host.whole P.n) :=
  hostAt_whole h.host0 h.host1 h.host2 h.host3


end

theorem qn : (Qof P).n = P.n := shear_n _ _

section
variable (h : SEnv P W O s c) (p : ℕ)
include h
theorem ivv :
    ivV (c.nreg 170014) (c.nreg 170019) p = iv (Qof P) p := by
  rw [h.r19, ← qn]; exact ivV_eq h.lb h.lb1 p

theorem iev :
    iEdgeV (c.nreg 170014) P.n p = iEdge (Qof P) p := by
  rw [← qn]; exact iEdgeV_eq h.lb h.lb1 p


end

end SEnv

/-! ## The origin on the RAM -/

/-- **The symbolic origin** into `170020 … 170022`. -/
def originI : Stmt :=
  .ifLtN 170005 170018
    (block [.copyN 170020 170005, .copyN 170021 170006, .copyN 170022 170007])
    (.ifLtN 170012 170007
      (.seq (block [.constN 170020 1, .subN 170022 170007 170011, .copyN 170095 170006])
        (.seq iEdgeF (block [.copyN 170021 170096])))
      (.seq (block [.constN 170020 0, .copyN 170095 170006])
        (.seq ivF (block [.copyN 170021 170096]))))

/-- The registers `originI` writes. -/
def BorgR (r : ℕ) : Prop :=
  r = 170020 ∨ r = 170021 ∨ r = 170022 ∨ r = 170092 ∨ r = 170095 ∨ r = 170096

section
variable {P : Polygon} {W : ℕ}
theorem originI_exec (c : Config) (hw : WordsBounded W c)
    (hn : 3 ≤ P.n) (h11 : c.nreg 170011 = 1) (h10 : c.nreg 170010 = P.n)
    (h12 : c.nreg 170012 = 0) (h18 : c.nreg 170018 = 2) (h19 : c.nreg 170019 = P.n - 1)
    (hlb : c.nreg 170014 = 1 ↔ Mountain.LeftInside (Qof P)) (hlb1 : c.nreg 170014 ≤ 1)
    {o : Origin} (ho : OriginIn c 170005 o) (hol : o.Lt P.n (interiorModel (Qof P)))
    (hW : P.n + 3 ≤ W) :
    ∃ c' k, Exec P W originI c c' k ∧ k ≤ 14 ∧ SymPtIn c' 170020 (oSym (Qof P) o) ∧
      (∀ r, ¬ BorgR r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hQ : (Qof P).n = P.n := shear_n _ _
  have hvv : ∀ p, ivV (c.nreg 170014) (c.nreg 170019) p = iv (Qof P) p := fun p => by
    rw [h19, ← hQ]; exact ivV_eq hlb hlb1 p
  have hev : ∀ p, iEdgeV (c.nreg 170014) P.n p = iEdge (Qof P) p := fun p => by
    rw [← hQ]; exact iEdgeV_eq hlb hlb1 p
  unfold originI
  cases o with
  | sym p =>
    have hk : c.nreg 170005 < c.nreg 170018 := by
      rw [h18]; cases p with
      | vtx i => rw [ho.1]; omega
      | onEdge e h => rw [ho.1]; omega
    refine spec_ifLtN_true hk ?_
    exec_block
    refine ⟨by omega, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · refine NFLoc.symPtIn_copy ho (by config_simp) (by config_simp) (by config_simp)
    simp_all [BorgR, Config.nreg_mk, upd] <;> omega_nf
  | walk x =>
    obtain ⟨e, hh⟩ := x
    obtain ⟨k2, k6, k7⟩ := ho
    have k6' : c.nreg 170006 = e := k6
    have k7' : c.nreg 170007 = hh := k7
    have hk : ¬ c.nreg 170005 < c.nreg 170018 := by omega
    refine spec_ifLtN_false hk ?_
    have he : e < P.n := by have := hol.1; simp_all [mi_n] <;> omega_nf
    have hhn : hh ≤ P.n := hol.2
    cases hh with
    | zero =>
      refine spec_ifLtN_false (by omega) ?_
      refine spec_seq ?_
      exec_block
      all_goals first | omega | skip
      refine spec_seq ?_
      obtain ⟨c₁, k₁, e₁, hk₁, rfl⟩ := ivF_exec (P := P) _ ‹_› (by ram_simp)
      refine ⟨_, _, e₁, ?_⟩
      have w₁ := e₁.wb_right
      exec_block
      refine ⟨by omega, ⟨by config_simp, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · simp_all
      simp_all [BorgR, Config.nreg_mk, upd] <;> omega_nf
    | succ h =>
      refine spec_ifLtN_true (by omega) ?_
      refine spec_seq ?_
      exec_block
      all_goals first | omega | skip
      refine spec_seq ?_
      obtain ⟨c₁, k₁, e₁, hk₁, q96, q, qm, qr, qrm, qo⟩ := iEdgeF_exec (P := P) _ ‹_›
        (by ram_simp) (by ram_simp) (by omega_nf)
        (by omega_nf)
      refine ⟨_, _, e₁, ?_⟩
      have w₁ := e₁.wb_right
      exec_block
      refine ⟨by omega, ⟨?_, ?_, ?_⟩, fun r hr => ?_, by rw [qm], by rw [qr], by rw [qrm],
        by rw [qo]⟩
      · ram_simp
      · ram_simp
      · config_simp; rw [q _ (by omega) (by omega)]; config_simp; omega
      · unfold BorgR at hr
        simp only [Config.nreg_mk, upd]
        grind [upd]

/-! ## Conditional assignments -/

/-- **A conditional assignment**: both branches assign the register `r`. -/
theorem exec_ite_upd {a b r : ℕ} {s₁ s₂ : Stmt} {v₁ v₂ K : ℕ} (c : Config)
    (h₁ : c.nreg a < c.nreg b → ∃ k, Exec P W s₁ c { c with nreg := upd c.nreg r v₁ } k ∧ k ≤ K)
    (h₂ : ¬ c.nreg a < c.nreg b → ∃ k, Exec P W s₂ c { c with nreg := upd c.nreg r v₂ } k ∧ k ≤ K) :
    ∃ k, Exec P W (.ifLtN a b s₁ s₂) c
      { c with nreg := upd c.nreg r (if c.nreg a < c.nreg b then v₁ else v₂) } k ∧ k ≤ K + 2 := by
  by_cases h : c.nreg a < c.nreg b
  · obtain ⟨k, e, hk⟩ := h₁ h
    exact ⟨k + 1, by rw [ite_eq_left h]; exact .ifLtN_true h e, by omega⟩
  · obtain ⟨k, e, hk⟩ := h₂ h
    exact ⟨k + 2, by rw [ite_eq_right h]; exact .ifLtN_false h e, by omega⟩


end

section
variable {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
include hw
theorem exec_skip_upd (r : ℕ) :
    Exec P W .skip c { c with nreg := upd c.nreg r (c.nreg r) } 0 := by
  rw [upd_eq_self]; exact .skip hw

theorem exec_constN_upd (r v : ℕ)
    (hv : v ≤ W) : Exec P W (block [.constN r v]) c { c with nreg := upd c.nreg r v } 1 :=
  Exec.block_cons (Exec.constN hw r v hv) (Exec.block_nil (Exec.constN (P := P) hw r v hv).wb_right)

theorem exec_copyN_upd (r a : ℕ) :
    Exec P W (block [.copyN r a]) c { c with nreg := upd c.nreg r (c.nreg a) } 1 :=
  Exec.block_cons (Exec.copyN hw r a) (Exec.block_nil (Exec.copyN (P := P) hw r a).wb_right)

theorem exec_subN_upd (r a b : ℕ) :
    Exec P W (block [.subN r a b]) c { c with nreg := upd c.nreg r (c.nreg a - c.nreg b) } 1 :=
  Exec.block_cons (Exec.subN hw r a b) (Exec.block_nil (Exec.subN (P := P) hw r a b).wb_right)

theorem exec_addN_upd (r a b : ℕ)
    (hv : c.nreg a + c.nreg b ≤ W) :
    Exec P W (block [.addN r a b]) c { c with nreg := upd c.nreg r (c.nreg a + c.nreg b) } 1 :=
  Exec.block_cons (Exec.addN hw r a b hv) (Exec.block_nil (Exec.addN (P := P) hw r a b hv).wb_right)


end

end

end IOrc

end Chazelle.Core
