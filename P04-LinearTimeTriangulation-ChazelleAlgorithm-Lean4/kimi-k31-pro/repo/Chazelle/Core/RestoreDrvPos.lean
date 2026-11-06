module

public import Chazelle.Core.RestoreDrvRound
public import Chazelle.Core.OutputWalk
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-E, part 12: the oracle costs are positive in the context of `RestoreSpec`

`oracle_pos`: from a configuration satisfying the precondition of `RestoreSpec`, the shooter and
the cutter can be run (virtually) on the subarc of the first walk edge, with the walk vertex `2`
as origin (not on that edge), so `1 ≤ F γ` and `1 ≤ G γ` (`shooter_cost_pos`,
`cutter_cost_pos`).  Also `one_le_gamma`: a semigranularity bound of a good model is positive.
-/

namespace Chazelle.Core

namespace Restore

open Machine Machine.Stmt Programs
open Chazelle.Chain (sideInArc sidePt)
open Chazelle.Geometry (lerp)

@[expose] public section

variable {M : Model}

/-- **A good model has a counted walk edge.** -/
theorem exists_counted (hG : GoodModel M) : ∃ p, p < M.W.n ∧ M.counted p := by
  rcases hG with ⟨C, -, rfl⟩ | ⟨Q, hQ, rfl⟩
  · refine ⟨6, ?_, ?_⟩
    · show 6 < (C.sideWalk C.sideBeta).n
      rw [C.sideWalk_n]; have := C.one_le; omega
    · show 6 ≤ 6 ∧ 6 < 2 * C.m + 6
      have := C.one_le; omega
  · refine ⟨0, ?_, trivial⟩
    show 0 < (interiorWalk Q).n
    rw [OutWalk.walk_n]; have := Jordan.simple_three_le hQ; omega

/-- **A semigranularity bound of a chord family of a good model is positive.** -/
theorem one_le_gamma (hG : GoodModel M) {Q : Polygon} {S : Set (Set Point)} {γ : ℕ}
    (hS : M.ChordFamily Q S) (h : M.Semigranular S γ) : 1 ≤ γ := by
  have hM := walkAx_of_goodModel hG
  obtain ⟨p₀, hp₀, hc₀⟩ := exists_counted hG
  by_contra hγ
  have hγ0 : γ = 0 := by omega
  subst hγ0
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hD : M.D ∈ M.regions ∅ := by
      show M.D ∈ Chazelle.Chain.regionsIn M.D ∅
      rwr [Chazelle.Chain.regionsIn_empty hM.preconn hM.nonempty]
    have h1 := h M.D hD
    rw [Gran.weight_empty hM hD] at h1
    have : 1 ≤ M.size := by
      unfold Model.size
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [Set.ncard_eq_zero (hs := (Set.finite_lt_nat M.W.n).subset fun p hp => hp.1)] at h0
      exact (Set.eq_empty_iff_forall_notMem.1 h0) p₀ ⟨hp₀, hc₀⟩
    omega
  · exact hM.not_semigranular_zero hS.2.1 hS.1 hne hp₀ hc₀ h

theorem key00 (Q : Polygon) : M.key Q ⟨0, 0⟩ = 0 := by simp [Model.key, Model.param]

theorem key10 (Q : Polygon) : M.key Q ⟨1, 0⟩ = 1 := by simp [Model.key, Model.param]

/-- The subarc from key `0` to key `1` meets at most one counted edge. -/
theorem arcWt01 (Q : Polygon) : M.arcWt (M.key Q ⟨0, 0⟩) (M.key Q ⟨1, 0⟩) ≤ 1 := by
  rw [key00, key10]
  unfold Model.arcWt
  calc _ ≤ ({0} : Set ℕ).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.finite_singleton 0)
        rintro p ⟨-, -, t, ht0, ht1, hin⟩
        simp [sideInArc, zero_lt_one, ite_true] at hin
        have : (p : ℝ) < 1 := by linarith [hin.2]
        have : p < 1 := by exact_mod_cast this
        sio only [Set.mem_singleton_iff]
    _ = 1 := Set.ncard_singleton 0

theorem properPos0 (Q : Polygon) (n : ℕ) (e : ℕ) : ProperPos M Q n ⟨e, 0⟩ :=
  ⟨by simp [Model.param], by simp [Model.param], by simp⟩

/-- The points of the subarc from key `0` to key `1` lie on the segment of the first walk edge. -/
theorem arcSet01_sub {x : Point} (hn : 2 ≤ M.W.n)
    (hx : x ∈ M.arcSet 0 1) : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = lerp (M.W.vtx 0) (M.W.vtx 1) s := by
  obtain ⟨p, t, hp, ht0, ht1, hk, rfl⟩ := hx
  have hwb : ∀ q, q + 1 < M.W.n → M.wb q = M.W.vtx (q + 1) := fun q hq => by
    show M.W.vtx ((q + 1) % M.W.n) = _; rw [Nat.mod_eq_of_lt hq]
  have hkey : (p : ℝ) + t ≤ 1 := by
    rcases hk with h | h | h
    · simp [sideInArc, zero_lt_one, ite_true] at h; linarith [h.2]
    · linarith
    · linarith
  have hp1 : p ≤ 1 := by
    have : (p : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  rcases Nat.lt_or_ge p 1 with h0 | h1
  · have : p = 0 := by omega
    subst this
    refine ⟨t, ht0, ht1, ?_⟩
    rw [show M.wa 0 = M.W.vtx 0 from rfl, hwb 0 (by omega)]
  · have : p = 1 := by omega
    subst this
    have ht : t = 0 := by push_cast at hkey; linarith
    subst ht
    refine ⟨1, by norm_num, le_rfl, ?_⟩
    rwr [Geometry.lerp_zero, Geometry.lerp_one]

/-- **The walk vertex `2` is not on the first walk edge** of a good model. -/
theorem vtx2_not_mem (hG : GoodModel M) (Q : Polygon) :
    M.pos Q ⟨2, 0⟩ ∉ M.arcSet (M.key Q ⟨0, 0⟩) (M.key Q ⟨1, 0⟩) := by
  rw [key00, key10]
  have hpos : M.pos Q ⟨2, 0⟩ = M.W.vtx 2 := by
    simp [Model.pos, Model.param, Geometry.lerp, Model.wa]
  rw [hpos]
  intro hx
  rcases hG with ⟨C, -, rfl⟩ | ⟨Q', hQ', rfl⟩
  · have hn : 2 ≤ (chainModel C).W.n := by
      show 2 ≤ (C.sideWalk C.sideBeta).n; rwo [C.sideWalk_n]
    obtain ⟨s, hs0, hs1, he⟩ := arcSet01_sub hn hx
    have e2 : (chainModel C).W.vtx 2 = (-C.radius, -C.radius) := rfl
    have e0 : (chainModel C).W.vtx 0 = C.slitTop := rfl
    have e1 : (chainModel C).W.vtx 1 = (-C.radius, C.radius) := rfl
    rw [e2, e0, e1] at he
    have hy := congrArg Prod.snd he
    simp [Geometry.lerp_snd, Chain.slitTop, sub_self, mul_zero, add_zero] at hy
    have := C.radius_pos
    linarith
  · have hsimp := (FactsInterior.interiorWalk_spec hQ').1
    have hn3 : 3 ≤ (interiorWalk Q').n := Jordan.simple_three_le hsimp
    obtain ⟨s, hs0, hs1, he⟩ := arcSet01_sub (by show 2 ≤ (interiorWalk Q').n; omega) hx
    set W := interiorWalk Q' with hWd
    have hv : ∀ q, q < W.n → sidePt W q 0 = W.vtx q := fun q _ => by
      unfold sidePt; rw [Geometry.lerp_zero]
    have hs01 : ∀ s : ℝ, lerp (W.vtx 0) (W.vtx 1) s = sidePt W 0 s := fun s => by
      unfold sidePt; rw [Nat.mod_eq_of_lt (by omega)]
    rcases hs1.lt_or_eq with hs1 | rfl
    · have := FactsInterior.pos_unique hsimp (p := 2) (p' := 0) (t := 0) (t' := s)
        (by omega) (by omega) le_rfl (by norm_num) hs0 hs1
        (by rwx [hv 2 (by omega), ← hs01])
      omega
    · have := FactsInterior.pos_unique hsimp (p := 2) (p' := 1) (t := 0) (t' := 0)
        (by omega) (by omega) le_rfl (by norm_num) le_rfl (by norm_num)
        (by
          change W.vtx 2 = lerp (W.vtx 0) (W.vtx 1) 1 at he
          rw [hv 2 (by omega), hv 1 (by omega), he, Geometry.lerp_one])
      omega

/-- The configuration `c` with the inputs of an oracle query in band `b`: model `MD`, subarc
`⟨0,0⟩ … ⟨1,0⟩`, origin the walk vertex `2`, weight bound `γ`, context `g`. -/
def setQ (c : Config) (b MD γ g : ℕ) : Config :=
  { c with nreg := fun r =>
      if r = bandReg b 0 then MD else if r = bandReg b 3 then 1 else
      if r = bandReg b 5 then 2 else if r = bandReg b 6 then 2 else
      if r = bandReg b 9 then γ else if r = bandReg b 13 then g else
      if bandReg b 0 ≤ r ∧ r ≤ bandReg b 13 then 0 else c.nreg r }

theorem setQ_wb {W : ℕ} {c : Config} (hw : WordsBounded W c) {b MD γ g : ℕ} (h2 : 2 ≤ W)
    (hMD : MD ≤ W) (hγ : γ ≤ W) (hg : g ≤ W) : WordsBounded W (setQ c b MD γ g) := by
  refine ⟨fun r => ?_, hw.2⟩
  simp [setQ]
  split_ifs <;> first | assumption | omega | exact hw.1 r

theorem setQ_alloc (c : Config) {b MD γ g : ℕ} (hb : 1 ≤ b) :
    (setQ c b MD γ g).nreg ALLOC = c.nreg ALLOC := by
  unfold setQ
  simp
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;>
    first | rfl | (exfalso; sio only [bandReg, ALLOC] at *)

/-- **The oracle costs are positive** in the context of `RestoreSpec`. -/
theorem oracle_pos {sh cu : Stmt} {Bs Bc : Finset ℕ} {F G H : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hcu : CutterOK cu Bc G H X Ok)
    {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) {MD γ g : ℕ} (hX : X.holds P c.nmem g (c.nreg ALLOC))
    (hcap : γ ≤ X.cap P c.nmem g) (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem MD)
    (hreg : c.nmem MD = 0 → ∀ H C, ChainDescAt c.nmem (MD + 1) (Qof P) H C →
      HostRegular (Qof P).n H)
    (hMD : ModelDescAt c.nmem MD (Qof P) M) (hGM : GoodModel M) (hOk : Ok P M) (hγ : 1 ≤ γ)
    (hMDW : MD ≤ W) (hγW : γ ≤ W) (hgW : g ≤ W) : 1 ≤ F γ ∧ 1 ≤ G γ := by
  have h2 : 2 ≤ W := le_trans (by ufo hostWords) hWh
  have hn2 : 2 < M.W.n := by
    rcases hGM with ⟨C, -, rfl⟩ | ⟨Q, hQ, rfl⟩
    · show 2 < (C.sideWalk C.sideBeta).n; rwo [C.sideWalk_n]
    · show 2 < (interiorWalk Q).n
      rw [OutWalk.walk_n]; have := Jordan.simple_three_le hQ; omega
  constructor
  · set cS := setQ c bShoot MD γ g with hcS
    have r0 : rd cS bShoot 0 = MD := by simp [hcS, rd, setQ, bandReg, bShoot]
    have r1 : rd cS bShoot 1 = 0 := by simp [hcS, rd, setQ, bandReg, bShoot]
    have r2 : rd cS bShoot 2 = 0 := by simp [hcS, rd, setQ, bandReg, bShoot]
    have r3 : rd cS bShoot 3 = 1 := by simp [hcS, rd, setQ, bandReg, bShoot]
    have r4 : rd cS bShoot 4 = 0 := by simp [hcS, rd, setQ, bandReg, bShoot]
    have r9 : rd cS bShoot 9 = γ := by simp [hcS, rd, setQ, bandReg, bShoot]
    have r13 : rd cS bShoot 13 = g := by simp [hcS, rd, setQ, bandReg, bShoot]
    have hwS : WordsBounded (W + F γ) cS :=
      Machine.WordsBounded.mono (setQ_wb hw h2 hMDW hγW hgW) (by omega)
    have hA : cS.nreg ALLOC = c.nreg ALLOC := setQ_alloc c (by decide)
    have hO : OriginIn cS (bandReg bShoot 5) (.walk ⟨2, 0⟩) :=
      ⟨by simp [hcS, setQ, bandReg, bShoot], by simp [hcS, setQ, bandReg, bShoot],
       by simp [hcS, setQ, bandReg, bShoot]⟩
    have hWA  := hw.1 ALLOC
    have := shooter_cost_pos hsh (W := W + F γ) hwS ⟨hG, by omega,
      by rwx [r13, hA], by rwx [r9, r13],
      by rwx [r0, hA], by rwx [r0], M, by rwx [r0], hOk,
      by rw [r1, r2]; exact properPos0 _ _ _, by rw [r3, r4]; exact properPos0 _ _ _,
      by rwo [r1], by rwo [r3], Or.inl r2, Or.inl r4,
      by rw [r1, r2, r3, r4, r9]; exact (arcWt01 _).trans hγ,
      .walk ⟨2, 0⟩, ⟨hn2, Nat.zero_le _⟩, hO, Or.inl ⟨2, rfl⟩,
      by rw [r1, r2, r3, r4]; exact vtx2_not_mem hGM _⟩
      (by rwo [hA, r9])
    rw [r9] at this
    exact this
  · set cC := setQ c bCut MD γ g with hcC
    have r0 : rd cC bCut 0 = MD := by simp [hcC, rd, setQ, bandReg, bCut]
    have r1 : rd cC bCut 1 = 0 := by simp [hcC, rd, setQ, bandReg, bCut]
    have r2 : rd cC bCut 2 = 0 := by simp [hcC, rd, setQ, bandReg, bCut]
    have r3 : rd cC bCut 3 = 1 := by simp [hcC, rd, setQ, bandReg, bCut]
    have r4 : rd cC bCut 4 = 0 := by simp [hcC, rd, setQ, bandReg, bCut]
    have r9 : rd cC bCut 9 = γ := by simp [hcC, rd, setQ, bandReg, bCut]
    have r13 : rd cC bCut 13 = g := by simp [hcC, rd, setQ, bandReg, bCut]
    have hwC : WordsBounded (W + G γ) cC :=
      Machine.WordsBounded.mono (setQ_wb hw h2 hMDW hγW hgW) (by omega)
    have hA : cC.nreg ALLOC = c.nreg ALLOC := setQ_alloc c (by decide)
    have hWA  := hw.1 ALLOC
    have := cutter_cost_pos hcu (W := W + G γ) hwC ⟨hG, by omega,
      by rwx [r13, hA], by rwx [r9, r13],
      by rwx [r0, hA], M, by rwx [r0], hOk,
      by rw [r1, r2]; exact properPos0 _ _ _, by rw [r3, r4]; exact properPos0 _ _ _,
      by rwo [r1], by rwo [r3], Or.inl r2, Or.inl r4,
      by rw [r1, r2, r3, r4, r9]; exact (arcWt01 _).trans hγ⟩
      (by rwo [hA, r9])
    rw [r9] at this
    exact this

end

end Restore

end Chazelle.Core
