module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SpecMerge

/-!
# WP-E, part 3: the oracle costs are positive

The cost bound of `RestoreSpec` is a product `… · F γ · G γ · …` of the oracle costs.  A
procedure has to run at least one instruction, so the bound is only usable once `1 ≤ F γ` and
`1 ≤ G γ` are known.  Both follow from the oracle interfaces themselves, as soon as their
preconditions can be met:

* `exec_zero`: an execution of cost `0` changes nothing;
* `cutter_cost_pos`: the arc-cutter returns at least one piece and at most `G γ`, so
  `1 ≤ G γ`;
* `shooter_cost_pos`: if `F γ = 0`, the shooter would run in `0` steps, so its hit flag would be
  the one it was given; given `1` it must report a first hit, given `0` it must report no hit, on
  the same ray — a contradiction.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Machine (Stmt Exec)

/-- **An execution of cost `0` changes nothing.** -/
theorem exec_zero {P : Polygon} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hk : k = 0) : c' = c := by
  induction h with
  | skip _ => rfl
  | instr _ _ _ _ => omega
  | seq _ _ ih₁ ih₂ =>
    simp_all
  | ifLtN_true _ _ _ => omega
  | ifLtN_false _ _ _ => omega
  | ifLtR_true _ _ _ => omega
  | ifLtR_false _ _ _ => omega
  | whileLtN_false _ _ => omega
  | whileLtN_true _ _ _ _ _ => omega
  | whileLtR_false _ _ => omega
  | whileLtR_true _ _ _ _ _ => omega

/-- **The arc-cutter costs at least one step**: from any configuration meeting its
precondition (with room), `1 ≤ G γ`. -/
theorem cutter_cost_pos {cu : Stmt} {B : Finset ℕ} {G H : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (h : CutterOK cu B G H X Ok) {P : Polygon} {W : ℕ}
    {c : Config} (hw : WordsBounded W c)
    (hpre : GoodEnv P ∧ hostWords P.n ≤ W ∧ X.holds P c.nmem (rd c bCut 13) (c.nreg ALLOC) ∧
      rd c bCut 9 ≤ X.cap P c.nmem (rd c bCut 13) ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bCut 0) ∧
      ∃ M, ModelDescAt c.nmem (rd c bCut 0) (Qof P) M ∧ Ok P M ∧
        ProperPos M (Qof P) P.n ⟨rd c bCut 1, rd c bCut 2⟩ ∧
        ProperPos M (Qof P) P.n ⟨rd c bCut 3, rd c bCut 4⟩ ∧
        rd c bCut 1 < M.W.n ∧ rd c bCut 3 < M.W.n ∧
        (rd c bCut 2 = 0 ∨ M.InnerPt (M.pos (Qof P) ⟨rd c bCut 1, rd c bCut 2⟩)) ∧
        (rd c bCut 4 = 0 ∨ M.InnerPt (M.pos (Qof P) ⟨rd c bCut 3, rd c bCut 4⟩)) ∧
        M.arcWt (M.key (Qof P) ⟨rd c bCut 1, rd c bCut 2⟩)
          (M.key (Qof P) ⟨rd c bCut 3, rd c bCut 4⟩) ≤ rd c bCut 9)
    (hroom : c.nreg ALLOC + G (rd c bCut 9) ≤ W) : 1 ≤ G (rd c bCut 9) := by
  obtain ⟨c', k, -, -, hpost, -⟩ := h P W c hw hpre hroom
  obtain ⟨M, hM, -⟩ := hpre.2.2.2.2.2
  obtain ⟨-, -, hq, hq1, -⟩ := hpost M hM
  omega

/-- The configuration `c` with the hit-flag register of the shooter set to `v`. -/
def withFlag (c : Config) (v : ℕ) : Config :=
  { c with nreg := upd c.nreg (bandReg bShoot 10) v }

section
variable (c : Config) (v : ℕ)
theorem withFlag_rd {i : ℕ} (hi : i ≠ 10) (_hi' : i < 10000) :
    rd (withFlag c v) bShoot i = rd c bShoot i := by
  unfold rd withFlag bandReg
  simp_all

theorem withFlag_flag : rd (withFlag c v) bShoot 10 = v := by
  aesop

theorem withFlag_alloc : (withFlag c v).nreg ALLOC = c.nreg ALLOC := by
  aesop

theorem withFlag_originIn (o : Origin) :
    OriginIn (withFlag c v) (bandReg bShoot 5) o ↔ OriginIn c (bandReg bShoot 5) o := by
  simp_all [withFlag, bandReg, bShoot, Machine.upd_other, add_zero, OriginIn, SymPtIn] 


end

theorem withFlag_wb {W : ℕ} {c : Config} (hw : WordsBounded W c) {v : ℕ} (hv : v ≤ W) :
    WordsBounded W (withFlag c v) := by
  obtain ⟨h1, h2⟩ := hw
  refine ⟨fun r => ?_, h2⟩
  unfold withFlag
  grind [Machine.upd_apply]

/-- **The ray-shooter costs at least one step**: from any configuration meeting its
precondition (with room), `1 ≤ F γ`. -/
theorem shooter_cost_pos {sh : Stmt} {B : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (h : ShooterOK sh B F X Ok) {P : Polygon} {W : ℕ}
    {c : Config} (hw : WordsBounded W c)
    (hpre : GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c.nmem (rd c bShoot 13) (c.nreg ALLOC) ∧
      rd c bShoot 9 ≤ X.cap P c.nmem (rd c bShoot 13) ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bShoot 0) ∧
      (c.nmem (rd c bShoot 0) = 0 → ∀ H C, ChainDescAt c.nmem (rd c bShoot 0 + 1) (Qof P) H C →
        HostRegular (Qof P).n H) ∧
      ∃ M, ModelDescAt c.nmem (rd c bShoot 0) (Qof P) M ∧ Ok P M ∧
        ProperPos M (Qof P) P.n ⟨rd c bShoot 1, rd c bShoot 2⟩ ∧
        ProperPos M (Qof P) P.n ⟨rd c bShoot 3, rd c bShoot 4⟩ ∧
        rd c bShoot 1 < M.W.n ∧ rd c bShoot 3 < M.W.n ∧
        (rd c bShoot 2 = 0 ∨ M.InnerPt (M.pos (Qof P) ⟨rd c bShoot 1, rd c bShoot 2⟩)) ∧
        (rd c bShoot 4 = 0 ∨ M.InnerPt (M.pos (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩)) ∧
        M.arcWt (M.key (Qof P) ⟨rd c bShoot 1, rd c bShoot 2⟩)
          (M.key (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩) ≤ rd c bShoot 9 ∧
        ∃ o : Origin, o.Lt P.n M ∧ OriginIn c (bandReg bShoot 5) o ∧
          ((∃ p, o = .walk ⟨p, 0⟩) ∨ (M.InnerPt (o.eval M (Qof P)) ∧
            ∀ x, o = .walk x → ProperPos M (Qof P) P.n x)) ∧
          o.eval M (Qof P) ∉ M.arcSet (M.key (Qof P) ⟨rd c bShoot 1, rd c bShoot 2⟩)
            (M.key (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩))
    (hroom : c.nreg ALLOC + F (rd c bShoot 9) ≤ W) : 1 ≤ F (rd c bShoot 9) := by
  by_contra hF
  have hF0 : F (rd c bShoot 9) = 0 := by omega
  obtain ⟨hG, hWh, hX, hcap, hwf, hreg, M, hM, hOk, hp1, hp2, he1, he2, hi1, hi2, hwt, o, hoLt,
    hoIn, hoK, hoA⟩ := hpre
  have hW1 : 1 ≤ W := le_trans (by omega_nf) hWh
  have r : ∀ v i, i ≠ 10 → i < 10000 → rd (withFlag c v) bShoot i = rd c bShoot i :=
    fun v i h1 h2 => withFlag_rd c v h1 h2
  -- run the shooter from `c` with flag `v`
  have run : ∀ v, v ≤ 1 → ∃ c', c' = withFlag c v ∧
      (∀ M' (o' : Origin), ModelDescAt c.nmem (rd c bShoot 0) (Qof P) M' →
        OriginIn c (bandReg bShoot 5) o' →
        (rd c' bShoot 10 = 1 → ∃ t, FirstHit (M'.arcSet (M'.key (Qof P) ⟨rd c bShoot 1,
            rd c bShoot 2⟩) (M'.key (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩))
          (o'.eval M' (Qof P)) (dirOf (rd c bShoot 8)) t) ∧
        (rd c' bShoot 10 ≠ 1 → NoHit (M'.arcSet (M'.key (Qof P) ⟨rd c bShoot 1,
            rd c bShoot 2⟩) (M'.key (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩))
          (o'.eval M' (Qof P)) (dirOf (rd c bShoot 8)))) := by
    intro v hv
    have hwv := withFlag_wb hw (le_trans hv hW1)
    have pre' : GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P (withFlag c v).nmem (rd (withFlag c v) bShoot 13)
          ((withFlag c v).nreg ALLOC) ∧
        rd (withFlag c v) bShoot 9 ≤ X.cap P (withFlag c v).nmem (rd (withFlag c v) bShoot 13) ∧
        ModelDescWF P ((withFlag c v).nreg ALLOC) (withFlag c v).nmem
          (rd (withFlag c v) bShoot 0) ∧
        ((withFlag c v).nmem (rd (withFlag c v) bShoot 0) = 0 → ∀ H C,
          ChainDescAt (withFlag c v).nmem (rd (withFlag c v) bShoot 0 + 1) (Qof P) H C →
          HostRegular (Qof P).n H) ∧
        ∃ M, ModelDescAt (withFlag c v).nmem (rd (withFlag c v) bShoot 0) (Qof P) M ∧ Ok P M ∧
          ProperPos M (Qof P) P.n ⟨rd (withFlag c v) bShoot 1, rd (withFlag c v) bShoot 2⟩ ∧
          ProperPos M (Qof P) P.n ⟨rd (withFlag c v) bShoot 3, rd (withFlag c v) bShoot 4⟩ ∧
          rd (withFlag c v) bShoot 1 < M.W.n ∧ rd (withFlag c v) bShoot 3 < M.W.n ∧
          (rd (withFlag c v) bShoot 2 = 0 ∨
            M.InnerPt (M.pos (Qof P) ⟨rd (withFlag c v) bShoot 1, rd (withFlag c v) bShoot 2⟩)) ∧
          (rd (withFlag c v) bShoot 4 = 0 ∨
            M.InnerPt (M.pos (Qof P) ⟨rd (withFlag c v) bShoot 3, rd (withFlag c v) bShoot 4⟩)) ∧
          M.arcWt (M.key (Qof P) ⟨rd (withFlag c v) bShoot 1, rd (withFlag c v) bShoot 2⟩)
            (M.key (Qof P) ⟨rd (withFlag c v) bShoot 3, rd (withFlag c v) bShoot 4⟩) ≤
              rd (withFlag c v) bShoot 9 ∧
          ∃ o : Origin, o.Lt P.n M ∧ OriginIn (withFlag c v) (bandReg bShoot 5) o ∧
            ((∃ p, o = .walk ⟨p, 0⟩) ∨ (M.InnerPt (o.eval M (Qof P)) ∧
              ∀ x, o = .walk x → ProperPos M (Qof P) P.n x)) ∧
            o.eval M (Qof P) ∉ M.arcSet (M.key (Qof P) ⟨rd (withFlag c v) bShoot 1,
              rd (withFlag c v) bShoot 2⟩)
              (M.key (Qof P) ⟨rd (withFlag c v) bShoot 3, rd (withFlag c v) bShoot 4⟩) := by
      simp only [r v 0 (by decide) (by decide), r v 1 (by decide) (by decide),
        r v 2 (by decide) (by decide), r v 3 (by decide) (by decide),
        r v 4 (by decide) (by decide), r v 9 (by decide) (by decide),
        r v 13 (by decide) (by decide), withFlag_alloc, withFlag_originIn]
      exact ⟨hG, hWh, hX, hcap, hwf, hreg, M, hM, hOk, hp1, hp2, he1, he2, hi1, hi2, hwt, o, hoLt,
        hoIn, hoK, hoA⟩
    obtain ⟨c', k, ex, hk, hpost, -⟩ := h P W (withFlag c v) hwv pre'
      (by grind [withFlag_alloc])
    beta_reduce at hk
    rw [r v 9 (by decide) (by decide), hF0] at hk
    have hc' := exec_zero ex (by omega)
    refine ⟨c', hc', fun M' o' hM' ho' => ?_⟩
    have hM'' : ModelDescAt (withFlag c v).nmem (rd (withFlag c v) bShoot 0) (Qof P) M' := by
      rw [r v 0 (by decide) (by decide)]; exact hM'
    have ho'' : OriginIn (withFlag c v) (bandReg bShoot 5) o' := (withFlag_originIn c v o').2 ho'
    have := hpost M' o' hM'' ho''
    grind
  obtain ⟨c₁, rfl, h₁⟩ := run 1 le_rfl
  obtain ⟨c₀, rfl, h₀⟩ := run 0 (by omega)
  obtain ⟨t, ht0, htA, -⟩ := (h₁ M o hM hoIn).1 (withFlag_flag c 1)
  exact (h₀ M o hM hoIn).2 (by grind [withFlag_flag]) t ht0 htA

end

end Restore

end Chazelle.Core
