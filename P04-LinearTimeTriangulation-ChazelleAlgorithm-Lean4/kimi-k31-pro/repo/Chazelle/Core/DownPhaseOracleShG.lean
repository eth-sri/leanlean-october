module

public import Chazelle.Core.DownPhaseOracleShF
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxRecDepth 20000

/-!
# WP-M (E7-B, RAM part 14): the query of the interior shooter

`queryI sh = normI ; branchI sh ; outI`: the normalized query (`normI`), one sub-query
(`L ≤ n - 1`, `plan_one`) or two (`L ≥ n`, `plan_two`) of the chain shooter `sh` (`sqS`), and the
answer (`outI`).  `queryI_exec`: the answer is the first hit of the ray on the subarc, as
`ShooterOK` asks for the interior model.
-/


namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)

@[expose] public section

/-- One or two sub-queries. -/
def branchI (sh : Stmt) : Stmt :=
  .ifLtN 170032 170010 (.seq setOne (sqS sh))
    (.seq setTwoA (.seq (sqS sh) (.seq setTwoB (sqS sh))))

/-- **The query of the interior shooter.** -/
def queryI (sh : Stmt) : Stmt := .seq normI (.seq (branchI sh) outI)

/-- The logarithm of a stretch within a weight bound. -/
theorem log_le_clog_succ {L γ : ℕ} (h1 : 1 ≤ L) (h2 : L ≤ γ) :
    Nat.log 2 (2 * L) ≤ Nat.clog 2 γ + 1 := by
  have e : Nat.log 2 (2 * L) = Nat.log 2 L + 1 := by
    rw [mul_comm]; exact Nat.log_mul_base (by norm_num) (by omega)
  rw [e]
  have := Nat.log_mono_right (b := 2) h2
  have := Nat.log_le_clog 2 γ
  omega

theorem room_one {A lg Fg cl W : ℕ} (h : A + (4 * Fg + 3000 * (cl + 1) + 19000) ≤ W)
    (hl : lg ≤ cl + 1) : A + 2 * Fg + 1204 * lg + 4500 ≤ W := by omega

theorem room_two {A k lg lg₁ Fg cl W : ℕ} (h : A + (4 * Fg + 3000 * (cl + 1) + 19000) ≤ W)
    (hk : k ≤ 2 * Fg + 1204 * lg₁ + 4500) (hl₁ : lg₁ ≤ cl + 1) (hl : lg ≤ cl + 1) :
    A + k + 2 * Fg + 1204 * lg + 4500 ≤ W := by omega

theorem cost_one {k₂ k₃ lg Fg cl : ℕ} (h2 : k₂ = 5) (h3 : k₃ ≤ 2 * Fg + 1204 * lg + 4500)
    (hl : lg ≤ cl + 1) : k₂ + k₃ + 1 ≤ 4 * Fg + 3000 * (cl + 1) + 18000 := by omega

theorem cost_two {k₂ k₃ k₄ k₅ lg lg₁ Fg cl : ℕ} (h2 : k₂ = 5)
    (h3 : k₃ ≤ 2 * Fg + 1204 * lg₁ + 4500) (h4 : k₄ ≤ 8) (h5 : k₅ ≤ 2 * Fg + 1204 * lg + 4500)
    (hl₁ : lg₁ ≤ cl + 1) (hl : lg ≤ cl + 1) :
    k₂ + (k₃ + (k₄ + k₅)) + 2 ≤ 4 * Fg + 3000 * (cl + 1) + 18000 := by omega

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- The frame of the parameter blocks. -/
theorem bset_io {r : ℕ} (h : Bset r = true) : bandOf r ∈ ioBands ∧ r ≠ ALLOC :=
  io_of_band (Or.inl (by sio only [Bset, decide_eq_true_eq] at h))

/-- **The query of the interior shooter.** -/
theorem queryI_exec {sh : Stmt} {F : ℕ → ℕ}
    (hsh : ShooterOK sh oracleBands F (gradeCtx O) OkModel) (c : Config) (hw : WordsBounded W c)
    (hS : SEnv P W O s c) (h70 : c.nreg 170070 = 0) (q : QFacts (Qof P) s.e₁ s.h₁ s.e₂ s.h₂)
    (hwt : (interiorModel (Qof P)).arcWt ((interiorModel (Qof P)).key (Qof P) ⟨s.e₁, s.h₁⟩)
      ((interiorModel (Qof P)).key (Qof P) ⟨s.e₂, s.h₂⟩) ≤ s.γ)
    (ho1 : |(s.o.eval (Qof P)).1| ≤ Jordan.coordBound (Qof P))
    (ho2 : |(s.o.eval (Qof P)).2| ≤ Jordan.coordBound (Qof P)) (hol : s.o.Lt P.n)
    (hoA : s.o.eval (Qof P) ∉ (interiorModel (Qof P)).arcSet
      ((interiorModel (Qof P)).key (Qof P) ⟨s.e₁, s.h₁⟩)
      ((interiorModel (Qof P)).key (Qof P) ⟨s.e₂, s.h₂⟩))
    (hroom : c.nreg ALLOC + (4 * F s.γ + 3000 * (Nat.clog 2 s.γ + 1) + 19000) ≤ W) :
    ∃ c' k, Exec P W (queryI sh) c c' k ∧
      k ≤ 4 * F s.γ + 3000 * (Nat.clog 2 s.γ + 1) + 19000 ∧
      (c'.nreg 140010 = 1 → ∃ t, FirstHit ((interiorModel (Qof P)).arcSet
          ((interiorModel (Qof P)).key (Qof P) ⟨s.e₁, s.h₁⟩)
          ((interiorModel (Qof P)).key (Qof P) ⟨s.e₂, s.h₂⟩)) (s.o.eval (Qof P)) (dirOf s.dir) t ∧
        ProperPos (interiorModel (Qof P)) (Qof P) P.n ⟨c'.nreg 140011, c'.nreg 140012⟩ ∧
        c'.nreg 140011 < (interiorModel (Qof P)).W.n ∧
        (interiorModel (Qof P)).pos (Qof P) ⟨c'.nreg 140011, c'.nreg 140012⟩ =
          rayPt (s.o.eval (Qof P)) (dirOf s.dir) t) ∧
      (c'.nreg 140010 ≠ 1 → NoHit ((interiorModel (Qof P)).arcSet
          ((interiorModel (Qof P)).key (Qof P) ⟨s.e₁, s.h₁⟩)
          ((interiorModel (Qof P)).key (Qof P) ⟨s.e₂, s.h₂⟩)) (s.o.eval (Qof P)) (dirOf s.dir)) ∧
      Frame ioBands c c' k := by
  have hQ : (Qof P).n = P.n := qn'
  have hn := hS.n3
  have hW := hS.hW
  unfold hostWords at hW
  have he1 : s.e₁ < P.n := by rw [← hQ]; exact q.he₁
  have he2 : s.e₂ < P.n := by rw [← hQ]; exact q.he₂
  have hh1 : s.h₁ ≤ P.n := by rw [← hQ]; exact q.hs.2.2
  have hh2 : s.h₂ ≤ P.n := by rw [← hQ]; exact q.he.2.2
  -- the normalized query
  obtain ⟨c₁, k₁, e₁, hk₁, a30, a31, a32, F₁⟩ := normI_exec c hw hS he1 he2 hh1 hh2 q.hs.1
  have w₁ := e₁.wb_right
  have f₁ : ∀ r, Bnorm r = false → c₁.nreg r = c.nreg r := F₁.1
  have S₁ : SEnv P W O s c₁ := hS.keep (fun r h1 h2 => f₁ r (by
    sio only [Bnorm, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]))
    (fun a _ => by rw [F₁.2.2.1]) (by rw [f₁ _ (by decide)])
  have Fr₁ : Frame ioBands c c₁ k₁ := frameIO_of_frameB (B := Bnorm) (fun r hr => io_of_band (by
    sio only [Bnorm, Bk, Bool.or_eq_true, decide_eq_true_eq] at hr)) F₁ k₁
  have hB₁ : BestI P c₁ ∅ (s.o.eval (Qof P)) (dirOf s.dir) :=
    bestI_empty (by rwx [f₁ _ (by decide)])
  set A := (interiorModel (Qof P)).arcSet ((interiorModel (Qof P)).key (Qof P) ⟨s.e₁, s.h₁⟩)
    ((interiorModel (Qof P)).key (Qof P) ⟨s.e₂, s.h₂⟩) with hAd
  set z := s.o.eval (Qof P) with hzd
  set σ := dirOf s.dir with hσd
  have bandSet : ∀ {d d' : Config}, FrameB Bset d d' → ∀ r, (r < 170033 ∨ 170038 ≤ r) →
      d'.nreg r = d.nreg r := fun F r hr => F.1 r (by
        sio only [Bset, decide_eq_false_iff_not])
  have keepSet : ∀ {d d' : Config}, FrameB Bset d d' → SEnv P W O s d → SEnv P W O s d' :=
    fun F hS' => hS'.keep (fun r h1 h2 => bandSet F r (by omega)) (fun a _ => by rw [F.2.2.1])
      (by rw [bandSet F _ (by ufo ALLOC)])
  have bestSet : ∀ {d d' : Config} {S' : Set Point}, FrameB Bset d d' → BestI P d S' z σ →
      BestI P d' S' z σ := fun F hb => hb.keep (fun r h1 h2 => bandSet F r (by omega))
  -- the branch
  have hbr : ∃ c₂ k₂, Exec P W (branchI sh) c₁ c₂ k₂ ∧
      k₂ ≤ 4 * F s.γ + 3000 * (Nat.clog 2 s.γ + 1) + 18000 ∧ BestI P c₂ (∅ ∪ A) z σ ∧
      SEnv P W O s c₂ ∧ Frame ioBands c₁ c₂ k₂ := by
    obtain ⟨hpS, hxy, hmod, heen, hee, hL1, hwtL, hwtn⟩ := qplan q
    unfold branchI
    by_cases hL : spanL (eeOf (Qof P) s.e₁ s.h₁ s.e₂ (nh (Qof P) s.e₂ s.h₂))
        (nh (Qof P) s.e₂ s.h₂) + 1 ≤ (Qof P).n
    · -- one sub-query
      have hcond : c₁.nreg 170032 < c₁.nreg 170010 := by rwo [a32, S₁.r10, ← hQ]
      obtain ⟨hsub, hset, hwL⟩ := plan_one q hL
      obtain ⟨c₂, k₂, e₂, hk₂, b33, b34, b35, b36, b37, Fs⟩ := setOne_exec (P := P) c₁ w₁
      have S₂ := keepSet Fs S₁
      have hLγ : spanL (eeOf (Qof P) s.e₁ s.h₁ s.e₂ (nh (Qof P) s.e₂ s.h₂))
          (nh (Qof P) s.e₂ s.h₂) ≤ s.γ := hwL ▸ hwt
      have hlog := log_le_clog_succ hL1 hLγ
      have hA₂ : c₂.nreg ALLOC = c.nreg ALLOC := by
        rw [bandSet Fs _ (by ufo ALLOC), f₁ _ (by decide)]
      obtain ⟨c₃, k₃, e₃, hk₃, hB₃, S₃, F₃, g₃⟩ := sqS_exec hsh c₂ e₂.wb_right S₂
        (by rw [b33, S₁.r1]) (by rw [b34, S₁.r2]) (by rw [b35, a31]) (by rw [b36, a30]) (by rw [b37, a32])
        hsub hLγ ho1 ho2 hol (by rwx [← hset]) (bestSet Fs hB₁)
        (by rw [hA₂]; exact room_one hroom hlog)
      refine ⟨c₃, _, .ifLtN_true hcond (.seq e₂ e₃), cost_one hk₂ hk₃ hlog,
        by rwx [hAd, hset], S₃,
        ((frameIO_of_frameB (fun r h => bset_io h) Fs k₂).trans F₃).mono (by simp) (by omega)⟩
    · -- two sub-queries
      push Not at hL
      have hcond : ¬ c₁.nreg 170032 < c₁.nreg 170010 := by rwo [a32, S₁.r10, ← hQ]
      obtain ⟨hsubA, hsubB, hset, hwn⟩ := plan_two q (by omega)
      have hnγ : P.n ≤ s.γ := by rw [← hQ]; exact hwn ▸ hwt
      -- the first sub-query
      obtain ⟨c₂, k₂, e₂, hk₂, b33, b34, b35, b36, b37, Fs⟩ := setTwoA_exec (P := P) c₁ w₁ (by omega)
      have S₂ := keepSet Fs S₁
      have hA₂ : c₂.nreg ALLOC = c.nreg ALLOC := by
        rw [bandSet Fs _ (by ufo ALLOC), f₁ _ (by decide)]
      have hlogA := log_le_clog_succ (L := 2) (γ := s.γ) (by norm_num) (by omega)
      have hsA : (interiorModel (Qof P)).arcSet ((interiorModel (Qof P)).key (Qof P) ⟨s.e₁, s.h₁⟩)
          ((interiorModel (Qof P)).key (Qof P) ⟨s.e₂, s.h₂⟩) ⊇ oset (interiorWalk (Qof P)) s.e₁
          ((interiorModel (Qof P)).param (Qof P) ⟨s.e₁, s.h₁⟩)
          ((2 : ℕ) + (interiorModel (Qof P)).param (Qof P) ⟨(s.e₁ + 2) % (Qof P).n, 0⟩) := by
        rw [hset]; exact Set.subset_union_left
      obtain ⟨c₃, k₃, e₃, hk₃, hB₃, S₃, F₃, g₃⟩ := sqS_exec hsh c₂ e₂.wb_right S₂ (u := s.e₁)
        (L := 2) (sh₀ := s.h₁) (ee := 2) (eh := 0)
        (by rw [b33, S₁.r1]) (by rw [b34, S₁.r2]) b35 b36 b37
        hsubA (by omega) ho1 ho2 hol (fun h => hoA (hsA h)) (bestSet Fs hB₁)
        (by rw [hA₂]; exact room_one hroom hlogA)
      -- the second sub-query
      have c31 : c₃.nreg 170031 = eeOf (Qof P) s.e₁ s.h₁ s.e₂ (nh (Qof P) s.e₂ s.h₂) := by
        rwx [g₃ _ (by norm_num) (by norm_num) (by decide), bandSet Fs _ (by omega)]
      have c30 : c₃.nreg 170030 = nh (Qof P) s.e₂ s.h₂ := by
        rwx [g₃ _ (by norm_num) (by norm_num) (by decide), bandSet Fs _ (by omega)]
      have c32 : c₃.nreg 170032 = spanL (eeOf (Qof P) s.e₁ s.h₁ s.e₂ (nh (Qof P) s.e₂ s.h₂))
          (nh (Qof P) s.e₂ s.h₂) := by
        rwx [g₃ _ (by norm_num) (by norm_num) (by decide), bandSet Fs _ (by omega)]
      obtain ⟨c₄, k₄, e₄, hk₄, d33, d34, d35, d36, d37, Ft⟩ := setTwoB_exec (P := P) c₃
        e₃.wb_right S₃ he1
      have S₄ := keepSet Ft S₃
      have hA₄ : c₄.nreg ALLOC ≤ c.nreg ALLOC + k₃ := by
        rw [bandSet Ft _ (by ufo ALLOC)]
        have := F₃.2.2.2.2.2.2; omega
      have hLB : spanL (eeOf (Qof P) s.e₁ s.h₁ s.e₂ (nh (Qof P) s.e₂ s.h₂))
          (nh (Qof P) s.e₂ s.h₂) - 2 ≤ s.γ := by
        have := hsubB.h2; rwo [hQ] at this
      have hlogB := log_le_clog_succ hsubB.h1 hLB
      have hsB : (interiorModel (Qof P)).arcSet ((interiorModel (Qof P)).key (Qof P) ⟨s.e₁, s.h₁⟩)
          ((interiorModel (Qof P)).key (Qof P) ⟨s.e₂, s.h₂⟩) ⊇ oset (interiorWalk (Qof P))
          ((s.e₁ + 2) % (Qof P).n) ((interiorModel (Qof P)).param (Qof P) ⟨(s.e₁ + 2) % (Qof P).n, 0⟩)
          ((eeOf (Qof P) s.e₁ s.h₁ s.e₂ (nh (Qof P) s.e₂ s.h₂) - 2 : ℕ) +
            (interiorModel (Qof P)).param (Qof P) ⟨((s.e₁ + 2) % (Qof P).n +
              (eeOf (Qof P) s.e₁ s.h₁ s.e₂ (nh (Qof P) s.e₂ s.h₂) - 2)) % (Qof P).n,
              nh (Qof P) s.e₂ s.h₂⟩) := by
        rw [hset]; exact Set.subset_union_right
      obtain ⟨c₅, k₅, e₅, hk₅, hB₅, S₅, F₅, g₅⟩ := sqS_exec hsh c₄ e₄.wb_right S₄
        (u := (s.e₁ + 2) % (Qof P).n) (sh₀ := 0)
        (by rw [d33, hQ]) d34 (by rw [d35, c31]) (by rw [d36, c30]) (by rw [d37, c32])
        hsubB hLB ho1 ho2 hol (fun h => hoA (hsB h)) (bestSet Ft hB₃)
        (le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hA₄ _) _) _)
          (room_two hroom hk₃ hlogA hlogB))
      refine ⟨c₅, _, .ifLtN_false hcond (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
        cost_two hk₂ hk₃ hk₄ hk₅ hlogA hlogB, ?_, S₅,
        ((((frameIO_of_frameB (fun r h => bset_io h) Fs k₂).trans F₃).trans
          (frameIO_of_frameB (fun r h => bset_io h) Ft k₄)).trans F₅).mono (by simp) (by omega)⟩
      rw [hAd, hset, ← Set.union_assoc]
      exact hB₅
  obtain ⟨c₂, k₂, e₂, hk₂, hB₂, S₂, F₂⟩ := hbr
  -- the answer
  obtain ⟨c₃, k₃, e₃, hk₃, hhit, hno, F₃⟩ := outI_exec c₂ e₂.wb_right S₂ hB₂
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, fun h => ?_, fun h => ?_,
    ((Fr₁.trans F₂).trans (frameIO_of_frameB (B := Bout) (fun r hr => io_of_band (by
      sio only [Bout, Bool.or_eq_true, decide_eq_true_eq] at hr)) F₃ k₃)).mono
      (by simp) (by omega)⟩
  · obtain ⟨t, h1, h2, h3, h4⟩ := hhit h
    rw [Set.empty_union] at h1
    exact ⟨t, h1, h2, h3, h4⟩
  · have := hno h
    rw [Set.empty_union] at this
    exact this

end exec

end

end IOrc

end Chazelle.Core
