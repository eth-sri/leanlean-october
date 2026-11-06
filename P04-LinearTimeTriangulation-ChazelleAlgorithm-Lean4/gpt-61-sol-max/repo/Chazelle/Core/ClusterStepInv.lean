module

public import Chazelle.Core.ClusterStepMem

/-!
# WP-I, part 38: helpers for one split step

* `SFacts.of_static`: the static facts survive changes of the dynamic slots;
* `SInv.length_le`: the stack has at most `μ` entries;
* `m2_facts`: the memory after the marks and the copy.
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

section static

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g}
  {C : CoTree (starTree T a ha)} {R : BTree} {first : Fin μ → Fin N} {preE slot upT : ℕ → ℕ} {k c W : ℕ}

/-- **The static facts only read the static slots.** -/
theorem SFacts.of_static {S : SS} {A0 U : ℕ} {m m' : ℕ → ℕ}
    (h : SFacts M T a ha C R first preE slot upT k c S A0 U W m) (he : StaticEq A0 U m m') :
    SFacts M T a ha C R first preE slot upT k c S A0 U W m' := by
  have hL := h.lay
  have := hL.hFIRST; have := hL.hLEV; have := hL.hPV; have := hL.hFP; have := hL.hATT
  have := hL.hSO; have := hL.hSF; have := hL.hFPAR; have := hL.hFSZ; have := hL.hFPRE
  have := hL.hLBOT; have := hL.hLTOP; have := hL.hHALF; have := hL.hPOW; have := hL.hUPT
  have := hL.hUP; have := hL.hμU; have := hL.hNU; have := hL.hLU; have := hL.hVERT
  have := hL.hOPP; have hN := h.hN; have hμ := h.hμ
  have hlt : ∀ v : Fin μ, (v : ℕ) < μ := fun v => v.2
  have hltN : ∀ d : Fin N, (d : ℕ) < N := fun d => d.2
  refine ⟨hL, hN, hμ, h.planar, h.vert_first, fun d => ?_, fun d => ?_, fun v => ?_, fun v => ?_,
    h.lev_lt, fun d => ?_, fun d => ?_, fun x => ?_, fun x => ?_, fun g hg => ?_, fun g hg => ?_,
    h.r0, fun g hg => ?_, fun g hg => ?_, h.R_ok, h.R_n, h.R_up, h.R_root, h.R_pre,
    fun j hj g hg => ?_, h.upT_eq, h.upT_lt, fun x hx => ?_, fun j hj x hx => ?_,
    fun j hj => ?_, h.pow_big, h.pow_U, h.L_pos, fun w hw => ?_, fun v x hvx => ?_, fun v => ?_⟩
  · have := hltN d; rw [he _ (by omega)]; exact h.vert d
  · have := hltN d; rw [he _ (by omega)]; exact h.opp d
  · have := hlt v; rw [he _ (by omega)]; exact h.first v
  · have := hlt v; rw [he _ (by omega)]; exact h.lev v
  · have := hltN d; rw [he _ (by omega)]; exact h.att d
  · have := hltN d; rw [he _ (by omega)]; exact h.fp d
  · have := enc_lt x
    rw [he _ (by omega)]; exact h.so x
  · have := enc_lt x
    rw [he _ (by omega)]; exact h.sf x
  · have := hltN g; rw [he _ (by omega)]; exact h.fpar g hg
  · rw [he _ (by omega)]; exact h.fpar_lt g hg
  · rw [he _ (by omega)]; exact h.pre g hg
  · rw [he _ (by omega)]; exact h.sz g hg
  · rw [he _ (by omega)]; exact h.up_tab j hj g hg
  · rw [he _ (by omega)]; exact h.pv x hx
  · rw [he _ (by omega)]; exact h.upt_tab j hj x hx
  · rw [he _ (by omega)]; exact h.pow j hj
  · rw [he _ (by omega)]; exact h.half w hw
  · have := h.lev_lt v
    rw [he (S.bLBOT + _) (by omega), he (S.bLTOP + _) (by omega)]; exact h.win v x hvx
  · have := h.lev_lt v
    rw [he (S.bLBOT + _) (by omega), he (S.bLTOP + _) (by omega)]; exact h.win_k v

end static

section stack

variable {μ k s : ℕ} {H : Finset ℕ} {slab : ℕ → ℕ} {Adj : ℕ → ℕ → Prop}

/-- **The stack has at most `μ` entries** (each of them contributes at least `2` to the
potential `pot2`). -/
theorem SInv.length_le {act : ℕ → ℕ} {stk : List (ℕ × ℕ)} {fin : Finset (ℕ × ℕ)}
    {D : Finset ℕ} {nsp : ℕ} (hI : SInv μ k s H slab Adj act stk fin D nsp) :
    stk.length ≤ μ := by
  have h2 := hI.pot2
  have hge : ∑ p ∈ stk.toFinset, 2 ≤ ∑ p ∈ stk.toFinset, (2 * len p - s) :=
    Finset.sum_le_sum (fun p hp => by
      have := hI.big p (List.mem_toFinset.mp hp); omega)
  rw [Finset.sum_const, List.toFinset_card_of_nodup hI.nodup, smul_eq_mul] at hge
  omega

end stack

section m2

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g}
  {C : CoTree (starTree T a ha)} {R : BTree} {first : Fin μ → Fin N} {preE slot upT : ℕ → ℕ} {k c W : ℕ}

open Classical in
/-- **The memory after the marks and the copy.** -/
theorem m2_facts {S : SS} {A0 U : ℕ} {m : ℕ → ℕ} {lo hi : ℕ} {rest : List (ℕ × ℕ)}
    {fin : Finset (ℕ × ℕ)} {D : Finset ℕ} {nsp : ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m)
    (hD : DInv M T k c S m ((lo, hi) :: rest) fin D nsp) {lbot ltop : ℕ}
    (hwin : ∀ x : Fin μ, (x : ℕ) ∈ items (fun i => m (S.bACT + i)) (lo, hi) →
      lbot ≤ T.level x ∧ T.level x ≤ ltop) (f : Fin N) :
    let m2 := copyF (marksF m S lo hi lbot ltop upT f) S lo hi
    (∀ x, ¬ (S.bDF ≤ x ∧ x < S.bDF + S.μ) → ¬ (S.bTMP + lo ≤ x ∧ x < S.bTMP + hi) →
      m2 x = m x) ∧
    (∀ i, lo ≤ i → i < hi → m2 (S.bTMP + i) = m (S.bACT + i)) ∧
    (∀ y, y < μ → m2 (S.bDF + y) =
      if y ∈ items (fun i => m (S.bACT + i)) (lo, hi) ∧ markN T a f y then 1 else m (S.bDF + y)) ∧
    m2 (S.bFP + f) = M.fperm f := by
  intro m2
  have hL := hSF.lay
  have := hL.hFP; have := hL.hACT
  have := hL.hPOS; have := hL.hTMP; have := hL.hDF; have := hL.hμU; have := hL.hNU
  have := hL.hLEV
  have hN := hSF.hN; have hμ := hSF.hμ
  have hlv : Lv ((lo, hi) :: rest) fin (lo, hi) := Or.inl List.mem_cons_self
  have hhi : hi ≤ μ := hD.rng _ hlv
  have hmk := fun (y : ℕ) (hy : y < μ) => marksF_df (m0 := m) (S := S) (lo := lo) (hi := hi)
    (lbot := lbot) (ltop := ltop) T hSF.upT_eq (fun x hx => by rw [hμ] at hx ⊢; exact hSF.upT_lt x hx)
    hμ (fun x hx => hD.pos_iff hlv hx) hwin hSF.lev hSF.vert hSF.opp hSF.att
    (fun y hy => ⟨by omega, by omega⟩) f ⟨y, hy⟩
  have hmo : ∀ x, ¬ (S.bDF ≤ x ∧ x < S.bDF + S.μ) → marksF m S lo hi lbot ltop upT f x = m x := by
    intro x hx
    have hup : ∀ x, x < S.μ → upT x < S.μ := fun x hx => by
      rw [hμ] at hx ⊢; exact hSF.upT_lt x hx
    have hvl : ∀ u : Fin μ, (u : ℕ) < S.μ := fun u => by omega
    unfold marksF
    rw [markStep_other hup (by rw [hSF.att, hSF.vert]; exact hvl _) hx,
      markStep_other hup (by rw [hSF.opp, hSF.vert]; exact hvl _) hx,
      markStep_other hup (by rw [hSF.vert]; exact hvl _) hx]
  have hm2 : ∀ x, ¬ (S.bDF ≤ x ∧ x < S.bDF + S.μ) → ¬ (S.bTMP + lo ≤ x ∧ x < S.bTMP + hi) →
      m2 x = m x := by
    grind [copyF]
  refine ⟨hm2, fun i h1 h2 => ?_, fun y hy => ?_, ?_⟩
  · show copyF _ S lo hi _ = _
    unfold copyF
    grind
  · grind [copyF]
  · have hf : (f : ℕ) < N := f.2
    rw [hm2 _ (by omega) (by omega)]; exact hSF.fp f

end m2

end

end Chazelle.Core.Cluster
