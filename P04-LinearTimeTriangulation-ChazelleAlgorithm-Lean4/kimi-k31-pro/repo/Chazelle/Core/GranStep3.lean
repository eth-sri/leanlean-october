module

public import Chazelle.Core.GranStep2
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# WP-F, part 9: the removal preserves the invariant

`Inv.remove`: if the live chord `c` on top of the worklist is removable, then
`st.remove c (st.mu E c)` satisfies the invariant.  The pieces: the class of every referenced
class after the removal (`ref_cases`: the merged class `s0 c`, or an old class not touched by
`c`), the sides of the live chords (`rm_s0`, `rm_s1`: the chords of `s1 c` are relabelled), the
counts and the ring (`cnt_rm`, `ring_rm`), and the worklist (`work_rm`, via
`Merge.removable_of_removable_sdiff`).
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn)

variable {E : Env} {st : St}

/-- A position whose predecessor and successor coincide sees only that other live position. -/
theorem only_live {Lv : ℕ → Prop} {A : ℕ} {nxt prv : ℕ → ℕ} (h : RingOK Lv A nxt prv) {d : ℕ}
    (hd : d < A) (hdL : Lv d) (he : prv d = nxt d) {i : ℕ} (hi : i < A) (hiL : Lv i)
    (hid : i ≠ d) : i = prv d := by
  have hp := h.pred hd hdL
  have hs := h.succ hd hdL
  rw [← he] at hs
  by_contra hip
  rcases cyc_cover (natCast_ne hp.2.2.1) (natCast_ne hip) with h1 | h1 | h1
  · exact hp.2.2.2 i hi hiL h1
  · exact hid (by exact_mod_cast h1)
  · exact hs.2.2.2 i hi hiL h1

/-- Unlinking a live position when two other live positions remain. -/
theorem ringOK_unl {Lv : ℕ → Prop} {A : ℕ} {r : (ℕ → ℕ) × (ℕ → ℕ)} (h : RingOK Lv A r.1 r.2)
    {d : ℕ} (hd : d < A) (hdL : Lv d)
    (h2 : ∃ a b, a < A ∧ b < A ∧ Lv a ∧ Lv b ∧ a ≠ d ∧ b ≠ d ∧ a ≠ b) :
    RingOK (fun j => Lv j ∧ j ≠ d) A (St.unl r d).1 (St.unl r d).2 := by
  have hne : r.2 d ≠ r.1 d := by
    intro he
    obtain ⟨a, b, ha, hb, haL, hbL, had, hbd, hab⟩ := h2
    exact hab ((only_live h hd hdL he ha haL had).trans
      (only_live h hd hdL he hb hbL hbd).symm)
  exact ringOK_unlink h hd hdL hne

section Rm3

variable (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) {P : Set Point}
  (hs : Merge.IsSplit E.M.D (st.F E \ {cs E.M E.Q E.N c}) (cs E.M E.Q E.N c) P
    (st.cl E (st.s0 c)) (st.cl E (st.s1 c)))
include hE h hc hs

omit hE h hc hs in
/-- The relabelling of the first side. -/
theorem rm_s0 (hE : E.Good) (h : Inv E st) (hc : c ∈ st.L E)
    (_hs : Merge.IsSplit E.M.D (st.F E \ {cs E.M E.Q E.N c})
    (cs E.M E.Q E.N c) P (st.cl E (st.s0 c)) (st.cl E (st.s1 c))) {i : ℕ} (hi : i ∈ st.L E)
    (hic : i ≠ c) (μ : ℕ) :
    (st.remove c μ).s0 i = if st.s0 i = st.s1 c then st.s0 c else st.s0 i := by
  show (if i ∈ st.exl (st.s1 c) ∧ i ≠ c ∧ st.s0 i = st.s1 c then st.s0 c else st.s0 i) = _
  by_cases e : st.s0 i = st.s1 c
  · have hmem : i ∈ st.exl (st.s1 c) := by
      refine (exl_Y hE h hc i).2 ⟨hi, ?_⟩
      rw [← e]
      exact ((h.sides i hi).2.2.2 _ (St.cl_spec (st := st) hE (h.sides i hi).1).1).2 (Or.inl rfl)
    rw [ite_eq_left ⟨hmem, hic, e⟩, ite_eq_left e]
  · rw [ite_eq_right (fun h' => e h'.2.2), ite_eq_right e]

omit hE h hc hs in
/-- The relabelling of the second side. -/
theorem rm_s1 (hE : E.Good) (h : Inv E st) (hc : c ∈ st.L E)
    (_hs : Merge.IsSplit E.M.D (st.F E \ {cs E.M E.Q E.N c})
    (cs E.M E.Q E.N c) P (st.cl E (st.s0 c)) (st.cl E (st.s1 c))) {i : ℕ} (hi : i ∈ st.L E)
    (hic : i ≠ c) (μ : ℕ) :
    (st.remove c μ).s1 i = if st.s1 i = st.s1 c then st.s0 c else st.s1 i := by
  show (if i ∈ st.exl (st.s1 c) ∧ i ≠ c ∧ st.s1 i = st.s1 c then st.s0 c else st.s1 i) = _
  by_cases e : st.s1 i = st.s1 c
  · have hmem : i ∈ st.exl (st.s1 c) := by
      refine (exl_Y hE h hc i).2 ⟨hi, ?_⟩
      rw [← e]
      exact ((h.sides i hi).2.2.2 _ (St.cl_spec (st := st) hE (h.sides i hi).2.1).1).2
        (Or.inr rfl)
    rw [ite_eq_left ⟨hmem, hic, e⟩, ite_eq_left e]
  · rw [ite_eq_right (fun h' => e h'.2.2), ite_eq_right e]

/-- The class after the removal of an old class. -/
theorem rm_cl_g {x : ℕ} (hx : x < E.R) (μ : ℕ) :
    (st.remove c μ).cl E x = if st.cl E x = st.cl E (st.s0 c) ∨ st.cl E x = st.cl E (st.s1 c)
      then P else st.cl E x := by
  split_ifs with hxc
  · exact rm_cl_in hE h hc hs hx hxc μ
  · push Not at hxc
    exact rm_cl_out hE h hc hs hx hxc.1 hxc.2 μ

/-- The class of a relabelled side is the class of the old side. -/
theorem rm_cl_s0 {i : ℕ} (hi : i ∈ st.L E) (hic : i ≠ c) (μ : ℕ) :
    (st.remove c μ).cl E ((st.remove c μ).s0 i) = (st.remove c μ).cl E (st.s0 i) := by
  rw [rm_s0 hE h hc hs hi hic]
  split_ifs with e
  · rw [e, rm_cl_in hE h hc hs (h.sides c hc).1 (Or.inl rfl),
      rm_cl_in hE h hc hs (h.sides c hc).2.1 (Or.inr rfl)]
  · rfl

theorem rm_cl_s1 {i : ℕ} (hi : i ∈ st.L E) (hic : i ≠ c) (μ : ℕ) :
    (st.remove c μ).cl E ((st.remove c μ).s1 i) = (st.remove c μ).cl E (st.s1 i) := by
  rw [rm_s1 hE h hc hs hi hic]
  split_ifs with e
  · rw [e, rm_cl_in hE h hc hs (h.sides c hc).1 (Or.inl rfl),
      rm_cl_in hE h hc hs (h.sides c hc).2.1 (Or.inr rfl)]
  · rfl

omit hE h hc hs in
/-- The merged region is not an old region. -/
theorem g_eq_P_iff (_hE : E.Good) (_h : Inv E st) (hc : c ∈ st.L E)
    (hs : Merge.IsSplit E.M.D (st.F E \ {cs E.M E.Q E.N c}) (cs E.M E.Q E.N c) P (st.cl E (st.s0 c))
    (st.cl E (st.s1 c))) {W : Set Point} (hW : W ∈ E.M.regions (st.F E)) :
    (if W = st.cl E (st.s0 c) ∨ W = st.cl E (st.s1 c) then P else W) = P ↔
      W = st.cl E (st.s0 c) ∨ W = st.cl E (st.s1 c) := by
  split_ifs with hw
  · exact ⟨fun _ => hw, fun _ => rfl⟩
  · push Not at hw
    rcases split_cases (St.cs_mem_F hc) hs hW with e | e | ⟨-, e⟩
    · exact absurd e hw.1
    · exact absurd e hw.2
    · exact ⟨fun e' => absurd e' e, fun e' => by tauto⟩

/-- **The sides after the removal.** -/
theorem sides_rm {i : ℕ} (hi : i ∈ st.L E) (hic : i ≠ c) (μ : ℕ) :
    (st.remove c μ).s0 i < E.R ∧ (st.remove c μ).s1 i < E.R ∧
      (st.remove c μ).cl E ((st.remove c μ).s0 i) ≠ (st.remove c μ).cl E ((st.remove c μ).s1 i) ∧
      ∀ Z ∈ E.M.regions ((st.remove c μ).F E), (TouchesIn E.M.D (cs E.M E.Q E.N i) Z ↔
        Z = (st.remove c μ).cl E ((st.remove c μ).s0 i) ∨
          Z = (st.remove c μ).cl E ((st.remove c μ).s1 i)) := by
  obtain ⟨hs0, hs1, hne, htouch⟩ := h.sides i hi
  obtain ⟨hc0, hc1, -, htc⟩ := h.sides c hc
  have hW0 := (St.cl_spec (st := st) hE hs0).1
  have hW1 := (St.cl_spec (st := st) hE hs1).1
  rw [rm_cl_s0 hE h hc hs hi hic, rm_cl_s1 hE h hc hs hi hic, rm_cl_g hE h hc hs hs0,
    rm_cl_g hE h hc hs hs1, rm_F hE h hc]
  refine ⟨by rw [rm_s0 hE h hc hs hi hic]; split_ifs <;> assumption,
    by rw [rm_s1 hE h hc hs hi hic]; split_ifs <;> assumption, ?_, fun Z hZ => ?_⟩
  · intro he
    by_cases hP : (if st.cl E (st.s0 i) = st.cl E (st.s0 c) ∨ st.cl E (st.s0 i) = st.cl E (st.s1 c)
        then P else st.cl E (st.s0 i)) = P
    · have e0 := (g_eq_P_iff hE h hc hs hW0).1 hP
      have e1 := (g_eq_P_iff hE h hc hs hW1).1 (he ▸ hP)
      -- `i` touches both classes of `c`
      have t0 : TouchesIn E.M.D (cs E.M E.Q E.N i) (st.cl E (st.s0 i)) :=
        (htouch _ hW0).2 (Or.inl rfl)
      have t1 : TouchesIn E.M.D (cs E.M E.Q E.N i) (st.cl E (st.s1 i)) :=
        (htouch _ hW1).2 (Or.inr rfl)
      rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1
      · exact hne (e0.trans e1.symm)
      · rw [e0] at t0; rw [e1] at t1; exact not_both hE h hc hs hi hic t0 t1
      · rw [e0] at t0; rw [e1] at t1; exact not_both hE h hc hs hi hic t1 t0
      · exact hne (e0.trans e1.symm)
    · have hP' : (if st.cl E (st.s1 i) = st.cl E (st.s0 c) ∨ st.cl E (st.s1 i) = st.cl E (st.s1 c)
          then P else st.cl E (st.s1 i)) ≠ P := he ▸ hP
      rw [ite_eq_right (fun h' => hP (ite_eq_left h'))] at he
      rw [ite_eq_right (fun h' => hP' (ite_eq_left h'))] at he
      exact hne he
  · by_cases hZP : Z = P
    · subst hZP
      rw [touch_P hE h hc hs hi hic, htouch _ (h.cl_mem hE hc).1, htouch _ (h.cl_mem hE hc).2,
        eq_comm (a := Z), eq_comm (a := Z), g_eq_P_iff hE h hc hs hW0, g_eq_P_iff hE h hc hs hW1]
      tauto
    · obtain ⟨hZS, hZ0, hZ1⟩ := other_ne hE h hc hs hZ hZP
      rw [htouch Z hZS]
      have k : ∀ W, (Z = (if W = st.cl E (st.s0 c) ∨ W = st.cl E (st.s1 c) then P else W) ↔
          Z = W) := by
        intro W
        split_ifs with hw
        · constructor
          · intro e; exact absurd e hZP
          · intro e; rcases hw with hw | hw
            · exact absurd (e.trans hw) hZ0
            · exact absurd (e.trans hw) hZ1
        · exact Iff.rfl
      rw [k, k]

/-- **The referenced classes after the removal**: the merged class `s0 c`, or an old class not
touched by `c`. -/
theorem ref_cases {x : ℕ} (μ : ℕ) (hx : (st.remove c μ).Ref E x) :
    x = st.s0 c ∨ (st.Ref E x ∧ x < E.R ∧ st.cl E x ≠ st.cl E (st.s0 c) ∧
      st.cl E x ≠ st.cl E (st.s1 c)) := by
  obtain ⟨i, hi, hx⟩ := hx
  rw [rm_L hE h hc] at hi
  have hic : i ≠ c := fun e => hi.2 (by rwr [e])
  have hiL := hi.1
  have hX : st.Ref E (st.s0 c) := ⟨c, hc, Or.inl rfl⟩
  have hY : st.Ref E (st.s1 c) := ⟨c, hc, Or.inr rfl⟩
  have key : ∀ w, st.Ref E w → w < E.R → x = w → w ≠ st.s1 c →
      x = st.s0 c ∨ (st.Ref E x ∧ x < E.R ∧ st.cl E x ≠ st.cl E (st.s0 c) ∧
        st.cl E x ≠ st.cl E (st.s1 c)) := by
    intro w hw hwR hxw hwY
    subst hxw
    by_cases hwX : x = st.s0 c
    · exact Or.inl hwX
    · exact Or.inr ⟨hw, hwR, fun e => hwX (h.refInj _ _ hw hX e),
        fun e => hwY (h.refInj _ _ hw hY e)⟩
  rcases hx with hx | hx
  · rw [rm_s0 hE h hc hs hiL hic] at hx
    split_ifs at hx with e
    · exact Or.inl hx
    · exact key _ ⟨i, hiL, Or.inl rfl⟩ (h.sides i hiL).1 hx e
  · rw [rm_s1 hE h hc hs hiL hic] at hx
    split_ifs at hx with e
    · exact Or.inl hx
    · exact key _ ⟨i, hiL, Or.inr rfl⟩ (h.sides i hiL).2.1 hx e

/-- The new exit list has at most `D` entries. -/
theorem newEx_le (hlow : st.deg (st.s0 c) < 3 ∨ st.deg (st.s1 c) < 3) :
    (st.newEx c).length ≤ E.D := by
  have l := newEx_length hE h hc hs
  have dX := (h.cls _ ⟨c, hc, Or.inl rfl⟩).2.2.2.2
  have dY := (h.cls _ ⟨c, hc, Or.inr rfl⟩).2.2.2.2
  omega

/-- **The class data after the removal.** -/
theorem cls_rm (hlow : st.deg (st.s0 c) < 3 ∨ st.deg (st.s1 c) < 3) {x : ℕ}
    (hx : (st.remove c (st.mu E c)).Ref E x) :
    (st.remove c (st.mu E c)).deg x =
        E.M.deg ((st.remove c (st.mu E c)).F E) ((st.remove c (st.mu E c)).cl E x) ∧
      (st.remove c (st.mu E c)).wt x =
        E.M.weight ((st.remove c (st.mu E c)).F E) ((st.remove c (st.mu E c)).cl E x) ∧
      ((st.remove c (st.mu E c)).exl x).Nodup ∧
      (∀ i, i ∈ (st.remove c (st.mu E c)).exl x ↔ i ∈ (st.remove c (st.mu E c)).L E ∧
        TouchesIn E.M.D (cs E.M E.Q E.N i) ((st.remove c (st.mu E c)).cl E x)) ∧
      (st.remove c (st.mu E c)).deg x ≤ E.D := by
  set μ := st.mu E c
  rw [rm_F hE h hc, rm_L hE h hc]
  rcases ref_cases hE h hc hs μ hx with rfl | ⟨hxR, hxlt, h1, h2⟩
  · have hcl : (st.remove c μ).cl E (st.s0 c) = P :=
      rm_cl_in hE h hc hs (h.sides c hc).1 (Or.inl rfl) μ
    have hdeg : (st.remove c μ).deg (st.s0 c) = (st.newEx c).length := by
      show Function.update st.deg (st.s0 c) _ (st.s0 c) = _
      rw [Function.update_self]
    have hexl : (st.remove c μ).exl (st.s0 c) = st.newEx c := by
      refine exl_of_list _ _ hdeg fun t ht => ?_
      show (if st.s0 c = st.s0 c ∧ t < (st.newEx c).length then (st.newEx c).getD t 0
        else st.ex (st.s0 c) t) = _
      rw [ite_eq_left ⟨rfl, ht⟩]
    rw [hcl, hdeg, hexl]
    refine ⟨(deg_P hE h hc hs).symm, ?_, newEx_nodup hE h hc hs, fun i => ?_,
      newEx_le hE h hc hs hlow⟩
    · show Function.update st.wt (st.s0 c) μ (st.s0 c) = _
      rw [Function.update_self]
      exact h.mu_eq hE hc hs
    · rw [mem_newEx hE h hc hs]
      simp only [mem_sdiff, mem_singleton_iff]
      tauto
  · have hxX : x ≠ st.s0 c := fun e => h1 (by rw [e])
    obtain ⟨hcx, hxP⟩ := cl_out hE h hc hs hxlt h1 h2
    have hcl  := rm_cl_out hE h hc hs hxlt h1 h2 μ
    have hdeg : (st.remove c μ).deg x = st.deg x := by
      show Function.update st.deg (st.s0 c) _ x = _
      rw [Function.update_of_ne hxX]
    have hexl : (st.remove c μ).exl x = st.exl x := by
      unfold St.exl
      rw [hdeg]
      congr 1
      funext t
      show (if x = st.s0 c ∧ (t : ℕ) < (st.newEx c).length then (st.newEx c).getD t 0
        else st.ex x t) = _
      rw [ite_eq_right (fun h' => hxX h'.1)]
    obtain ⟨d1, w1, n1, m1, l1⟩ := h.cls x hxR
    rw [hcl, hdeg, hexl]
    refine ⟨by rwx [deg_other hE h hc hs hcx hxP], ?_, n1, fun i => ?_, l1⟩
    · show Function.update st.wt (st.s0 c) μ x = _
      rw [Function.update_of_ne hxX, weight_other' hE h hc hs hcx hxP]
      exact w1
    · rw [m1]
      simp only [mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨hi, ht⟩
        refine ⟨⟨hi, fun e => ?_⟩, ht⟩
        subst e
        have := (split_touches_iff hE.hM (St.F_adm (st := st) hE) (St.F_finite (st := st) hE)
          (St.cs_mem_F hc) hs (St.cl_spec (st := st) hE hxlt).1).1 ht
        rcases this with e | e
        · exact h1 e
        · exact h2 e
      · rintro ⟨⟨hi, -⟩, ht⟩; exact ⟨hi, ht⟩

/-- **Referenced classes stay distinct.** -/
theorem refInj_rm {x y : ℕ} (μ : ℕ) (hx : (st.remove c μ).Ref E x)
    (hy : (st.remove c μ).Ref E y)
    (he : (st.remove c μ).cl E x = (st.remove c μ).cl E y) : x = y := by
  have hP  := rm_cl_in hE h hc hs (h.sides c hc).1 (Or.inl rfl) μ
  rcases ref_cases hE h hc hs μ hx with rfl | ⟨hxR, hxlt, h1, h2⟩ <;>
    rcases ref_cases hE h hc hs μ hy with rfl | ⟨hyR, hylt, h1', h2'⟩
  · rfl
  · rw [hP, rm_cl_out hE h hc hs hylt h1' h2'] at he
    exact absurd he.symm (cl_out hE h hc hs hylt h1' h2').2
  · rw [hP, rm_cl_out hE h hc hs hxlt h1 h2] at he
    exact absurd he (cl_out hE h hc hs hxlt h1 h2).2
  · rw [rm_cl_out hE h hc hs hxlt h1 h2, rm_cl_out hE h hc hs hylt h1' h2'] at he
    exact h.refInj _ _ hxR hyR he

end Rm3

end

end Gran

end Chazelle.Core
