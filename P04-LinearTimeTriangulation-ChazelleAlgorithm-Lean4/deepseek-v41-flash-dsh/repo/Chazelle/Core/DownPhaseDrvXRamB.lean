module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvXRamA

/-!
# Down phase, extraction (D6), RAM part 2: register-step helpers, host points

* `NRegs d d' f`: `d'` differs from `d` only in its natural registers, which are `f`; the step
  lemmas `x_const`, `x_copy`, `x_sub`, `x_add`, `x_skipR`, `x_ifR`, `x_if` (conditionals as one
  step whose effect is an `if`).
* `Enc d s`: the registers `217070 … 217072` encode the symbolic point `s`.
* `lookS_exec`: `lookS` finds host point `k` of a well-formed host.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK

@[expose] public section

/-! ## Register steps -/

/-- `d'` differs from `d` only in the natural registers, which are `f`. -/
def NRegs (d d' : Config) (f : ℕ → ℕ) : Prop :=
  d'.nreg = f ∧ d'.rreg = d.rreg ∧ d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output

section steps

variable {P : Polygon} {W : ℕ}

theorem x_const (d : Config) (hw : WordsBounded W d) (r v : ℕ) (hv : v ≤ W) :
    ∃ d' k, Exec P W (block [.constN r v]) d d' k ∧ k ≤ 1 ∧ NRegs d d' (upd d.nreg r v) := by
  refine spec_step (Machine.Exec.constN hw _ _ hv) (fun hw₁ => ?_)
  exact spec_nil hw₁ ⟨le_rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem x_copy (d : Config) (hw : WordsBounded W d) (r a : ℕ) :
    ∃ d' k, Exec P W (block [.copyN r a]) d d' k ∧ k ≤ 1 ∧ NRegs d d' (upd d.nreg r (d.nreg a)) := by
  refine spec_step (Machine.Exec.copyN hw _ _) (fun hw₁ => ?_)
  exact spec_nil hw₁ ⟨le_rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem x_sub (d : Config) (hw : WordsBounded W d) (r a b : ℕ) :
    ∃ d' k, Exec P W (block [.subN r a b]) d d' k ∧ k ≤ 1 ∧
      NRegs d d' (upd d.nreg r (d.nreg a - d.nreg b)) := by
  refine spec_step (Machine.Exec.subN hw _ _ _) (fun hw₁ => ?_)
  exact spec_nil hw₁ ⟨le_rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem x_skipR (d : Config) (hw : WordsBounded W d) (r : ℕ) :
    ∃ d' k, Exec P W .skip d d' k ∧ k ≤ 1 ∧ NRegs d d' (upd d.nreg r (d.nreg r)) :=
  ⟨d, 0, .skip hw, ⋄, by rw [Machine.upd_eq_self], rfl, rfl, rfl, rfl⟩

theorem x_mono {s : Stmt} {d : Config} {K K' : ℕ} {Q : Config → Prop}
    (h : ∃ d' k, Exec P W s d d' k ∧ k ≤ K ∧ Q d') (hK : K ≤ K') :
    ∃ d' k, Exec P W s d d' k ∧ k ≤ K' ∧ Q d' := by
  obtain ⟨d', k, e, hk, q⟩ := h
  exact ⟨d', k, e, ⋄, q⟩

theorem x_if {a b : ℕ} {t e : Stmt} {d : Config} {K : ℕ} {f g : ℕ → ℕ}
    (ht : d.nreg a < d.nreg b → ∃ d' k, Exec P W t d d' k ∧ k ≤ K ∧ NRegs d d' f)
    (he : ¬ d.nreg a < d.nreg b → ∃ d' k, Exec P W e d d' k ∧ k ≤ K ∧ NRegs d d' g) :
    ∃ d' k, Exec P W (.ifLtN a b t e) d d' k ∧ k ≤ K + 2 ∧
      NRegs d d' (if d.nreg a < d.nreg b then f else g) := by
  by_cases h : d.nreg a < d.nreg b
  · obtain ⟨d', k, ex, hk, hn⟩ := ht h
    exact ⟨d', k + 1, .ifLtN_true h ex, ⋄, by rw [ite_eq_left h]; exact hn⟩
  · obtain ⟨d', k, ex, hk, hn⟩ := he h
    exact ⟨d', k + 2, .ifLtN_false h ex, ⋄, by rw [ite_eq_right h]; exact hn⟩

theorem x_ifR {a b r : ℕ} {t e : Stmt} {d : Config} {K : ℕ} {v₁ v₂ : ℕ}
    (ht : d.nreg a < d.nreg b → ∃ d' k, Exec P W t d d' k ∧ k ≤ K ∧ NRegs d d' (upd d.nreg r v₁))
    (he : ¬ d.nreg a < d.nreg b → ∃ d' k, Exec P W e d d' k ∧ k ≤ K ∧
      NRegs d d' (upd d.nreg r v₂)) :
    ∃ d' k, Exec P W (.ifLtN a b t e) d d' k ∧ k ≤ K + 2 ∧
      NRegs d d' (upd d.nreg r (if d.nreg a < d.nreg b then v₁ else v₂)) := by
  obtain ⟨d', k, ex, hk, hn⟩ := x_if ht he
  refine ⟨d', k, ex, hk, ?_⟩
  by_cases h : d.nreg a < d.nreg b
  · Ξ' ite_eq_left h at hn ⊢; exact hn
  · Ξ' ite_eq_right h at hn ⊢; exact hn

/-- Sequencing with an `NRegs` first part. -/
theorem x_seq {s t : Stmt} {d : Config} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop}
    (h₁ : ∃ d₁ k₁, Exec P W s d d₁ k₁ ∧ k₁ ≤ K₁ ∧ Q₁ d₁)
    (h₂ : ∀ d₁, WordsBounded W d₁ → Q₁ d₁ → ∃ d₂ k₂, Exec P W t d₁ d₂ k₂ ∧ k₂ ≤ K₂ ∧ Q₂ d₂) :
    ∃ d₂ k, Exec P W (.seq s t) d d₂ k ∧ k ≤ K₁ + K₂ ∧ Q₂ d₂ := by
  obtain ⟨d₁, k₁, e₁, hk₁, q₁⟩ := h₁
  obtain ⟨d₂, k₂, e₂, hk₂, q₂⟩ := h₂ d₁ e₁.wb_right q₁
  exact ⟨d₂, k₁ + k₂, .seq e₁ e₂, ⋄, q₂⟩

end steps

/-! ## Host points -/

/-- The registers `217070 … 217072` encode the symbolic point `s`. -/
def Enc (d : Config) : SymPt → Prop
  | .vtx j => d.nreg 217070 = 1 ∧ d.nreg 217071 = j
  | .onEdge e h => d.nreg 217070 = 2 ∧ d.nreg 217071 = e ∧ d.nreg 217072 = h

theorem Enc.congr {d d' : Config} {s : SymPt} (h : Enc d s) (h0 : d'.nreg 217070 = d.nreg 217070)
    (h1 : d'.nreg 217071 = d.nreg 217071) (h2 : d'.nreg 217072 = d.nreg 217072) : Enc d' s := by
  cases s <;> ϴ' Enc at h ⊢ <;> omega

/-- A host item at address `p` (three words). -/
def ItemAt (m : ℕ → ℕ) (p : ℕ) : HostItem → Prop
  | .run a ℓ => m p = 0 ∧ m (p + 1) = a ∧ m (p + 2) = ℓ
  | .pt (.vtx j) => m p = 1 ∧ m (p + 1) = j
  | .pt (.onEdge e h) => m p = 2 ∧ m (p + 1) = e ∧ m (p + 2) = h

/-- A well-formed host item. -/
def ItemWF (n : ℕ) : HostItem → Prop
  | .run a ℓ => a < n ∧ ℓ < n
  | .pt x => x.Lt n

theorem itemAt_of_hostAt {m : ℕ → ℕ} {B : ℕ} {H : Host} (hH : HostAt m B H) {i : ℕ}
    (hi : i < H.length) : ItemAt m (B + 1 + 3 * i) (H.getD i (.run 0 0)) := by
  have h := hH.2 i hi
  have e1 : B + 1 + 3 * i + 1 = B + 2 + 3 * i := ⋄
  have e2 : B + 1 + 3 * i + 2 = B + 3 + 3 * i := ⋄
  rcases hx : H.getD i (.run 0 0) with ⟨a, ℓ⟩ | ⟨j | ⟨e, h'⟩⟩ <;> Ξ' hx at h <;>
    ϴ' ItemAt, e1, e2 at h ⊢ <;> exact h

theorem itemWF_of_hostWF {n : ℕ} {H : Host} (hH : HostWF n H) {i : ℕ} (hi : i < H.length) :
    ItemWF n (H.getD i (.run 0 0)) := by
  have hmem : H.getD i (.run 0 0) ∈ H := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have h := hH _ hmem
  rcases hx : H.getD i (.run 0 0) with ⟨a, ℓ⟩ | x <;> Ξ' hx at h <;> exact h

theorem pts_take_succ {n : ℕ} {H : Host} {j : ℕ} (hj : j < H.length) :
    Host.pts n (H.take (j + 1)) = Host.pts n (H.take j) ++ (H.getD j (.run 0 0)).pts n := by
  unfold Host.pts
  rw [List.take_add_one, List.flatMap_append, List.getElem?_eq_getElem hj,
    List.getD_eq_getElem _ _ hj]
  simp

theorem hpt_take {n : ℕ} {H : Host} {j k : ℕ} (hk : k < (Host.pts n (H.take j)).length) :
    hpt n H k = (Host.pts n (H.take j)).getD k (.vtx 0) := by
  unfold hpt
  conv_lhs => rw [← List.take_append_drop j H]
  unfold Host.pts at hk ⊢
  Ξ List.flatMap_append, List.getD_append _ _ _ _ hk

theorem run_pts_length (n a ℓ : ℕ) : ((HostItem.run a ℓ).pts n).length = ℓ + 1 := by
  Θ HostItem.pts

theorem run_pts_getD (n a ℓ : ℕ) {t : ℕ} (ht : t ≤ ℓ) :
    ((HostItem.run a ℓ).pts n).getD t (.vtx 0) = .vtx ((a + t) % n) := by
  ϴ HostItem.pts
  Ξ List.getD_eq_getElem _ _ (by simp; omega)
  simp

/-! ## `lookS` -/

/-- The run case of `lookBody`. -/
def lookRun : Stmt :=
  .seq
    (.ifLtN 217090 217093 .skip
      (.seq (block [.subN 217097 217090 217093])
        (.ifLtN 217096 217097 .skip
          (.seq (block [.constN 217070 1, .addN 217071 217095 217097])
            (.ifLtN 217071 217020 .skip (block [.subN 217071 217071 217020]))))))
    (block [.addN 217093 217093 217096, .addN 217093 217093 217027])

/-- The point case of `lookBody`. -/
def lookPt : Stmt :=
  .seq
    (.ifLtN 217090 217093 .skip
      (.ifLtN 217093 217090 .skip
        (block [.copyN 217070 217094, .copyN 217071 217095, .copyN 217072 217096])))
    (block [.addN 217093 217093 217027])

/-- The first block of `lookBody`. -/
def lookRd : Stmt :=
  block [.loadN 217094 217092, .addN 217097 217092 217027, .loadN 217095 217097,
    .addN 217097 217097 217027, .loadN 217096 217097]

/-- The last block of `lookBody`. -/
def lookNx : Stmt :=
  block [.addN 217092 217092 217027, .addN 217092 217092 217027, .addN 217092 217092 217027,
    .addN 217091 217091 217027]

theorem lookBody_eq : lookBody = .seq lookRd (.seq (.ifLtN 217094 217027 lookRun lookPt) lookNx) :=
  rfl

/-- The registers `lookS` writes. -/
def Blook (r : ℕ) : Bool :=
  decide (r = 217070 ∨ r = 217071 ∨ r = 217072 ∨ (217091 ≤ r ∧ r ≤ 217097))

/-- The registers the item cases write. -/
def Bitem (r : ℕ) : Bool :=
  decide (r = 217070 ∨ r = 217071 ∨ r = 217072 ∨ r = 217093 ∨ r = 217097)

theorem wr_lookRun : wr Bitem lookRun = true := ⌖
theorem wr_lookPt : wr Bitem lookPt = true := ⌖

section look

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 2000000 in
theorem lookRun_exec (d : Config) (hw : WordsBounded W d) {n a ℓ cum : ℕ}
    (h20 : d.nreg 217020 = n) (h27 : d.nreg 217027 = 1) (h93 : d.nreg 217093 = cum)
    (h95 : d.nreg 217095 = a) (h96 : d.nreg 217096 = ℓ) (ha : a < n) (hℓ : ℓ < n)
    (hnW : 2 * n ≤ W) (hcW : cum + ℓ + 1 ≤ W) :
    ∃ d' k, Exec P W lookRun d d' k ∧ k ≤ 14 ∧ d'.nreg 217093 = cum + (ℓ + 1) ∧
      (d.nreg 217090 < cum → d'.nreg 217070 = d.nreg 217070 ∧ d'.nreg 217071 = d.nreg 217071 ∧
        d'.nreg 217072 = d.nreg 217072) ∧
      (cum ≤ d.nreg 217090 → d.nreg 217090 ≤ cum + ℓ →
        Enc d' (.vtx ((a + (d.nreg 217090 - cum)) % n))) ∧ FrameB Bitem d d' := by
  obtain ⟨d', k, ex, hk, h1, h2, h3⟩ : ∃ d' k, Exec P W lookRun d d' k ∧ k ≤ 14 ∧
      d'.nreg 217093 = cum + (ℓ + 1) ∧
      (d.nreg 217090 < cum → d'.nreg 217070 = d.nreg 217070 ∧ d'.nreg 217071 = d.nreg 217071 ∧
        d'.nreg 217072 = d.nreg 217072) ∧
      (cum ≤ d.nreg 217090 → d.nreg 217090 ≤ cum + ℓ →
        Enc d' (.vtx ((a + (d.nreg 217090 - cum)) % n))) := by
    unfold lookRun
    refine spec_seq ?_
    by_cases c1 : d.nreg 217090 < d.nreg 217093
    · refine spec_ifLtN_true c1 ?_
      refine spec_skip hw ?_
      exec_block
      · omega
      · config_simp; omega
      · refine ⟨⋄, by config_simp; omega, fun _ => ⟨by config_simp, by config_simp,
          by config_simp⟩, fun h _ => absurd c1 (⋄)⟩
    · refine spec_ifLtN_false c1 ?_
      refine spec_seq ?_
      exec_block
      by_cases c2 : ℓ < d.nreg 217090 - cum
      · refine spec_ifLtN_true (by config_simp; omega) ?_
        refine spec_skip ‹_› ?_
        exec_block
        · config_simp; omega
        · config_simp; omega
        · refine ⟨⋄, by config_simp; omega, fun h => absurd h (⋄),
            fun _ h => absurd c2 (⋄)⟩
      · refine spec_ifLtN_false (by config_simp; omega) ?_
        refine spec_seq ?_
        exec_block
        · omega
        · config_simp; omega
        by_cases c3 : a + (d.nreg 217090 - cum) < n
        · refine spec_ifLtN_true (by config_simp; omega) ?_
          refine spec_skip ‹_› ?_
          exec_block
          · config_simp; omega
          · config_simp; omega
          · refine ⟨⋄, by config_simp; omega, fun h => absurd h (⋄),
              fun _ _ => ?_⟩
            ϴ Enc
            config_simp
            rw [Nat.mod_eq_of_lt c3]; omega
        · refine spec_ifLtN_false (by config_simp; omega) ?_
          exec_block
          · config_simp; omega
          · config_simp; omega
          · refine ⟨⋄, by config_simp; omega, fun h => absurd h (⋄),
              fun _ _ => ?_⟩
            ϴ Enc
            config_simp
            Ξ Nat.mod_eq_sub_mod (⋄), Nat.mod_eq_of_lt (⋄)
            omega
  exact ⟨d', k, ex, hk, h1, h2, h3, exec_frameB ex wr_lookRun⟩

set_option maxHeartbeats 1000000 in
theorem lookPt_exec (d : Config) (hw : WordsBounded W d) {cum : ℕ}
    (h27 : d.nreg 217027 = 1) (h93 : d.nreg 217093 = cum) (hcW : cum + 1 ≤ W) :
    ∃ d' k, Exec P W lookPt d d' k ∧ k ≤ 8 ∧ d'.nreg 217093 = cum + 1 ∧
      (d.nreg 217090 ≠ cum → d'.nreg 217070 = d.nreg 217070 ∧ d'.nreg 217071 = d.nreg 217071 ∧
        d'.nreg 217072 = d.nreg 217072) ∧
      (d.nreg 217090 = cum → d'.nreg 217070 = d.nreg 217094 ∧ d'.nreg 217071 = d.nreg 217095 ∧
        d'.nreg 217072 = d.nreg 217096) ∧ FrameB Bitem d d' := by
  obtain ⟨d', k, ex, hk, h1, h2, h3⟩ : ∃ d' k, Exec P W lookPt d d' k ∧ k ≤ 8 ∧
      d'.nreg 217093 = cum + 1 ∧
      (d.nreg 217090 ≠ cum → d'.nreg 217070 = d.nreg 217070 ∧ d'.nreg 217071 = d.nreg 217071 ∧
        d'.nreg 217072 = d.nreg 217072) ∧
      (d.nreg 217090 = cum → d'.nreg 217070 = d.nreg 217094 ∧ d'.nreg 217071 = d.nreg 217095 ∧
        d'.nreg 217072 = d.nreg 217096) := by
    unfold lookPt
    refine spec_seq ?_
    by_cases c1 : d.nreg 217090 < d.nreg 217093
    · refine spec_ifLtN_true c1 ?_
      refine spec_skip hw ?_
      exec_block
      · omega
      · refine ⟨⋄, by config_simp; omega, fun _ => ⟨by config_simp, by config_simp,
          by config_simp⟩, fun h => absurd c1 (⋄)⟩
    · refine spec_ifLtN_false c1 ?_
      by_cases c2 : d.nreg 217093 < d.nreg 217090
      · refine spec_ifLtN_true c2 ?_
        refine spec_skip hw ?_
        exec_block
        · omega
        · refine ⟨⋄, by config_simp; omega, fun _ => ⟨by config_simp, by config_simp,
            by config_simp⟩, fun h => absurd c2 (⋄)⟩
      · refine spec_ifLtN_false c2 ?_
        exec_block
        · config_simp; omega
        · refine ⟨⋄, by config_simp; omega, fun h => absurd h (⋄),
            fun _ => ⟨by config_simp, by config_simp, by config_simp⟩⟩
  exact ⟨d', k, ex, hk, h1, h2, h3, exec_frameB ex wr_lookPt⟩

set_option maxHeartbeats 2000000 in
/-- **One host item of `lookS`.** -/
theorem lookBody_exec (d : Config) (hw : WordsBounded W d) {n p cum : ℕ} {it : HostItem}
    (h20 : d.nreg 217020 = n) (h27 : d.nreg 217027 = 1) (h92 : d.nreg 217092 = p)
    (h93 : d.nreg 217093 = cum) (hit : ItemAt d.nmem p it) (hwf : ItemWF n it)
    (hpW : p + 3 ≤ W) (hcW : cum + (it.pts n).length ≤ W) (h91W : d.nreg 217091 + 1 ≤ W)
    (hnW : 2 * n ≤ W) :
    ∃ d' k, Exec P W lookBody d d' k ∧ k ≤ 30 ∧
      d'.nreg 217091 = d.nreg 217091 + 1 ∧ d'.nreg 217092 = p + 3 ∧
      d'.nreg 217093 = cum + (it.pts n).length ∧
      (d.nreg 217090 < cum → d'.nreg 217070 = d.nreg 217070 ∧ d'.nreg 217071 = d.nreg 217071 ∧
        d'.nreg 217072 = d.nreg 217072) ∧
      (cum ≤ d.nreg 217090 → d.nreg 217090 < cum + (it.pts n).length →
        Enc d' ((it.pts n).getD (d.nreg 217090 - cum) (.vtx 0))) ∧
      FrameB Blook d d' := by
  rw [lookBody_eq]
  -- read the item
  obtain ⟨d1, k1, e1, hk1, a94, a95, a96, f1, m1, -⟩ : ∃ d1 k1, Exec P W lookRd d d1 k1 ∧ k1 ≤ 5 ∧
      d1.nreg 217094 = d.nmem p ∧ d1.nreg 217095 = d.nmem (p + 1) ∧
      d1.nreg 217096 = d.nmem (p + 2) ∧
      (∀ r, r ≠ 217094 → r ≠ 217095 → r ≠ 217096 → r ≠ 217097 → d1.nreg r = d.nreg r) ∧
      d1.nmem = d.nmem ∧ d1.rreg = d.rreg ∧ d1.rmem = d.rmem ∧ d1.output = d.output := by
    unfold lookRd
    exec_block
    · config_simp; omega
    · config_simp; omega
    · refine ⟨by omega, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩ <;> config_simp
      · rw [h92]
      · rw [h92, h27]
      · rw [h92, h27, show p + 1 + 1 = p + 2 by omega]
      · simp only [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2,
          Machine.upd_other _ _ _ h3, Machine.upd_other _ _ _ h4]
  have hw1 := e1.wb_right
  -- the item
  obtain ⟨d2, k2, e2, hk2, a93, hkeep, henc, f2⟩ : ∃ d2 k2,
      Exec P W (.ifLtN 217094 217027 lookRun lookPt) d1 d2 k2 ∧ k2 ≤ 16 ∧
      d2.nreg 217093 = cum + (it.pts n).length ∧
      (d.nreg 217090 < cum → d2.nreg 217070 = d.nreg 217070 ∧ d2.nreg 217071 = d.nreg 217071 ∧
        d2.nreg 217072 = d.nreg 217072) ∧
      (cum ≤ d.nreg 217090 → d.nreg 217090 < cum + (it.pts n).length →
        Enc d2 ((it.pts n).getD (d.nreg 217090 - cum) (.vtx 0))) ∧ FrameB Bitem d1 d2 := by
    have b20 : d1.nreg 217020 = n := by rw [f1 _ (by decide) (by decide) (by decide) (by decide), h20]
    have b27 : d1.nreg 217027 = 1 := by
      rw [f1 _ (by decide) (by decide) (by decide) (by decide), h27]
    have b93 : d1.nreg 217093 = cum := by
      rw [f1 _ (by decide) (by decide) (by decide) (by decide), h93]
    have b90 : d1.nreg 217090 = d.nreg 217090 := f1 _ (by decide) (by decide) (by decide) (by decide)
    have b70 : d1.nreg 217070 = d.nreg 217070 := f1 _ (by decide) (by decide) (by decide) (by decide)
    have b71 : d1.nreg 217071 = d.nreg 217071 := f1 _ (by decide) (by decide) (by decide) (by decide)
    have b72 : d1.nreg 217072 = d.nreg 217072 := f1 _ (by decide) (by decide) (by decide) (by decide)
    rcases it with ⟨a, ℓ⟩ | ⟨j | ⟨e, h⟩⟩
    · obtain ⟨i0, i1, i2⟩ := hit
      obtain ⟨ha, hℓ⟩ := hwf
      rw [run_pts_length] at hcW ⊢
      obtain ⟨d2, k2, e2, hk2, r93, r1, r2, rf⟩ := lookRun_exec (P := P) d1 hw1 b20 b27 b93
        (by rw [a95, i1]) (by rw [a96, i2]) ha hℓ hnW (by omega)
      refine ⟨d2, k2 + 1, .ifLtN_true (by rw [a94, i0, b27]; omega) e2, by omega, r93,
        fun h => ?_, fun h h' => ?_, rf⟩
      · obtain ⟨x, y, z⟩ := r1 (by rw [b90]; exact h)
        exact ⟨x.trans b70, y.trans b71, z.trans b72⟩
      · rw [run_pts_getD n a ℓ (by omega)]
        have := r2 (by rw [b90]; exact h) (by rw [b90]; omega)
        rwa [b90] at this
    · obtain ⟨i0, i1⟩ := hit
      obtain ⟨d2, k2, e2, hk2, r93, r1, r2, rf⟩ := lookPt_exec (P := P) d1 hw1 b27 b93
        (by simp [HostItem.pts] at hcW; omega)
      refine ⟨d2, k2 + 2, .ifLtN_false (by rw [a94, i0, b27]; omega) e2, by omega,
        by rw [r93]; simp [HostItem.pts], fun h => ?_, fun h h' => ?_, rf⟩
      · obtain ⟨x, y, z⟩ := r1 (by rw [b90]; omega)
        exact ⟨x.trans b70, y.trans b71, z.trans b72⟩
      · simp only [HostItem.pts, List.length_singleton] at h'
        have hk : d.nreg 217090 = cum := by omega
        obtain ⟨x, y, -⟩ := r2 (by rw [b90]; exact hk)
        rw [hk, Nat.sub_self]
        simp only [HostItem.pts, List.getD_cons_zero, Enc]
        exact ⟨by rw [x, a94, i0], by rw [y, a95, i1]⟩
    · obtain ⟨i0, i1, i2⟩ := hit
      obtain ⟨d2, k2, e2, hk2, r93, r1, r2, rf⟩ := lookPt_exec (P := P) d1 hw1 b27 b93
        (by simp [HostItem.pts] at hcW; omega)
      refine ⟨d2, k2 + 2, .ifLtN_false (by rw [a94, i0, b27]; omega) e2, by omega,
        by rw [r93]; simp [HostItem.pts], fun h => ?_, fun h h' => ?_, rf⟩
      · obtain ⟨x, y, z⟩ := r1 (by rw [b90]; omega)
        exact ⟨x.trans b70, y.trans b71, z.trans b72⟩
      · simp only [HostItem.pts, List.length_singleton] at h'
        have hk : d.nreg 217090 = cum := by omega
        obtain ⟨x, y, z⟩ := r2 (by rw [b90]; exact hk)
        rw [hk, Nat.sub_self]
        simp only [HostItem.pts, List.getD_cons_zero, Enc]
        exact ⟨by rw [x, a94, i0], by rw [y, a95, i1], by rw [z, a96, i2]⟩
  have hw2 := e2.wb_right
  -- advance
  have c91 : d2.nreg 217091 = d.nreg 217091 := by
    rw [f2.1 _ (by decide), f1 _ (by decide) (by decide) (by decide) (by decide)]
  have c92 : d2.nreg 217092 = p := by
    rw [f2.1 _ (by decide), f1 _ (by decide) (by decide) (by decide) (by decide), h92]
  have c27 : d2.nreg 217027 = 1 := by
    rw [f2.1 _ (by decide), f1 _ (by decide) (by decide) (by decide) (by decide), h27]
  obtain ⟨d3, k3, e3, hk3, a91, a92, f3⟩ : ∃ d3 k3, Exec P W lookNx d2 d3 k3 ∧ k3 ≤ 4 ∧
      d3.nreg 217091 = d.nreg 217091 + 1 ∧ d3.nreg 217092 = p + 3 ∧
      (∀ r, r ≠ 217091 → r ≠ 217092 → d3.nreg r = d2.nreg r) := by
    unfold lookNx
    exec_block
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · refine ⟨by omega, ?_, ?_, fun r h1 h2 => ?_⟩ <;> config_simp
      · omega
      · omega
      · simp only [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]
  have wr3 : wr Blook lookNx = true := by decide
  have wr1 : wr Blook lookRd = true := by decide
  have wr2 : wr Blook (.ifLtN 217094 217027 lookRun lookPt) = true := by decide
  refine ⟨d3, k1 + (k2 + k3), .seq e1 (.seq e2 e3), by omega, a91, a92, ?_, fun h => ?_,
    fun h h' => ?_, (exec_frameB e1 wr1).trans ((exec_frameB e2 wr2).trans (exec_frameB e3 wr3))⟩
  · rw [f3 _ (by decide) (by decide), a93]
  · obtain ⟨x, y, z⟩ := hkeep h
    exact ⟨(f3 _ (by decide) (by decide)).trans x, (f3 _ (by decide) (by decide)).trans y,
      (f3 _ (by decide) (by decide)).trans z⟩
  · exact (henc h h').congr (f3 _ (by decide) (by decide)) (f3 _ (by decide) (by decide))
      (f3 _ (by decide) (by decide))

set_option maxHeartbeats 2000000 in
/-- **`lookS`: host point `k = 217090`** of a well-formed host of at most `64` items. -/
theorem lookS_exec (d : Config) (hw : WordsBounded W d) {n HB : ℕ} {H : Host}
    (hH : HostAt d.nmem HB H) (hwf : HostWF n H) (hlen : H.length ≤ 64)
    (hHB : HB + 3 * H.length + 1 ≤ W) (hpW : 64 * n ≤ W) (hnW : 2 * n ≤ W)
    (h20 : d.nreg 217020 = n) (h27 : d.nreg 217027 = 1) (h34 : d.nreg 217034 = H.length)
    (h35 : d.nreg 217035 = HB + 1) :
    ∃ d' k, Exec P W lookS d d' k ∧ k ≤ 2100 ∧
      (d.nreg 217090 < (H.pts n).length → Enc d' (hpt n H (d.nreg 217090))) ∧
      FrameB Blook d d' := by
  have hptsW : (H.pts n).length ≤ 64 * n :=
    (Host.pts_length_le hwf).trans (Nat.mul_le_mul_right _ hlen)
  -- initialisation
  obtain ⟨d0, k0, e0, hk0, a91, a92, a93, f0⟩ : ∃ d0 k0, Exec P W (block [.constN 217091 0,
      .copyN 217092 217035, .constN 217093 0]) d d0 k0 ∧ k0 ≤ 3 ∧
      d0.nreg 217091 = 0 ∧ d0.nreg 217092 = HB + 1 ∧ d0.nreg 217093 = 0 ∧ FrameB Blook d d0 := by
    obtain ⟨d0, k0, e0, hk0, a91, a92, a93⟩ : ∃ d0 k0, Exec P W (block [.constN 217091 0,
        .copyN 217092 217035, .constN 217093 0]) d d0 k0 ∧ k0 ≤ 3 ∧
        d0.nreg 217091 = 0 ∧ d0.nreg 217092 = HB + 1 ∧ d0.nreg 217093 = 0 := by
      exec_block
      · omega
      · omega
      · refine ⟨by omega, ?_, ?_, ?_⟩ <;> config_simp
        exact h35
    exact ⟨d0, k0, e0, hk0, a91, a92, a93, exec_frameB e0 (by decide)⟩
  -- the loop
  set k := d.nreg 217090 with hkdef
  let Inv : ℕ → Config → Prop := fun j c => WordsBounded W c ∧ c.nreg 217091 = j ∧
    c.nreg 217034 = H.length ∧ c.nreg 217092 = HB + 1 + 3 * j ∧
    c.nreg 217093 = (Host.pts n (H.take j)).length ∧
    (k < (Host.pts n (H.take j)).length → Enc c (hpt n H k)) ∧ FrameB Blook d c
  have hI0 : Inv 0 d0 := ⟨e0.wb_right, a91, by rw [f0.1 _ (by decide), h34], by rw [a92],
    by rw [a93]; simp [Host.pts], fun h => by simp [Host.pts] at h, f0⟩
  obtain ⟨d', k', e', ⟨-, -, -, -, -, henc, f'⟩, hk'⟩ := DrvR.forLoop (P := P) (W := W) (ir := 217091)
    (nr := 217034) (body := lookBody) Inv 30 H.length
    (fun j c hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩)
    (fun j c hj hc => by
      obtain ⟨hwc, c91, c34, c92, c93, cenc, cf⟩ := hc
      have hlen' : (Host.pts n (H.take (j + 1))).length ≤ (H.pts n).length := by
        have := List.take_append_drop (j + 1) H
        conv_rhs => rw [← this]
        unfold Host.pts; rw [List.flatMap_append, List.length_append]; omega
      rw [pts_take_succ hj, List.length_append] at hlen'
      obtain ⟨c', kb, eb, hkb, b91, b92, b93, bkeep, benc, bf⟩ := lookBody_exec (P := P) c hwc
        (n := n) (p := HB + 1 + 3 * j) (cum := (Host.pts n (H.take j)).length)
        (it := H.getD j (.run 0 0)) (by rw [cf.1 _ (by decide), h20])
        (by rw [cf.1 _ (by decide), h27]) c92 c93
        (by rw [cf.2.2.1]; exact itemAt_of_hostAt hH hj) (itemWF_of_hostWF hwf hj)
        (by omega) (by omega) (by rw [c91]; omega) hnW
      have c90 : c.nreg 217090 = k := cf.1 _ (by decide)
      refine ⟨c', kb, eb, ⟨eb.wb_right, by rw [b91, c91], by rw [bf.1 _ (by decide), c34],
        by rw [b92]; ring, by rw [b93, pts_take_succ hj, List.length_append], fun hk => ?_,
        cf.trans bf⟩, hkb⟩
      rw [c90] at bkeep benc
      by_cases hk0 : k < (Host.pts n (H.take j)).length
      · obtain ⟨x, y, z⟩ := bkeep hk0
        exact (cenc hk0).congr x y z
      · rw [pts_take_succ hj, List.length_append] at hk
        have := benc (by omega) (by omega)
        rw [hpt_take (n := n) (H := H) (j := j + 1) (k := k)
            (by rw [pts_take_succ hj, List.length_append]; omega),
          pts_take_succ hj, List.getD_append_right _ _ _ _ (by omega)]
        exact this)
    hI0 (Nat.zero_le _)
  refine ⟨d', k0 + k', .seq e0 e', by omega, fun hk => ?_, f'⟩
  rw [List.take_of_length_le (le_refl _)] at henc
  exact henc hk

end look

end

end DrvX

end Chazelle.Core
