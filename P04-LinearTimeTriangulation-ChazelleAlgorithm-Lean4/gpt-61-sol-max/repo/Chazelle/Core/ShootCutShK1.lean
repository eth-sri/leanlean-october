module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShootCutShQO

/-!
# WP-G, part 51: the walk position of the hit of a query (`k1OutR`) and the environment across
a query

* `ShEnv.of_agree`: the shooting environment survives a step that keeps its registers and the
  memory below the allocator and does not lower it (a Lemma 3.6 query);
* `k1OutR`: `k1Out` on the RAM, into `140225`, `140226`.
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim

@[expose] public section

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

/-! ## The environment across a query -/

/-- **The environment survives** a step keeping its registers (but the allocator), the memory
below the allocator, and not lowering the allocator. -/
theorem ShEnv.of_agree {c c' : Config} (E : ShEnv P W H C z σ c)
    (hr : ∀ r, envR r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    ShEnv P W H C z σ c' := by
  have e403 : c'.nreg 140403 = c.nreg 140403 := hr _ (Or.inl rfl) (by omega_nf)
  obtain ⟨hB5, hwf⟩ := E.hwf
  obtain ⟨hlen, hHwf, hHA, hs⟩ := hwf H C E.hD
  have hD' : ChainDescAt c'.nmem (c.nreg 140403) (Qof P) H C :=
    chainDesc_agree' E.hD hB5 hHA hm
  have hB' : c'.nmem (c.nreg 140403) = c.nmem (c.nreg 140403) := hm _ (by omega)
  -- a host read in the new memory is the host
  have hback : ∀ H' C', ChainDescAt c'.nmem (c.nreg 140403) (Qof P) H' C' →
      ChainDescAt c.nmem (c.nreg 140403) (Qof P) H' C' := fun H' C' h' => by
    have hlen' : H'.length = H.length := by
      have a1 := h'.1.1
      have a2 := E.hD.1.1
      grind
    exact chainDesc_agree' h' hB5 (by omega) (fun a ha => (hm a ha).symm)
  refine ⟨E.hG, E.hW, by ram_simp, ⟨by omega, fun H' C' h' => ?_⟩,
    fun H' h' => ?_, by ram_grind, ?_, ?_, ?_,
    E.hσ⟩
  · grind
  · rw [e403, hB'] at h'
    have hlen' : H'.length = H.length := by
      have a1 := h'.1
      have a2 := E.hD.1.1
      grind
    exact E.hreg H' (hostAt_agree' h' (by omega) (fun a ha => (hm a ha).symm))
  · exact E.ox.copy (hr _ (by omega_nf) (by decide)) (hr _ (by omega_nf)
      (by decide)) (hr _ (by omega_nf) (by decide)) (hr _ (by omega_nf)
      (by decide))
  · exact E.oy.copy (hr _ (by omega_nf) (by decide)) (hr _ (by omega_nf)
      (by decide)) (hr _ (by omega_nf) (by decide))
  · ram_grind

/-! ## The walk position of the hit on the RAM -/

/-- `if a = b then T else E`. -/
def ifEq (a b : ℕ) (T E : Stmt) : Stmt := .ifLtN a b E (.ifLtN b a E T)

/-- Write the walk position `(e, h)` given by two instructions. -/
def wpos (i₁ i₂ : Instr) : Stmt := block [i₁, i₂]

/-- **`k1Out` on the RAM**: inputs `p₀ = 140250`, `x₀ = 140256`, `dir = 140257`, `w = 140258`,
`e' = 120006`, `h = 140236`; output `140225`, `140226`. -/
def k1OutR : Stmt :=
  .seq (.instr (.addN 140351 140256 140258))
    (.ifLtN 120006 140256
      (.ifLtN 140257 K1
        (ifEq 140236 140256 (wpos (.addN 140225 140250 140258) (.constN 140226 0))
          (wpos (.copyN 140225 140250) (.constN 140226 0)))
        (ifEq 140236 140256 (wpos (.copyN 140225 140250) (.constN 140226 0))
          (wpos (.addN 140225 140250 140258) (.constN 140226 0))))
      (.ifLtN 120006 140351
        (.seq (.instr (.subN 140352 120006 140256))
          (.ifLtN 140257 K1
            (.seq (block [.subN 140353 140258 K1, .subN 140353 140353 140352,
                .addN 140353 140250 140353])
              (ifEq 140236 120006 (wpos (.addN 140225 140353 K1) (.constN 140226 0))
                (wpos (.copyN 140225 140353) (.addN 140226 140236 K1))))
            (.seq (block [.addN 140353 140250 140352, .addN 140354 120006 K1])
              (ifEq 140236 140354 (wpos (.addN 140225 140353 K1) (.constN 140226 0))
                (wpos (.copyN 140225 140353) (.addN 140226 140236 K1))))))
        (.ifLtN 140257 K1
          (ifEq 140236 140256 (wpos (.addN 140225 140250 140258) (.constN 140226 0))
            (wpos (.copyN 140225 140250) (.constN 140226 0)))
          (ifEq 140236 140256 (wpos (.copyN 140225 140250) (.constN 140226 0))
            (wpos (.addN 140225 140250 140258) (.constN 140226 0))))))

/-- The registers written by `k1OutR`. -/
def Bko (r : ℕ) : Bool := r == 140225 || r == 140226 || decide (140351 ≤ r ∧ r < 140355)

theorem wr_k1OutR : wr Bko k1OutR = true := by decide

theorem ifEq_exec {a b : ℕ} {T E : Stmt} (c : Config) {K : ℕ} {R : Config → Prop}
    (hT : c.nreg a = c.nreg b → ∃ c' k, Exec P W T c c' k ∧ k ≤ K ∧ R c')
    (hE : c.nreg a ≠ c.nreg b → ∃ c' k, Exec P W E c c' k ∧ k ≤ K ∧ R c') :
    ∃ c' k, Exec P W (ifEq a b T E) c c' k ∧ k ≤ K + 4 ∧ R c' := by
  unfold ifEq
  by_cases h1 : c.nreg a < c.nreg b
  · obtain ⟨c', k, ex, hk, q⟩ := hE (by omega)
    exact ⟨c', _, .ifLtN_true h1 ex, by omega, q⟩
  by_cases h2 : c.nreg b < c.nreg a
  · obtain ⟨c', k, ex, hk, q⟩ := hE (by omega)
    exact ⟨c', _, .ifLtN_false h1 (.ifLtN_true h2 ex), by omega, q⟩
  · obtain ⟨c', k, ex, hk, q⟩ := hT (by omega)
    exact ⟨c', _, .ifLtN_false h1 (.ifLtN_false h2 ex), by omega, q⟩

theorem wpos_exec {i₁ i₂ : Instr} {c c₁ c₂ : Config} (e₁ : Exec P W (.instr i₁) c c₁ 1)
    (e₂ : Exec P W (.instr i₂) c₁ c₂ 1) : Exec P W (wpos i₁ i₂) c c₂ 2 :=
  Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_nil e₂.wb_right))

theorem k1OutR_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1)
    {p₀ x0 w dir e' h : ℕ} (h50 : c.nreg 140250 = p₀) (h56 : c.nreg 140256 = x0)
    (h57 : c.nreg 140257 = dir) (h58 : c.nreg 140258 = w) (h06 : c.nreg 120006 = e')
    (h36 : c.nreg 140236 = h) (hdir : dir = 1 ∨ dir = 0) (hW1 : p₀ + w + 1 ≤ W)
    (hW2 : x0 + w ≤ W) (hW3 : e' + 1 ≤ W) (hW4 : h + 1 ≤ W) :
    ∃ c' k, Exec P W k1OutR c c' k ∧ k ≤ 30 ∧ c'.nreg 140225 = (k1Out p₀ x0 w dir e' h).edge ∧
      c'.nreg 140226 = (k1Out p₀ x0 w dir e' h).hgt ∧ FrameB Bko c c' := by
  suffices key : ∃ c' k, Exec P W k1OutR c c' k ∧ k ≤ 30 ∧
      c'.nreg 140225 = (k1Out p₀ x0 w dir e' h).edge ∧
      c'.nreg 140226 = (k1Out p₀ x0 w dir e' h).hgt by
    obtain ⟨c', k, ex, hk, a, b⟩ := key
    exact ⟨c', k, ex, hk, a, b, exec_frameB ex wr_k1OutR⟩
  have e₀ := Exec.addN (P := P) hw 140351 140256 140258 (by omega)
  set c₁ : Config := { c with nreg := upd c.nreg 140351 (c.nreg 140256 + c.nreg 140258) } with hc₁
  have w₁ := e₀.wb_right
  have g₁ : ∀ r, r ≠ 140351 → c₁.nreg r = c.nreg r := fun r hr => by ram_simp
  have q51 : c₁.nreg 140351 = x0 + w := by ram_simp
  have q50 := (g₁ 140250 (by decide)).trans h50
  have q56 := (g₁ 140256 (by decide)).trans h56
  have q57 := (g₁ 140257 (by decide)).trans h57
  have q58 := (g₁ 140258 (by decide)).trans h58
  have q06 := (g₁ 120006 (by decide)).trans h06
  have q36 := (g₁ 140236 (by decide)).trans h36
  have qK := (g₁ K1 (by decide)).trans h1
  -- the leaves: a vertex position `(p₀, 0)` or `(p₀ + w, 0)`
  have vP : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 140250 = p₀ →
      ∃ c' k, Exec P W (wpos (.copyN 140225 140250) (.constN 140226 0)) c₂ c' k ∧ k ≤ 2 ∧
        c'.nreg 140225 = p₀ ∧ c'.nreg 140226 = 0 := fun c₂ hw₂ g50 => by
    have ea := Exec.copyN (P := P) hw₂ 140225 140250
    have eb := Exec.constN (P := P) ea.wb_right 140226 0 (Nat.zero_le _)
    exact ⟨_, _, wpos_exec ea eb, le_rfl, by simp [g50], by simp⟩
  have vW : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 140250 = p₀ → c₂.nreg 140258 = w →
      ∃ c' k, Exec P W (wpos (.addN 140225 140250 140258) (.constN 140226 0)) c₂ c' k ∧ k ≤ 2 ∧
        c'.nreg 140225 = p₀ + w ∧ c'.nreg 140226 = 0 := fun c₂ hw₂ g50 g58 => by
    have ea := Exec.addN (P := P) hw₂ 140225 140250 140258 (by omega)
    have eb := Exec.constN (P := P) ea.wb_right 140226 0 (Nat.zero_le _)
    exact ⟨_, _, wpos_exec ea eb, le_rfl, by ram_simp, by simp⟩
  -- the outside cases
  have outside : ¬ (x0 ≤ e' ∧ e' < x0 + w) → ∃ c' k, Exec P W (.ifLtN 140257 K1
      (ifEq 140236 140256 (wpos (.addN 140225 140250 140258) (.constN 140226 0))
        (wpos (.copyN 140225 140250) (.constN 140226 0)))
      (ifEq 140236 140256 (wpos (.copyN 140225 140250) (.constN 140226 0))
        (wpos (.addN 140225 140250 140258) (.constN 140226 0)))) c₁ c' k ∧ k ≤ 8 ∧
      c'.nreg 140225 = (k1Out p₀ x0 w dir e' h).edge ∧
      c'.nreg 140226 = (k1Out p₀ x0 w dir e' h).hgt := fun hout => by
    unfold k1Out
    rw [ite_eq_right hout]
    rcases hdir with rfl | rfl
    · rw [ite_eq_left rfl]
      obtain ⟨c', k, ex, hk, v1, v2⟩ := ifEq_exec (P := P) (W := W) (a := 140236) (b := 140256)
        (T := wpos (.copyN 140225 140250) (.constN 140226 0))
        (E := wpos (.addN 140225 140250 140258) (.constN 140226 0)) c₁ (K := 2)
        (R := fun c' => c'.nreg 140225 = (if h = x0 then (⟨p₀, 0⟩ : WPos) else ⟨p₀ + w, 0⟩).edge ∧
          c'.nreg 140226 = (if h = x0 then (⟨p₀, 0⟩ : WPos) else ⟨p₀ + w, 0⟩).hgt)
        (fun he => by
          grind)
        (fun he => by
          grind)
      exact ⟨c', _, .ifLtN_false (by omega) ex, by omega, v1, v2⟩
    · rw [ite_eq_right (by norm_num : ¬ (0 = 1))]
      obtain ⟨c', k, ex, hk, v1, v2⟩ := ifEq_exec (P := P) (W := W) (a := 140236) (b := 140256)
        (T := wpos (.addN 140225 140250 140258) (.constN 140226 0))
        (E := wpos (.copyN 140225 140250) (.constN 140226 0)) c₁ (K := 2)
        (R := fun c' => c'.nreg 140225 = (if h = x0 then (⟨p₀ + w, 0⟩ : WPos) else ⟨p₀, 0⟩).edge ∧
          c'.nreg 140226 = (if h = x0 then (⟨p₀ + w, 0⟩ : WPos) else ⟨p₀, 0⟩).hgt)
        (fun he => by
          grind)
        (fun he => by
          grind)
      exact ⟨c', _, .ifLtN_true (by omega) ex, by omega, v1, v2⟩
  unfold k1OutR
  by_cases t1 : c₁.nreg 120006 < c₁.nreg 140256
  · obtain ⟨c', k, ex, hk, v1, v2⟩ := outside (by omega)
    exact ⟨c', _, .seq e₀ (.ifLtN_true t1 ex), by omega, v1, v2⟩
  by_cases t2 : c₁.nreg 120006 < c₁.nreg 140351
  swap
  · obtain ⟨c', k, ex, hk, v1, v2⟩ := outside (by omega)
    exact ⟨c', _, .seq e₀ (.ifLtN_false t1 (.ifLtN_false t2 ex)), by omega, v1, v2⟩
  -- inside the block
  have hin : x0 ≤ e' ∧ e' < x0 + w := by omega
  have e₁ := Exec.subN (P := P) w₁ 140352 120006 140256
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 140352 (c₁.nreg 120006 - c₁.nreg 140256) }
    with hc₂
  have w₂ := e₁.wb_right
  have g₂ : ∀ r, r ≠ 140352 → c₂.nreg r = c₁.nreg r := fun r hr => by rw [hc₂]; simp [hr]
  have q52 : c₂.nreg 140352 = e' - x0 := by rw [hc₂]; simp [q06, q56]
  have r50 := (g₂ 140250 (by decide)).trans q50
  have r57 := (g₂ 140257 (by decide)).trans q57
  have r58 := (g₂ 140258 (by decide)).trans q58
  have r06 := (g₂ 120006 (by decide)).trans q06
  have r36 := (g₂ 140236 (by decide)).trans q36
  have rK := (g₂ K1 (by decide)).trans qK
  unfold k1Out
  rw [ite_eq_left hin]
  rcases hdir with rfl | rfl
  · -- upward
    rw [ite_eq_left rfl]
    obtain ⟨c₃, k₃, e₃, hk₃, s53, s54, g₃⟩ : ∃ c₃ k₃, Exec P W (block [.addN 140353 140250 140352,
        .addN 140354 120006 K1]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ c₃.nreg 140353 = p₀ + (e' - x0) ∧
        c₃.nreg 140354 = e' + 1 ∧ ∀ r, r ≠ 140353 → r ≠ 140354 → c₃.nreg r = c₂.nreg r := by
      have ea := Exec.addN (P := P) w₂ 140353 140250 140352 (by omega)
      have eb := Exec.addN (P := P) ea.wb_right 140354 120006 K1 (by
        simp [K1]; grind [K1])
      refine ⟨_, _, Exec.block_cons ea (Exec.block_cons eb (Exec.block_nil eb.wb_right)), rfl,
        by simp [K1]; omega, by simp [K1]; grind [K1], fun r h1 h2 => by
          simp [h1, h2]⟩
    have w₃ := e₃.wb_right
    have s36 : c₃.nreg 140236 = h := by grind
    have sK : c₃.nreg K1 = 1 := by rw [g₃ _ (by decide) (by decide), rK]
    obtain ⟨c', k, ex, hk, v1, v2⟩ := ifEq_exec (P := P) (W := W) (a := 140236) (b := 140354)
      (T := wpos (.addN 140225 140353 K1) (.constN 140226 0))
      (E := wpos (.copyN 140225 140353) (.addN 140226 140236 K1)) c₃ (K := 2)
      (R := fun c' => c'.nreg 140225 = (if h = e' + 1 then (⟨p₀ + (e' - x0) + 1, 0⟩ : WPos)
          else ⟨p₀ + (e' - x0), h + 1⟩).edge ∧
        c'.nreg 140226 = (if h = e' + 1 then (⟨p₀ + (e' - x0) + 1, 0⟩ : WPos)
          else ⟨p₀ + (e' - x0), h + 1⟩).hgt)
      (fun he => by
        rw [s36, s54] at he
        have ea' := Exec.addN (P := P) w₃ 140225 140353 K1 (by grind)
        have eb' := Exec.constN (P := P) ea'.wb_right 140226 0 (Nat.zero_le _)
        exact ⟨_, _, wpos_exec ea' eb', le_rfl, by rw [ite_eq_left he]; simp [s53, K1]; exact sK,
          by rw [ite_eq_left he]; simp⟩)
      (fun he => by
        rw [s36, s54] at he
        have ea' := Exec.copyN (P := P) w₃ 140225 140353
        have eb' := Exec.addN (P := P) ea'.wb_right 140226 140236 K1
          (by simp [K1]; grind [K1])
        exact ⟨_, _, wpos_exec ea' eb', le_rfl, by rw [ite_eq_right he]; simp [s53],
          by rw [ite_eq_right he]; simp [K1]; grind [K1]⟩)
    exact ⟨c', _, .seq e₀ (.ifLtN_false t1 (.ifLtN_true t2 (.seq e₁ (.ifLtN_false
      (by omega) (.seq e₃ ex))))), by omega, v1, v2⟩
  · -- downward
    rw [ite_eq_right (by norm_num : ¬ (0 = 1))]
    obtain ⟨c₃, k₃, e₃, hk₃, s53, g₃⟩ : ∃ c₃ k₃, Exec P W (block [.subN 140353 140258 K1,
        .subN 140353 140353 140352, .addN 140353 140250 140353]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
        c₃.nreg 140353 = p₀ + (w - 1 - (e' - x0)) ∧
        ∀ r, r ≠ 140353 → c₃.nreg r = c₂.nreg r := by
      have ea := Exec.subN (P := P) w₂ 140353 140258 K1
      have eb := Exec.subN (P := P) ea.wb_right 140353 140353 140352
      have ec := Exec.addN (P := P) eb.wb_right 140353 140250 140353 (by
        simp [K1]; omega)
      refine ⟨_, _, Exec.block_cons ea (Exec.block_cons eb (Exec.block_cons ec
        (Exec.block_nil ec.wb_right))), rfl, ?_, fun r hr => by simp [hr]⟩
      simp [K1]; grind [K1]
    have w₃ := e₃.wb_right
    have s36 : c₃.nreg 140236 = h := by grind
    have s06 : c₃.nreg 120006 = e' := by grind
    have sK : c₃.nreg K1 = 1 := by ram_grind
    obtain ⟨c', k, ex, hk, v1, v2⟩ := ifEq_exec (P := P) (W := W) (a := 140236) (b := 120006)
      (T := wpos (.addN 140225 140353 K1) (.constN 140226 0))
      (E := wpos (.copyN 140225 140353) (.addN 140226 140236 K1)) c₃ (K := 2)
      (R := fun c' => c'.nreg 140225 = (if h = e' then (⟨p₀ + (w - 1 - (e' - x0)) + 1, 0⟩ : WPos)
          else ⟨p₀ + (w - 1 - (e' - x0)), h + 1⟩).edge ∧
        c'.nreg 140226 = (if h = e' then (⟨p₀ + (w - 1 - (e' - x0)) + 1, 0⟩ : WPos)
          else ⟨p₀ + (w - 1 - (e' - x0)), h + 1⟩).hgt)
      (fun he => by
        rw [s36, s06] at he
        have ea' := Exec.addN (P := P) w₃ 140225 140353 K1 (by omega)
        have eb' := Exec.constN (P := P) ea'.wb_right 140226 0 (Nat.zero_le _)
        exact ⟨_, _, wpos_exec ea' eb', le_rfl, by rw [ite_eq_left he]; simp [s53, K1]; exact sK,
          by rw [ite_eq_left he]; simp⟩)
      (fun he => by
        rw [s36, s06] at he
        have ea' := Exec.copyN (P := P) w₃ 140225 140353
        have eb' := Exec.addN (P := P) ea'.wb_right 140226 140236 K1
          (by simp [K1]; grind [K1])
        exact ⟨_, _, wpos_exec ea' eb', le_rfl, by rw [ite_eq_right he]; simp [s53],
          by rw [ite_eq_right he]; simp [K1]; grind [K1]⟩)
    exact ⟨c', _, .seq e₀ (.ifLtN_false t1 (.ifLtN_true t2 (.seq e₁ (.ifLtN_true
      (by omega) (.seq e₃ ex))))), by omega, v1, v2⟩

end

end ShootCut

end Chazelle.Core
