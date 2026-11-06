module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.GranRamRm3

/-!
# WP-F, RAM part 9: the worklist loop

`bodyStmt` executes one step `St.step` of the worklist (`body_exec`); `loopStmt` runs it while
the worklist is not empty (`loop_exec`), ending in a machine state of a state with the invariant
and an empty worklist.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## The step in cases -/

section Cases

variable {E : Env} {st : St}

theorem step_dead (h : st.live st.cur ≠ 1) : st.step E = st.pop := by
  grind [St.step]

theorem step_keep (h : st.live st.cur = 1)
    (hd : 3 ≤ st.deg (st.s0 st.cur) ∧ 3 ≤ st.deg (st.s1 st.cur)) : st.step E = st.pop := by
  simp_all [St.step] <;> omega_nf

section
variable (h : st.live st.cur = 1) (hd : ¬ (3 ≤ st.deg (st.s0 st.cur) ∧ 3 ≤ st.deg (st.s1 st.cur)))
include h hd
theorem step_heavy
    (hm : E.γ < st.mu E st.cur) : st.step E = st.pop := by
  simp_all [St.step] <;> omega_nf

theorem step_rm
    (hm : ¬ E.γ < st.mu E st.cur) : st.step E = st.remove st.cur (st.mu E st.cur) := by
  grind [St.step]


end

end Cases

/-- A machine state survives a statement changing only temporaries (`≥ 90060`) and no memory. -/
theorem MS.frameT {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {c c' : Config} {st : St}
    (h : MS W E d A₀ m₀ c st) (hw : WordsBounded W c')
    (hr : ∀ r, r < 90060 → c'.nreg r = c.nreg r) (hm : c'.nmem = c.nmem) :
    MS W E d A₀ m₀ c' st :=
  ⟨hw, h.cst.frame fun r hr' _ => hr r (by omega), by ram_grind,
    by ram_grind, by ram_grind,
    fun a ha => by ram_grind⟩

/-! ## The body -/

/-- Compute the merged weight; pop if it exceeds `γ`, else remove. -/
def tryStmt : Stmt := .seq muStmt (.ifLtN 90014 90078 popStmt rmStmt)

/-- **One step of the worklist.** -/
def bodyStmt : Stmt :=
  .seq frontStmt (.ifLtN 90063 90019 popStmt
    (.seq xyStmt (.seq ndStmt (.ifLtN 90066 90020 tryStmt (.ifLtN 90067 90020 tryStmt popStmt)))))

/-- The registers `muStmt` writes. -/
def Bmu (r : ℕ) : Bool := decide (r = 90061) || decide (90074 ≤ r ∧ r < 90100)

theorem wr_mu_fine : wr Bmu muStmt = true := by decide

/-- The registers `ndStmt` writes. -/
def Bnd (r : ℕ) : Bool := decide (r = 90061) || decide (90068 ≤ r ∧ r < 90074)

theorem wr_nd_fine : wr Bnd ndStmt = true := by decide

/-- The registers of the body. -/
def Bbody (r : ℕ) : Bool := decide (90060 ≤ r ∧ r < 90110) || decide (r = 90050) ||
  decide (r = 90051)

theorem wrS_body : wrS Bbody bodyStmt = true := by decide

section
variable {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {c : Config} {st : St} (hE : E.Good) (hM : MS W E d A₀ m₀ c st) (hI : Inv E st) (hD : DimOK E d W) (hA : A₀ ≤ d.b0)
include hE hM hI hD hA
theorem try_exec (hc : st.cur ∈ st.L E) (htop : 0 < st.top)
    (hlow : ¬ (3 ≤ st.deg (st.s0 st.cur) ∧ 3 ≤ st.deg (st.s1 st.cur)))
    (h62 : c.nreg 90062 = st.cur) (h64 : c.nreg 90064 = st.s0 st.cur)
    (h65 : c.nreg 90065 = st.s1 st.cur)
    (h66 : c.nreg 90066 = st.deg (st.s0 st.cur)) (h67 : c.nreg 90067 = st.deg (st.s1 st.cur))
    (h68 : c.nreg 90068 = st.nd0 st.cur) (h69 : c.nreg 90069 = st.nd1 st.cur)
    (h72 : c.nreg 90072 = bit (decide (st.cnt (st.nd0 st.cur) = 1)))
    (h73 : c.nreg 90073 = bit (decide (st.cnt (st.nd1 st.cur) = 1))) :
    ∃ c' k, Exec P W tryStmt c c' k ∧ k ≤ 60 * E.D + 330 ∧ MS W E d A₀ m₀ c' (st.step E) := by
  obtain ⟨c₁, k₁, e₁, hk₁, m78, -⟩ := mu_exec (P := P) hE hM.wb hM.cst hM.enc hI hD hc h64 h65
    h68 h69 h72 h73 hM.nlive
  have F₁ := exec_frameB e₁ wr_mu_fine
  have g : ∀ r, r < 90100 → r ≠ 90061 → (r < 90074) → c₁.nreg r = c.nreg r := fun r a1 a2 a3 =>
    F₁.1 r (by core_grind)
  have hM₁ : MS W E d A₀ m₀ c₁ st := hM.frameT e₁.wb_right (fun r hr => g r (by omega) (by omega)
    (by omega)) F₁.2.2.1
  by_cases hm : E.γ < st.mu E st.cur
  · obtain ⟨c₂, k₂, e₂, hk₂, hM₂, -, -⟩ := hM₁.pop (P := P)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rw [hM₁.cst.γ, m78]; exact hm) e₂), by omega, ?_⟩
    rw [step_heavy hc.2 hlow hm]; exact hM₂
  · have hlow' : st.deg (st.s0 st.cur) < 3 ∨ st.deg (st.s1 st.cur) < 3 := by omega
    have hI' := hI.step hE htop
    rw [step_rm hc.2 hlow hm] at hI' ⊢
    obtain ⟨c₂, k₂, e₂, hk₂, hM₂, -⟩ := rm_exec (P := P) (μ := st.mu E st.cur) hE hM₁ hI hD hA hc
      htop hlow' hI'
      (by simp_all)
      (by simp_all)
      (by simp_all)
      (by simp_all)
      (by simp_all)
      (by simp_all)
      (by simp_all)
      (by simp_all)
      (by simp_all) m78
    exact ⟨c₂, _, .seq e₁ (.ifLtN_false (by rw [hM₁.cst.γ, m78]; exact hm) e₂), by omega, hM₂⟩

/-- **One step of the worklist on the RAM.** -/
theorem body_exec (htop : 0 < st.top) :
    ∃ c' k, Exec P W bodyStmt c c' k ∧ k ≤ 60 * E.D + 400 ∧ MS W E d A₀ m₀ c' (st.step E) ∧
      FrameS Bbody c c' := by
  suffices hh : ∃ c' k, Exec P W bodyStmt c c' k ∧ k ≤ 60 * E.D + 400 ∧
      MS W E d A₀ m₀ c' (st.step E) by
    obtain ⟨c', k, e, h1, h2⟩ := hh
    exact ⟨c', k, e, h1, h2, exec_frameS e wrS_body⟩
  obtain ⟨c₁, k₁, e₁, hk₁, f62, f63, hcK, fr, fm⟩ := front_exec (P := P) hM hI hD htop
  have hM₁ : MS W E d A₀ m₀ c₁ st := hM.frameT e₁.wb_right (fun r hr => fr r (by omega)
    (by omega) (by omega) (by omega)) fm
  have hl01 := hI.live01 _ hcK
  by_cases hl : st.live st.cur = 1
  swap
  · obtain ⟨c₂, k₂, e₂, hk₂, hM₂, -, -⟩ := hM₁.pop (P := P)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rw [f63, hM₁.cst.one]; omega) e₂), by omega, ?_⟩
    rw [step_dead hl]; exact hM₂
  have hc : st.cur ∈ st.L E := ⟨hcK, hl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, x64, x65, x66, x67, xr, xm⟩ := xy_exec (P := P) hM₁.wb hM₁.cst
    hM₁.enc hI hD hc f62
  have hM₂ : MS W E d A₀ m₀ c₂ st := hM₁.frameT e₂.wb_right (fun r hr => xr r (by omega)
    (by omega) (by omega) (by omega) (by omega)) xm
  obtain ⟨c₃, k₃, e₃, hk₃, n68, n69, n72, n73, F₃⟩ := nd_exec (P := P) hM₂.wb hM₂.cst hM₂.enc hI hD
    hc (by ram_grind)
  have hM₃ : MS W E d A₀ m₀ c₃ st := hM₂.frameT e₃.wb_right (fun r hr => F₃.1 r (Bin_false
    (by omega))) F₃.2.2.1
  have F₃' := exec_frameB e₃ wr_nd_fine
  have g : ∀ r, 90061 < r → r < 90068 → c₃.nreg r = c₂.nreg r := fun r a1 a2 =>
    F₃'.1 r (by core_grind)
  have t62 : c₃.nreg 90062 = st.cur := by
    ram_grind
  have t64 : c₃.nreg 90064 = st.s0 st.cur := by ram_grind
  have t65 : c₃.nreg 90065 = st.s1 st.cur := by ram_grind
  have t66 : c₃.nreg 90066 = st.deg (st.s0 st.cur) := by ram_grind
  have t67 : c₃.nreg 90067 = st.deg (st.s1 st.cur) := by ram_grind
  have tryE := fun (hlow : ¬ (3 ≤ st.deg (st.s0 st.cur) ∧ 3 ≤ st.deg (st.s1 st.cur))) =>
    try_exec (P := P) hE hM₃ hI hD hA hc htop hlow t62 t64 t65 t66 t67 n68 n69 n72 n73
  have hnl : ¬ c₁.nreg 90063 < c₁.nreg 90019 := by rw [f63, hM₁.cst.one, hl]; omega
  by_cases h3X : 3 ≤ st.deg (st.s0 st.cur)
  · by_cases h3Y : 3 ≤ st.deg (st.s1 st.cur)
    · obtain ⟨c₄, k₄, e₄, hk₄, hM₄, -, -⟩ := hM₃.pop (P := P)
      refine ⟨c₄, _, .seq e₁ (.ifLtN_false hnl (.seq e₂ (.seq e₃ (.ifLtN_false
        (by rw [t66, hM₃.cst.three]; omega) (.ifLtN_false (by rw [t67, hM₃.cst.three]; omega)
          e₄))))), by omega, ?_⟩
      rw [step_keep hl ⟨h3X, h3Y⟩]; exact hM₄
    · obtain ⟨c₄, k₄, e₄, hk₄, hM₄⟩ := tryE (by omega)
      exact ⟨c₄, _, .seq e₁ (.ifLtN_false hnl (.seq e₂ (.seq e₃ (.ifLtN_false
        (by rw [t66, hM₃.cst.three]; omega) (.ifLtN_true (by rw [t67, hM₃.cst.three]; omega)
          e₄))))), by omega, hM₄⟩
  · obtain ⟨c₄, k₄, e₄, hk₄, hM₄⟩ := tryE (by omega)
    exact ⟨c₄, _, .seq e₁ (.ifLtN_false hnl (.seq e₂ (.seq e₃ (.ifLtN_true
      (by rw [t66, hM₃.cst.three]; omega) e₄)))), by omega, hM₄⟩

/-! ## The loop -/


end

/-- **The worklist loop** (`r52 = 0`). -/
def loopStmt : Stmt := .whileLtN 90052 90050 bodyStmt

theorem loop_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {c : Config}
    {st : St} (hE : E.Good) (hM : MS W E d A₀ m₀ c st) (hI : Inv E st) (hD : DimOK E d W)
    (hA : A₀ ≤ d.b0) (h52 : c.nreg 90052 = 0) :
    ∃ c' k st', Exec P W loopStmt c c' k ∧ k ≤ (60 * E.D + 402) * st.meas E + 2 ∧
      MS W E d A₀ m₀ c' st' ∧ Inv E st' ∧ st'.top = 0 ∧
      (∀ r, Bbody r = false → c'.nreg r = c.nreg r) := by
  obtain ⟨c', k, e, ⟨st', hM', hI', h52', hr'⟩, hx, hk⟩ := Exec.whileLtN_bounded (P := P)
    (a := 90052) (b := 90050) (body := bodyStmt)
    (fun c₁ => ∃ st₁, MS W E d A₀ m₀ c₁ st₁ ∧ Inv E st₁ ∧ c₁.nreg 90052 = 0 ∧
      (∀ r, Bbody r = false → c₁.nreg r = c.nreg r))
    (fun c₁ => c₁.nreg 90050 + (E.D + 1) * c₁.nreg 90051) (60 * E.D + 400)
    (fun _ ⟨_, h, _⟩ => h.wb)
    (fun c₁ ⟨st₁, hM₁, hI₁, h52₁, hr₁⟩ ht => by
      have htop : 0 < st₁.top := by rw [h52₁, hM₁.top] at ht; exact ht
      obtain ⟨c₂, k₂, e₂, hk₂, hM₂, F₂⟩ := body_exec (P := P) hE hM₁ hI₁ hD hA htop
      have hI₂ := hI₁.step hE htop
      have hms := measure_step hE hI₁ htop
      refine ⟨c₂, k₂, e₂, ⟨_, hM₂, hI₂, by ram_grind,
        fun r hr => by ram_grind⟩, hk₂, ?_⟩
      unfold St.meas at hms
      rw [hM₂.top, hM₂.nlive, hM₁.top, hM₁.nlive]
      exact hms) ⟨st, hM, hI, h52, fun _ _ => rfl⟩
  refine ⟨c', k, st', e, ?_, hM', hI', ?_, hr'⟩
  · rw [hM.top, hM.nlive] at hk
    omega_nf
  · rw [h52', hM'.top] at hx; omega

end

end Gran

end Chazelle.Core
