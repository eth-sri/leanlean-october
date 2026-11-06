module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShootCutCStep2

/-!
# WP-G, part 21: the path of the main loop

The main loop walks the walk vertices of a chain model (`n = 2m + 7` walk edges) forward, with
positions unwrapped to naturals `U` (the vertex is `U mod n`):

* `UPath n u ps u'`: the pieces `ps` go from the vertex of `u` to the vertex of `u'` with
  increasing unwrapped positions (`chained_upath`: a chained list of vertex pieces);
* `BrkU`: the unwrapped breakpoints (the top `2m + 6` and the breakpoints of the tour);
  `card_brkU_le`: at most `3 + 8 |H|` of them within one lap;
* `mu`: the potential of the loop, `2 · #(breakpoints in [U, F)) + [U < F, U not a
  breakpoint]`; `mu_lt`: it decreases at every step of the loop.
-/

namespace Chazelle.Core

@[expose] public section

namespace ShootCut

/-- The pieces `ps` go from the walk vertex of `u` to the one of `u'`, with increasing
unwrapped positions. -/
def UPath (n : ℕ) : ℕ → List Pc → ℕ → Prop
  | u, [], u' => u = u'
  | u, pc :: ps, u' => pc.s = ⟨u % n, 0⟩ ∧ ∃ u₁, u < u₁ ∧ pc.e = ⟨u₁ % n, 0⟩ ∧ UPath n u₁ ps u'

theorem UPath.append {n : ℕ} : ∀ {u : ℕ} {ps : List Pc} {v : ℕ}, UPath n u ps v →
    ∀ (qs : List Pc) {w : ℕ}, UPath n v qs w → UPath n u (ps ++ qs) w
  | _, [], _, h, _, _, hq => by simp_all [UPath] 
  | _, _ :: _, _, ⟨h1, u₁, h2, h3, h4⟩, qs, _, hq => ⟨h1, u₁, h2, h3, UPath.append h4 qs hq⟩

theorem mod_shift {n U c x : ℕ} (hU : U % n = c) (hcx : c ≤ x) (hx : x < n) :
    (U + (x - c)) % n = x := by
  have e := Nat.div_add_mod U n
  rw [hU] at e
  rw [show U + (x - c) = n * (U / n) + x by omega, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]

theorem chained_le : ∀ {ps : List Pc} {c c' : ℕ}, Chained ⟨c, 0⟩ ps ⟨c', 0⟩ →
    (∀ pc ∈ ps, pc.s.hgt = 0 ∧ pc.e.hgt = 0 ∧ pc.s.edge < pc.e.edge) → c ≤ c'
  | [], c, c', h, _ => by
    simp_all [Chained, WPos.mk.injEq, and_true] 
  | pc :: ps, c, c', ⟨h1, h2⟩, hv => by
    obtain ⟨-, he0, hlt⟩ := hv pc (by simp)
    have hpe : pc.e = ⟨pc.e.edge, 0⟩ := by rw [← he0]
    rw [hpe] at h2
    have := chained_le h2 (fun q hq => hv q (by simp [hq]))
    grind

/-- **A chained list of vertex pieces** without wrap is a path. -/
theorem chained_upath {n : ℕ} : ∀ {ps : List Pc} {c c' : ℕ}, Chained ⟨c, 0⟩ ps ⟨c', 0⟩ →
    (∀ pc ∈ ps, pc.s.hgt = 0 ∧ pc.e.hgt = 0 ∧ pc.s.edge < pc.e.edge) → c' < n →
    ∀ U, U % n = c → UPath n U ps (U + (c' - c))
  | [], c, c', h, _, _, U, _ => by
    simp_all [Chained, WPos.mk.injEq, and_true, UPath] 
  | pc :: ps, c, c', ⟨h1, h2⟩, hv, hc', U, hU => by
    obtain ⟨-, he0, hlt⟩ := hv pc (by simp)
    have hpe : pc.e = ⟨pc.e.edge, 0⟩ := by rw [← he0]
    rw [hpe] at h2
    have hv' : ∀ q ∈ ps, q.s.hgt = 0 ∧ q.e.hgt = 0 ∧ q.s.edge < q.e.edge :=
      fun q hq => hv q (by simp [hq])
    have hle := chained_le h2 hv'
    rw [h1] at hlt
    simp only at hlt
    have hm := mod_shift hU hlt.le (show pc.e.edge < n by omega)
    have hp := chained_upath h2 hv' hc' (U + (pc.e.edge - c)) hm
    refine ⟨by rw [h1, hU], U + (pc.e.edge - c), by omega, by rw [hpe, hm], ?_⟩
    grind

/-! ## Breakpoints and the potential -/

variable (C : Chain) (nQ : ℕ) (H : Host)

/-- A residue of the walk is a breakpoint: the top `2m + 6`, or a breakpoint of the tour. -/
def BrkRes (ρ : ℕ) : Prop :=
  ρ = 2 * C.m + 6 ∨ (6 ≤ ρ ∧ ρ < 2 * C.m + 6 ∧ Brk C nQ H (ρ - 6))

/-- An unwrapped breakpoint. -/
def BrkU (x : ℕ) : Prop := BrkRes C nQ H (x % (2 * C.m + 7))

noncomputable instance : DecidablePred (BrkU C nQ H) := Classical.decPred _

/-- **The potential** of the main loop at the unwrapped position `U` (final position `F`). -/
noncomputable def mu (F U : ℕ) : ℕ :=
  2 * ((Finset.Ico U F).filter (BrkU C nQ H)).card + if U < F ∧ ¬ BrkU C nQ H U then 1 else 0

variable {C nQ H}

theorem card_Ico_sub {U U' F : ℕ} (h : U ≤ U') :
    ((Finset.Ico U' F).filter (BrkU C nQ H)).card ≤
      ((Finset.Ico U F).filter (BrkU C nQ H)).card :=
  Finset.card_le_card fun x hx => by
    grind

theorem card_Ico_succ {U U' F : ℕ} (h : U < U') (hU : U < F) (hb : BrkU C nQ H U) :
    ((Finset.Ico U' F).filter (BrkU C nQ H)).card + 1 ≤
      ((Finset.Ico U F).filter (BrkU C nQ H)).card := by
  have hsub : insert U ((Finset.Ico U' F).filter (BrkU C nQ H)) ⊆
      (Finset.Ico U F).filter (BrkU C nQ H) := by
    grind
  
  have := Finset.card_le_card hsub
  simp_all

/-- **The potential decreases** along a step `U → U'` that starts or stops at a breakpoint or
stops at `F`. -/
theorem mu_lt {F U U' : ℕ} (h : U < U') (hF : U' ≤ F)
    (hb : BrkU C nQ H U ∨ U' = F ∨ BrkU C nQ H U') : mu C nQ H F U' < mu C nQ H F U := by
  have h1 := card_Ico_sub (C := C) (nQ := nQ) (H := H) (F := F) h.le
  rcases hb with hb | hb | hb
  · unfold mu
    have := card_Ico_succ (F := F) h (by omega) hb
    ram_grind
  · subst hb
    have hz : mu C nQ H U' U' = 0 := by unfold mu; simp
    rw [hz]
    unfold mu
    by_cases hU : BrkU C nQ H U
    · have := card_Ico_succ (F := U') h h hU
      omega
    simp_all
  · unfold mu
    by_cases hU : BrkU C nQ H U
    · have := card_Ico_succ (F := F) h (by omega) hU
      simp_all
    ram_grind

/-- The potential is at most `2 · #breakpoints + 1`. -/
theorem mu_le (F U : ℕ) :
    mu C nQ H F U ≤ 2 * ((Finset.Ico U F).filter (BrkU C nQ H)).card + 1 := by
  grind [mu]

/-- **Few breakpoints within one lap.** -/
theorem card_brkU_le (hn : 0 < nQ) (hwf : HostWF nQ H) {U F : ℕ}
    (hUF : F ≤ U + (2 * C.m + 7)) :
    ((Finset.Ico U F).filter (BrkU C nQ H)).card ≤ 3 + 8 * H.length := by
  classical
  have hinj : Set.InjOn (fun x => x % (2 * C.m + 7)) ((Finset.Ico U F).filter (BrkU C nQ H) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at hx hy
    simp only at hxy
    
    rcases Nat.lt_or_ge x y with h | h
    · exfalso
      have : (2 * C.m + 7) ∣ y - x := (Nat.modEq_iff_dvd' h.le).1 hxy
      have := Nat.le_of_dvd (by omega) this
      omega
    · rcases h.lt_or_eq with h | h
      · exfalso
        have : (2 * C.m + 7) ∣ x - y := (Nat.modEq_iff_dvd' h.le).1 hxy.symm
        have := Nat.le_of_dvd (by omega) this
        omega
      omega
  have himg : ((Finset.Ico U F).filter (BrkU C nQ H)).image (fun x => x % (2 * C.m + 7)) ⊆
      insert (2 * C.m + 6) (((Finset.range (2 * C.m)).filter (Brk C nQ H)).image (· + 6)) := by
    intro ρ hρ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hρ
    simp only [Finset.mem_filter] at hx
    rcases hx.2 with h | ⟨h6, hlt, hb⟩
    · grind
    · refine Finset.mem_insert.2 (Or.inr (Finset.mem_image.2 ⟨x % (2 * C.m + 7) - 6, ?_,
        by omega⟩))
      grind
  have h1 := Finset.card_le_card himg
  rw [Finset.card_image_of_injOn hinj] at h1
  have h2 := Finset.card_insert_le (2 * C.m + 6)
    (((Finset.range (2 * C.m)).filter (Brk C nQ H)).image (· + 6))
  have h3 := Finset.card_image_le (s := (Finset.range (2 * C.m)).filter (Brk C nQ H))
    (f := (· + 6))
  have h4 := card_brk_le C hn hwf
  have h4' : ((Finset.range (2 * C.m)).filter (Brk C nQ H)).card ≤ 2 + 8 * H.length :=
    le_trans (Finset.card_le_card fun i hi => by
      simp only [Finset.mem_filter] at hi ⊢; ram_grind) h4
  omega

end ShootCut

end

end Chazelle.Core
