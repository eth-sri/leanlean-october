module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterTables
public import Chazelle.Core.ClusterFirst
public import Chazelle.Separator.Maps

/-!
# WP-I, part 25: face permutation, tree flags and face representatives on the RAM

* `fpStmt`: `FP[d] := ROT[OPP[d]]` (the face permutation), `fpStmt_exec`;
* `teStmt`: the tree-dart flags `TE[d] = 1` iff `d = PAR[v]` or `d = OPP[PAR[v]]` for some
  `1 ≤ v < μ`, else `0`; `teStmt_exec`;
* `attStmt`: the face representatives `ATT[e]` = the least dart of the face of `e`, by walking
  every face cycle once from its least dart; `attStmt_exec`.
* `face_orbit`: the darts of a face are the face-permutation iterates of any of its darts.

Registers: `fpStmt` `130520` (`ROT`), `130521` (`OPP`), `130522` (`FP`), `130523` (`N`), scratch
`130524 … 130526`; `teStmt` `130540` (`PAR`), `130541` (`OPP`), `130542` (`TE`), `130543` (`μ`),
`130544` (`N`), scratch `130545 … 130547` (and the fill registers `130150 … 130154`);
`attStmt` `130530` (`FP`), `130531` (`ATT`), `130532` (`N`), scratch `130533 … 130537` (and the fill
registers).
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs Chazelle.Separator

@[expose] public section

/-! ## Face orbits -/

section orbit

variable {μ N : ℕ} {F : Type*} {M : CombMap (Fin μ) F (Fin N)}

section
variable {fp : ℕ → ℕ} (hfp : ∀ d : Fin N, fp d = M.fperm d)
include hfp
theorem iterate_fp (n : ℕ) (d : Fin N) :
    fp^[n] d = ((M.fperm ^ n) d : Fin N) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => grind [Function.iterate_succ_apply, pow_succ, Equiv.Perm.mul_apply]

theorem fp_injOn : InjOn fp N := by
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · have := hfp ⟨x, hx⟩; simp_all
  · have h1 := hfp ⟨x, hx⟩; have h2 := hfp ⟨y, hy⟩
    simp only at h1 h2
    rw [h1, h2] at hxy
    have := M.fperm.injective (Fin.ext hxy)
    simp_all


end

/-- **The darts of a face are the iterates of the face permutation below the period.** -/
theorem face_orbit [Finite (Fin N)] {fp : ℕ → ℕ} (hfp : ∀ d : Fin N, fp d = M.fperm d)
    (d e : Fin N) :
    M.face e = M.face d ↔ ∃ i, i < per fp N d ∧ fp^[i] d = e := by
  constructor
  · intro h
    have hsc := M.sameCycle_of_face d e h.symm
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    obtain ⟨j, hj, hjn⟩ := exists_lt_per_of_iterate (fp_injOn hfp) d.2 n
    refine ⟨j, hj, ?_⟩
    rw [← hjn, iterate_fp hfp]
    exact congrArg Fin.val hn
  · rintro ⟨i, -, hi⟩
    have : (M.fperm ^ i) d = e := Fin.ext (by rw [← iterate_fp hfp]; exact hi)
    rw [← this]
    clear this hi
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, M.face_fperm_apply, ih]

end orbit

/-! ## The face permutation -/

/-- One dart: `FP[d] := ROT[OPP[d]]`. -/
def fpBody : Stmt := block [.addN 130525 130521 130524, .loadN 130526 130525,
  .addN 130525 130520 130526, .loadN 130526 130525, .addN 130525 130522 130524,
  .storeN 130525 130526, .addN 130524 130524 130001]

/-- **The face permutation array.** -/
def fpStmt : Stmt := .seq (.instr (.constN 130524 0)) (.whileLtN 130524 130523 fpBody)

/-- The scratch registers of `fpStmt`. -/
def FpRG (r : ℕ) : Prop := 130524 ≤ r ∧ r ≤ 130526

section fp

variable {P : Polygon} {W : ℕ}

/-- **The face permutation**: `FP[d] = ROT[OPP[d]]` for `d < N`. -/
theorem fpStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bR bO bF N : ℕ} (hR : c.nreg 130520 = bR) (hO : c.nreg 130521 = bO)
    (hF : c.nreg 130522 = bF) (hN : c.nreg 130523 = N) (hwO : bO + N ≤ W) (hwF : bF + N ≤ W)
    (hdO : bF + N ≤ bO ∨ bO + N ≤ bF)
    (hRw : ∀ d, d < N → bR + c.nmem (bO + d) ≤ W ∧
      (bR + c.nmem (bO + d) < bF ∨ bF + N ≤ bR + c.nmem (bO + d))) :
    ∃ c' k, Exec P W fpStmt c c' k ∧ k ≤ 9 * N + 3 ∧ WordsBounded W c' ∧
      PFr FpRG (fun a => bF ≤ a ∧ a < bF + N) c c' ∧
      ∀ d, d < N → c'.nmem (bF + d) = c.nmem (bR + c.nmem (bO + d)) := by
  have e0 := Exec.constN (P := P) hw 130524 0 (by omega)
  set c1 := { c with nreg := upd c.nreg 130524 0 }
  have hf1 : PFr FpRG (fun a => bF + 0 ≤ a ∧ a < bF + N) c c1 :=
    PFr.nreg (PFr.refl c) (fun r hr => by
      ram_simp)
  obtain ⟨c', k, e, hk, hw', -, hf', hI⟩ := mapLoop (P := P) (W := W) (ri := 130524)
    (rn := 130523) (body := fpBody) (Rg := FpRG) (by omega_nf)
    (by omega_nf) (bOut := bF) (n := N) (j₀ := 0) (B := 7)
    (fun d => c.nmem (bR + c.nmem (bO + d))) e0.wb_right
    (by aesop)
    (by ram_simp) (Nat.zero_le _)
    (fun j c2 _ hjn hw2 hi2 hf2 => by
      have hf12 := hf1.trans hf2
      have r0 : ∀ r, ¬ FpRG r → c2.nreg r = c.nreg r := hf12.1
      have rR := (r0 130520 (by omega_nf)).trans hR
      have rO := (r0 130521 (by omega_nf)).trans hO
      have rF := (r0 130522 (by omega_nf)).trans hF
      have r1 := (r0 130001 (by omega_nf)).trans hone
      have mO : c2.nmem (bO + j) = c.nmem (bO + j) := hf12.2.2.2.2 _ (by omega)
      obtain ⟨hwr, hdr⟩ := hRw j hjn
      have mR : c2.nmem (bR + c.nmem (bO + j)) = c.nmem (bR + c.nmem (bO + j)) :=
        hf12.2.2.2.2 _ (by omega)
      unfold fpBody
      exec_block
      · omega
      · simp_all
      · config_simp; omega
      all_goals (grind [Machine.upd_apply, FpRG]))
  refine ⟨c', 1 + k, .seq e0 e, by omega, hw', ?_, fun d hd => hI d (Nat.zero_le _) hd⟩
  ram_grind

end fp

/-! ## Tree-dart flags -/

/-- One vertex: `TE[PAR[v]] := 1`, `TE[OPP[PAR[v]]] := 1`, `v := v + 1`. -/
def teBody : Stmt := block [.addN 130546 130540 130545, .loadN 130547 130546,
  .addN 130546 130541 130547, .loadN 130548 130546, .addN 130546 130542 130547,
  .storeN 130546 130001, .addN 130546 130542 130548, .storeN 130546 130001,
  .addN 130545 130545 130001]

/-- **The tree-dart flags.** -/
def teStmt : Stmt := .seq (block [.copyN 130150 130542, .copyN 130151 130544, .copyN 130152 130009])
  (.seq fillStmt (.seq (.instr (.copyN 130545 130001)) (.whileLtN 130545 130543 teBody)))

/-- The registers written by `teStmt`. -/
def TeRG (r : ℕ) : Prop := (130545 ≤ r ∧ r ≤ 130548) ∨ (130150 ≤ r ∧ r ≤ 130154)

/-- The tree darts: `PAR[v]` and `OPP[PAR[v]]` for `1 ≤ v < j`. -/
def TeSet (m : ℕ → ℕ) (bPar bO j d : ℕ) : Prop :=
  ∃ v, 1 ≤ v ∧ v < j ∧ (d = m (bPar + v) ∨ d = m (bO + m (bPar + v)))

section te

variable {P : Polygon} {W : ℕ}

/-- **The tree-dart flags**: `TE[d] = 1` on the tree darts, `0` elsewhere. -/
theorem teStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {bPar bO bT μ N : ℕ} (hPar : c.nreg 130540 = bPar)
    (hO : c.nreg 130541 = bO) (hT : c.nreg 130542 = bT) (hμ : c.nreg 130543 = μ)
    (hN : c.nreg 130544 = N) (hμ1 : 1 ≤ μ) (hwP : bPar + μ ≤ W) (hwT : bT + N ≤ W)
    (hNW : N + 1 ≤ W)
    (hdP : bT + N ≤ bPar ∨ bPar + μ ≤ bT) (hdO : bT + N ≤ bO ∨ bO + N ≤ bT)
    (hparN : ∀ v, 1 ≤ v → v < μ → c.nmem (bPar + v) < N ∧ bO + c.nmem (bPar + v) ≤ W ∧
      c.nmem (bO + c.nmem (bPar + v)) < N) :
    ∃ c' k, Exec P W teStmt c c' k ∧ k ≤ 5 * N + 11 * μ + 10 ∧ WordsBounded W c' ∧
      PFr TeRG (fun a => bT ≤ a ∧ a < bT + N) c c' ∧
      ∀ d, d < N → (c'.nmem (bT + d) = 1 ∧ TeSet c.nmem bPar bO μ d) ∨
        (c'.nmem (bT + d) = 0 ∧ ¬ TeSet c.nmem bPar bO μ d) := by
  classical
  -- the fill
  obtain ⟨c1, k1, e1, hk1, hw1, h150, h151, h152, hr1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130150 130542, .copyN 130151 130544, .copyN 130152 130009]) c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 130150 = bT ∧ c1.nreg 130151 = N ∧
      c1.nreg 130152 = 0 ∧ PFr TeRG (fun a => bT ≤ a ∧ a < bT + N) c c1 := by
    exec_block
    refine ⟨rfl, ‹_›, by simp_all, by simp_all,
      by simp_all, PFr.nreg (PFr.refl c) (fun r hr => ?_)⟩
    grind [Machine.upd_apply, TeRG]
  have hone1 : c1.nreg 130001 = 1 := (hr1.1 _ (by omega_nf)).trans hone
  obtain ⟨c2, k2, e2, hk2, hf2, hfill⟩ := fillStmt_exec (P := P) e1.wb_right hone1
    (by omega) (by omega)
  rw [h150, h151, h152] at hfill
  rw [h151] at hk2
  have hr2 : PFr TeRG (fun a => bT ≤ a ∧ a < bT + N) c c2 :=
    hr1.trans (hf2.mono (fun r hr => by omega_nf)
      (fun a ha => by omega))
  have e3 := Exec.copyN (P := P) e2.wb_right 130545 130001
  set c3 := { c2 with nreg := upd c2.nreg 130545 (c2.nreg 130001) }
  have hr3 : PFr TeRG (fun a => bT ≤ a ∧ a < bT + N) c c3 :=
    PFr.nreg hr2 (fun r hr => by
      grind [Machine.upd_apply, TeRG])
  have hone3 : c3.nreg 130001 = 1 := (hr3.1 _ (by omega_nf)).trans hone
  obtain ⟨c', k, e, hk, hw', hi', hn', hf', hI⟩ := forN (P := P) (W := W) (ri := 130545)
    (rn := 130543) (body := teBody)
    (fun j c4 => WordsBounded W c4 ∧ c4.nreg 130545 = j ∧ c4.nreg 130543 = μ ∧
      PFr TeRG (fun a => bT ≤ a ∧ a < bT + N) c c4 ∧ 1 ≤ j ∧
      ∀ d, d < N → (c4.nmem (bT + d) = 1 ∧ TeSet c.nmem bPar bO j d) ∨
        (c4.nmem (bT + d) = 0 ∧ ¬ TeSet c.nmem bPar bO j d))
    μ 9 (fun j c4 h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c4 hj ⟨hw4, hi4, hn4, hf4, hj1, hI4⟩ => by
      have r0 : ∀ r, ¬ TeRG r → c4.nreg r = c.nreg r := hf4.1
      have rP := (r0 130540 (by unfold TeRG; omega)).trans hPar
      have rO := (r0 130541 (by unfold TeRG; omega)).trans hO
      have rT := (r0 130542 (by unfold TeRG; omega)).trans hT
      have r1 := (r0 130001 (by unfold TeRG; omega)).trans hone
      obtain ⟨hpN, hwo, hoN⟩ := hparN j hj1 hj
      have mP : c4.nmem (bPar + j) = c.nmem (bPar + j) := hf4.2.2.2.2 _ (by omega)
      set p := c.nmem (bPar + j)
      have mO : c4.nmem (bO + p) = c.nmem (bO + p) := hf4.2.2.2.2 _ (by omega)
      set o := c.nmem (bO + p)
      obtain ⟨c5, k5, e5, hk5, hw5, h5n, h5r, h5m, h5rr, h5rm, h5o⟩ : ∃ c5 k5,
          Exec P W teBody c4 c5 k5 ∧ k5 = 9 ∧ WordsBounded W c5 ∧ c5.nreg 130545 = j + 1 ∧
          (∀ r, ¬ TeRG r → c5.nreg r = c4.nreg r) ∧
          c5.nmem = upd (upd c4.nmem (bT + p) 1) (bT + o) 1 ∧
          c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧ c5.output = c4.output := by
        unfold teBody
        exec_block
        all_goals try (config_simp; simp only [rT, rO, rP, hi4, mP, mO, r1]; omega)
        refine ⟨rfl, ‹_›, by config_simp; rw [hi4, r1], fun r hr => ?_, ?_, rfl, rfl, rfl⟩
        · simp only [Machine.upd_apply]; grind [TeRG]
        · config_simp; simp only [rT, rO, rP, hi4, mP, mO, r1]
      refine ⟨c5, k5, e5, by omega, hw5, h5n, by grind [TeRG],
        ⟨fun r hr => (h5r r hr).trans (hf4.1 r hr), h5rr.trans hf4.2.1, h5rm.trans hf4.2.2.1,
          h5o.trans hf4.2.2.2.1, fun a ha => ?_⟩, by omega, fun d hd => ?_⟩
      · rw [h5m, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
        exact hf4.2.2.2.2 a ha
      · have hnew : TeSet c.nmem bPar bO (j + 1) d ↔ TeSet c.nmem bPar bO j d ∨
            d = p ∨ d = o := by
          constructor
          · rintro ⟨v, hv1, hv2, hv3⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hv2 with hv | rfl
            · exact Or.inl ⟨v, hv1, hv, hv3⟩
            grind
          · rintro (⟨v, hv1, hv2, hv3⟩ | h | h)
            · exact ⟨v, hv1, by omega, hv3⟩
            · exact ⟨j, hj1, by omega, Or.inl h⟩
            · exact ⟨j, hj1, by omega, Or.inr h⟩
        rw [h5m, Machine.upd_apply, Machine.upd_apply]
        grind)
    (j₀ := 1) ⟨e3.wb_right, by
      simp_all +zetaDelta ,
      by show upd c2.nreg 130545 (c2.nreg 130001) 130543 = μ
         rw [Machine.upd_other _ _ _ (by omega), hr2.1 _ (by omega_nf), hμ],
      hr3, le_rfl, fun d hd => Or.inr ⟨by
          grind, fun ⟨v, hv1, hv2, _⟩ => by omega⟩⟩ hμ1
  subst hk1
  refine ⟨c', 3 + (k2 + (1 + k)), .seq e1 (.seq e2 (.seq e3 e)), by omega, hw', hf', hI.2⟩

end te

/-! ## Face representatives -/

section orb

variable {f : ℕ → ℕ} {N : ℕ}

/-- `e` is on the cycle of `d`. -/
def Orb (f : ℕ → ℕ) (d e : ℕ) : Prop := ∃ i, f^[i] d = e

theorem orb_refl (d : ℕ) : Orb f d d := ⟨0, rfl⟩

theorem Orb.trans {a b c : ℕ} (h1 : Orb f a b) (h2 : Orb f b c) : Orb f a c := by
  obtain ⟨i, rfl⟩ := h1
  obtain ⟨j, rfl⟩ := h2
  exact ⟨j + i, by rw [Function.iterate_add_apply]⟩

section
variable (hf : InjOn f N) {a b : ℕ} (ha : a < N) (h : Orb f a b)
include hf a ha h
theorem Orb.symm : Orb f b a := by
  obtain ⟨i, rfl⟩ := h
  obtain ⟨j, hj, hij⟩ := exists_lt_per_of_iterate hf ha i
  refine ⟨per f N a - j, ?_⟩
  rw [hij, ← Function.iterate_add_apply, show per f N a - j + j = per f N a by omega,
    iterate_per hf ha]



end

open Classical in
/-- The least dart of the cycle of `e`. -/
noncomputable def minOrb (f : ℕ → ℕ) (e : ℕ) : ℕ := Nat.find (⟨e, orb_refl e⟩ : ∃ d, Orb f d e)

theorem minOrb_orb (e : ℕ) : Orb f (minOrb f e) e := by
  classical
  exact Nat.find_spec (⟨e, orb_refl e⟩ : ∃ d, Orb f d e)

theorem minOrb_le (e : ℕ) : minOrb f e ≤ e := by
  classical
  exact Nat.find_min' (⟨e, orb_refl e⟩ : ∃ d, Orb f d e) (orb_refl e)

theorem minOrb_min {d e : ℕ} (h : Orb f d e) : minOrb f e ≤ d := by
  classical
  exact Nat.find_min' (⟨e, orb_refl e⟩ : ∃ d, Orb f d e) h

/-- Darts on one cycle have the same least dart. -/
theorem minOrb_eq (hf : InjOn f N) {d e : ℕ} (hd : d < N) (h : Orb f d e) :
    minOrb f e = minOrb f d := by
  
  have h1 := minOrb_orb (f := f) e
  have h2 := minOrb_orb (f := f) d
  
  
  apply le_antisymm
  · exact minOrb_min (h2.trans h)
  · exact minOrb_min (h1.trans (h.symm hf hd))

end orb

/-- One step of the walk: `ATT[e] := d`, `e := FP[e]`, `cont := (e ≠ d)`. -/
def walkBody : Stmt := .seq (block [.addN 130536 130531 130534, .storeN 130536 130533,
    .addN 130536 130530 130534, .loadN 130534 130536, .constN 130535 0])
  (.ifLtN 130534 130533 (.instr (.copyN 130535 130001))
    (.ifLtN 130533 130534 (.instr (.copyN 130535 130001)) .skip))

/-- The walk around the cycle of `d`. -/
def walkS : Stmt := .seq (block [.copyN 130534 130533, .copyN 130535 130001])
  (.whileLtN 130009 130535 walkBody)

/-- One dart of the outer loop: walk its cycle unless it is visited. -/
def attOuter : Stmt := .seq (block [.addN 130536 130531 130533, .loadN 130537 130536])
  (.seq (.ifLtN 130537 130532 .skip walkS) (.instr (.addN 130533 130533 130001)))

/-- **The face representatives.** -/
def attStmt : Stmt := .seq (block [.copyN 130150 130531, .copyN 130151 130532,
    .copyN 130152 130532])
  (.seq fillStmt (.seq (.instr (.constN 130533 0)) (.whileLtN 130533 130532 attOuter)))

/-- The registers written by `attStmt`. -/
def AttRG (r : ℕ) : Prop := (130533 ≤ r ∧ r ≤ 130537) ∨ (130150 ≤ r ∧ r ≤ 130154)

/-- The unvisited cells. -/
def unv (m : ℕ → ℕ) (bA N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun x => m (bA + x) = N)).card

section att

variable {P : Polygon} {W : ℕ}

theorem unv_le (m : ℕ → ℕ) (bA N : ℕ) : unv m bA N ≤ N := by
  core_grind

/-- Setting a cell with `N` to `d < N` decreases the unvisited count. -/
theorem unv_upd {m : ℕ → ℕ} {bA N x d : ℕ} (hx : x < N) (hmx : m (bA + x) = N) (hd : d < N) :
    unv (upd m (bA + x) d) bA N + 1 = unv m bA N := by
  unfold unv
  have : (Finset.range N).filter (fun y => m (bA + y) = N) =
      insert x ((Finset.range N).filter (fun y => upd m (bA + x) d (bA + y) = N)) := by
    core_grind
  core_grind

/-- The context of the walk. -/
structure WalkCtx (c : Config) (bF bA N : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rF : c.nreg 130530 = bF
  rA : c.nreg 130531 = bA
  rN : c.nreg 130532 = N

theorem WalkCtx.of_frame {c c' : Config} {bF bA N : ℕ} (h : WalkCtx c bF bA N)
    (hr : ∀ r, ¬ AttRG r → c'.nreg r = c.nreg r) : WalkCtx c' bF bA N := by
  ram_grind

open Classical in
/-- **The walk around the cycle of `d`**: afterwards `ATT[x] = d` on the cycle, unchanged
elsewhere; cost plus `12` times the unvisited count does not grow beyond `12` times the old
count plus `6`. -/
theorem walkS_exec {c : Config} (hw : WordsBounded W c) {bF bA N d : ℕ}
    (hC : WalkCtx c bF bA N) (hd : c.nreg 130533 = d) (hdN : d < N)
    {f : ℕ → ℕ} (hf : InjOn f N) (hfm : ∀ x, x < N → c.nmem (bF + x) = f x)
    (hwA : bA + N ≤ W) (hwF : bF + N ≤ W) (hdisj : bA + N ≤ bF ∨ bF + N ≤ bA)
    (hfresh : ∀ i, i < per f N d → c.nmem (bA + f^[i] d) = N) :
    ∃ c' k, Exec P W walkS c c' k ∧ k + 12 * unv c'.nmem bA N ≤ 12 * unv c.nmem bA N + 6 ∧
      WordsBounded W c' ∧ c'.nreg 130533 = d ∧
      PFr AttRG (fun a => bA ≤ a ∧ a < bA + N) c c' ∧
      ∀ x, x < N → c'.nmem (bA + x) = if Orb f d x then d else c.nmem (bA + x) := by
  classical
  have hper := per_pos hf hdN
  -- the start
  obtain ⟨c1, k1, e1, hk1, hw1, h1e, h1c, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130534 130533, .copyN 130535 130001]) c c1 k1 ∧ k1 = 2 ∧
      WordsBounded W c1 ∧ c1.nreg 130534 = d ∧ c1.nreg 130535 = 1 ∧
      (∀ r, r ≠ 130534 → r ≠ 130535 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧
      c1.rmem = c.rmem ∧ c1.output = c.output ∧ c1.nmem = c.nmem := by
    exec_block
    refine ⟨rfl, ‹_›, by simp_all, by config_simp; exact hC.one,
      fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    simp_all
  -- the loop
  obtain ⟨c', k, e, ⟨hw', j, hj, hej, hcj, hdj, hf', hmj⟩, htest, hk⟩ := whileLtN_pot (P := P)
    (W := W) (a := 130009) (b := 130535) (body := walkBody)
    (fun c2 => WordsBounded W c2 ∧ ∃ j, j ≤ per f N d ∧ c2.nreg 130534 = f^[j] d ∧
      (c2.nreg 130535 = if j < per f N d then 1 else 0) ∧ c2.nreg 130533 = d ∧
      PFr AttRG (fun a => bA ≤ a ∧ a < bA + N) c c2 ∧
      ∀ x, x < N → c2.nmem (bA + x) =
        if ∃ i, i < j ∧ f^[i] d = x then d else c.nmem (bA + x))
    (fun c2 => 12 * unv c2.nmem bA N) (fun c2 h => h.1)
    (fun c2 ⟨hw2, j, hj, hej, hcj, hdj, hf2, hm2⟩ htest => by
      have hC2 := hC.of_frame hf2.1
      rw [hC2.zero, hcj] at htest
      have hjp : j < per f N d := by
        grind
      set e := f^[j] d
      have heN : e < N := hf.iterate_lt j hdN
      have hme : c2.nmem (bA + e) = N := by
        rw [hm2 e heN, ite_eq_right]
        · grind
        · rintro ⟨i, hi, hie⟩
          exact absurd (iterate_inj_of_lt_per hf hdN (by omega) hjp hie) (by omega)
      have hfe : c2.nmem (bF + e) = f e := by
        rw [hf2.2.2.2.2 _ (by omega)]; grind
      set e' := f e
      have he' : e' = f^[j + 1] d := by
        simp only [e', e]; rw [Function.iterate_succ_apply']
      -- the straight-line part
      obtain ⟨c3, k3, e3, hk3, hw3, h3e, h3c, h3d, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3,
          Exec P W (block [.addN 130536 130531 130534, .storeN 130536 130533,
            .addN 130536 130530 130534, .loadN 130534 130536, .constN 130535 0]) c2 c3 k3 ∧
          k3 = 5 ∧ WordsBounded W c3 ∧ c3.nreg 130534 = e' ∧ c3.nreg 130535 = 0 ∧
          c3.nreg 130533 = d ∧ (∀ r, ¬ AttRG r → c3.nreg r = c2.nreg r) ∧
          c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧
          c3.nmem = upd c2.nmem (bA + e) d := by
        exec_block
        all_goals first | omega | (config_simp; simp only [hC2.rA, hC2.rF, hej]; omega) | skip
        refine ⟨rfl, ‹_›, ?_, by config_simp, by ram_simp, fun r hr => ?_, rfl,
          rfl, rfl, ?_⟩
        · config_simp
          simp only [hC2.rA, hC2.rF, hej, hdj]
          ram_simp
        · simp only [Machine.upd_apply]; grind [AttRG]
        · config_simp; simp only [hC2.rA, hej, hdj]
      have hone3 : c3.nreg 130001 = 1 := (h3r _ (by omega_nf)).trans hC2.one
      -- the test `e' ≠ d`
      have hnext : (j + 1 < per f N d) ↔ e' ≠ d := by
        rw [he']
        constructor
        · intro h; exact iterate_ne_of_lt_per hf hdN (by omega) h
        · intro h
          by_contra h'
          exact h (by rw [show j + 1 = per f N d by omega]; exact iterate_per hf hdN)
      obtain ⟨c4, k4, e4, hk4, h4e, h4c, h4d, h4r, hrr4, hrm4, ho4, hm4⟩ : ∃ c4 k4,
          Exec P W (.ifLtN 130534 130533 (.instr (.copyN 130535 130001))
            (.ifLtN 130533 130534 (.instr (.copyN 130535 130001)) .skip)) c3 c4 k4 ∧
          k4 ≤ 4 ∧ c4.nreg 130534 = e' ∧
          (c4.nreg 130535 = if j + 1 < per f N d then 1 else 0) ∧ c4.nreg 130533 = d ∧
          (∀ r, ¬ AttRG r → c4.nreg r = c3.nreg r) ∧ c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧
          c4.output = c3.output ∧ c4.nmem = c3.nmem := by
        by_cases h1 : c3.nreg 130534 < c3.nreg 130533
        · have ec := Exec.copyN (P := P) hw3 130535 130001
          refine ⟨_, _, .ifLtN_true h1 ec, by omega, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl,
            rfl⟩
          · ram_simp
          · grind [Machine.upd_same]
          · ram_simp
          grind [Machine.upd_apply, AttRG]
        · by_cases h2 : c3.nreg 130533 < c3.nreg 130534
          · have ec := Exec.copyN (P := P) hw3 130535 130001
            refine ⟨_, _, .ifLtN_false h1 (.ifLtN_true h2 ec), by omega, ?_, ?_, ?_,
              fun r hr => ?_, rfl, rfl, rfl, rfl⟩
            · ram_simp
            · grind [Machine.upd_same]
            · ram_simp
            grind [Machine.upd_apply, AttRG]
          · refine ⟨c3, _, .ifLtN_false h1 (.ifLtN_false h2 (.skip hw3)), by omega, h3e, ?_, h3d,
              fun r _ => rfl, rfl, rfl, rfl, rfl⟩
            grind
      subst hk3
      refine ⟨c4, 5 + k4, .seq e3 e4, ⟨e4.wb_right, j + 1, by omega, by omega, h4c, h4d,
        ⟨fun r hr => (h4r r hr).trans ((h3r r hr).trans (hf2.1 r hr)),
          hrr4.trans (hrr3.trans hf2.2.1), hrm4.trans (hrm3.trans hf2.2.2.1),
          ho4.trans (ho3.trans hf2.2.2.2.1), fun a ha => ?_⟩, fun x hx => ?_⟩, ?_⟩
      · rw [hm4, hm3, Machine.upd_other _ _ _ (by omega)]; exact hf2.2.2.2.2 a ha
      · rw [hm4, hm3, Machine.upd_apply]
        by_cases hxe : bA + x = bA + e
        · rw [ite_eq_left hxe, ite_eq_left ⟨j, by omega, by omega⟩]
        · rw [ite_eq_right hxe, hm2 x hx]
          by_cases hex : ∃ i, i < j ∧ f^[i] d = x
          · obtain ⟨i, hi, hix⟩ := hex
            rw [ite_eq_left ⟨i, hi, hix⟩, ite_eq_left ⟨i, by omega, hix⟩]
          grind
      · rw [hm4, hm3]
        have := unv_upd (m := c2.nmem) (bA := bA) heN hme hdN
        omega)
    ⟨hw1, 0, Nat.zero_le _, by simp_all, by simp_all, by
      simp_all,
      ⟨fun r hr => h1r r (by grind [AttRG]) (by grind [AttRG]), hrr1,
        hrm1, ho1, fun a _ => by rw [hm1]⟩,
      fun x hx => by simp_all⟩
  have hC' := hC.of_frame hf'.1
  rw [hC'.zero, hcj] at htest
  have hjp : j = per f N d := by
    grind
  subst hjp
  refine ⟨c', k1 + k, .seq e1 e, ?_, hw', hdj, hf', fun x hx => ?_⟩
  · grind
  · rw [hmj x hx]
    congr 1
    apply propext
    constructor
    · ram_grind
    · rintro ⟨i, hi⟩
      obtain ⟨i', hi', hii⟩ := exists_lt_per_of_iterate hf hdN i
      grind

open Classical in
/-- **The face representatives**: afterwards `ATT[x]` is the least dart on the cycle of `x` under
`f x = FP[x]` (an injection of `[0, N)`), for all `x < N`. -/
theorem attStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {bF bA N : ℕ} (hF : c.nreg 130530 = bF)
    (hA : c.nreg 130531 = bA) (hN : c.nreg 130532 = N) {f : ℕ → ℕ} (hf : InjOn f N)
    (hfm : ∀ x, x < N → c.nmem (bF + x) = f x)
    (hwA : bA + N ≤ W) (hwF : bF + N ≤ W) (hNW : N + 1 ≤ W)
    (hdisj : bA + N ≤ bF ∨ bF + N ≤ bA) :
    ∃ c' k, Exec P W attStmt c c' k ∧ k ≤ 40 * N + 12 ∧ WordsBounded W c' ∧
      PFr AttRG (fun a => bA ≤ a ∧ a < bA + N) c c' ∧
      ∀ x, x < N → c'.nmem (bA + x) = minOrb f x := by
  -- the fill with `N`
  obtain ⟨c1, k1, e1, hk1, hw1, h150, h151, h152, hr1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130150 130531, .copyN 130151 130532, .copyN 130152 130532]) c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 130150 = bA ∧ c1.nreg 130151 = N ∧
      c1.nreg 130152 = N ∧ PFr AttRG (fun a => bA ≤ a ∧ a < bA + N) c c1 := by
    exec_block
    refine ⟨rfl, ‹_›, by simp_all, by simp_all,
      by simp_all, PFr.nreg (PFr.refl c) (fun r hr => ?_)⟩
    grind [Machine.upd_apply, AttRG]
  have hone1 : c1.nreg 130001 = 1 := (hr1.1 _ (by omega_nf)).trans hone
  obtain ⟨c2, k2, e2, hk2, hf2, hfill⟩ := fillStmt_exec (P := P) e1.wb_right hone1
    (by omega) (by omega)
  rw [h150, h151, h152] at hfill
  rw [h151] at hk2
  have hr2 : PFr AttRG (fun a => bA ≤ a ∧ a < bA + N) c c2 :=
    hr1.trans (hf2.mono (fun r hr => by grind [FillScr, AttRG])
      (fun a ha => by omega))
  have e3 := Exec.constN (P := P) e2.wb_right 130533 0 (by omega)
  set c3 := { c2 with nreg := upd c2.nreg 130533 0 }
  have hr3 : PFr AttRG (fun a => bA ≤ a ∧ a < bA + N) c c3 :=
    PFr.nreg hr2 (fun r hr => by
      grind [Machine.upd_apply, AttRG])
  have hC : WalkCtx c bF bA N := ⟨hone, hzero, hF, hA, hN⟩
  -- the outer loop
  obtain ⟨c', k, e, ⟨hw', d, hd, hdN, hf', hI⟩, htest, hk⟩ := whileLtN_pot (P := P) (W := W)
    (a := 130533) (b := 130532) (body := attOuter)
    (fun c4 => WordsBounded W c4 ∧ ∃ d, c4.nreg 130533 = d ∧ d ≤ N ∧
      PFr AttRG (fun a => bA ≤ a ∧ a < bA + N) c c4 ∧
      ∀ x, x < N → c4.nmem (bA + x) = if minOrb f x < d then minOrb f x else N)
    (fun c4 => 12 * unv c4.nmem bA N + 20 * (N - c4.nreg 130533)) (fun c4 h => h.1)
    (fun c4 ⟨hw4, d, hd4, hdN, hf4, hI4⟩ htest => by
      have hC4 := hC.of_frame hf4.1
      rw [hd4, hC4.rN] at htest
      have hmd : minOrb f d ≤ d := minOrb_le d
      obtain ⟨c5, k5, e5, hk5, hw5, h5v, h5d, h5r, hrr5, hrm5, ho5, hm5⟩ : ∃ c5 k5, Exec P W
          (block [.addN 130536 130531 130533, .loadN 130537 130536]) c4 c5 k5 ∧ k5 = 2 ∧
          WordsBounded W c5 ∧ c5.nreg 130537 = c4.nmem (bA + d) ∧ c5.nreg 130533 = d ∧
          (∀ r, ¬ AttRG r → c5.nreg r = c4.nreg r) ∧ c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧
          c5.output = c4.output ∧ c5.nmem = c4.nmem := by
        exec_block
        all_goals (grind [Chazelle.Core.Cluster.WalkCtx.rA, Machine.upd_apply, AttRG])
      have hC5 := hC4.of_frame h5r
      have hf5 : PFr AttRG (fun a => bA ≤ a ∧ a < bA + N) c c5 :=
        ⟨fun r hr => (h5r r hr).trans (hf4.1 r hr), hrr5.trans hf4.2.1, hrm5.trans hf4.2.2.1,
          ho5.trans hf4.2.2.2.1, fun a ha => by ram_grind⟩
      by_cases hvis : c5.nreg 130537 < c5.nreg 130532
      · -- visited: skip
        have hlt : minOrb f d < d := by
          rw [h5v, hC5.rN, hI4 d htest] at hvis
          grind
        have e6 := Exec.addN (P := P) hw5 130533 130533 130001 (by
          rw [h5d, hC5.one]; omega)
        refine ⟨_, k5 + (0 + 1 + 1), .seq e5 (.seq (.ifLtN_true hvis (.skip hw5)) e6),
          ⟨e6.wb_right, d + 1, by simp [h5d, hC5.one], by omega, PFr.nreg hf5 (fun r hr => by
            grind [Machine.upd_apply, AttRG]),
            fun x hx => ?_⟩, ?_⟩
        · grind [Chazelle.Core.Cluster.minOrb_orb, Chazelle.Core.Cluster.minOrb_eq]
        · simp only [Machine.upd_same, h5d, hC5.one, hm5]
          omega
      · -- a new cycle: walk
        have hmdd : minOrb f d = d := by
          grind [Chazelle.Core.Cluster.WalkCtx.rN, Chazelle.Core.Cluster.minOrb_le]
        have hfresh : ∀ i, i < per f N d → c5.nmem (bA + f^[i] d) = N := by
          intro i hi
          have hxN := hf.iterate_lt i htest
          rw [hm5, hI4 _ hxN, minOrb_eq hf htest ⟨i, rfl⟩, hmdd, ite_eq_right (by omega)]
        obtain ⟨c6, k6, e6, hk6, hw6, h6d, hf6, hm6⟩ := walkS_exec (P := P) hw5 hC5 h5d htest hf
          (fun x hx => by rw [hm5, hf4.2.2.2.2 _ (by omega)]; grind) hwA hwF hdisj
          hfresh
        have hC6 := hC5.of_frame hf6.1
        have e7 := Exec.addN (P := P) hw6 130533 130533 130001 (by
          rw [h6d, hC6.one]; omega)
        refine ⟨_, k5 + (k6 + 2 + 1), .seq e5 (.seq (.ifLtN_false hvis e6) e7),
          ⟨e7.wb_right, d + 1, by simp [h6d, hC6.one], by omega,
            PFr.nreg (hf5.trans hf6) (fun r hr => by
              grind [Machine.upd_apply, AttRG]),
            fun x hx => ?_⟩, ?_⟩
        · show c6.nmem (bA + x) = _
          rw [hm6 x hx]
          by_cases horb : Orb f d x
          · rw [ite_eq_left horb, minOrb_eq hf htest horb, hmdd, ite_eq_left (by omega)]
          grind [Chazelle.Core.Cluster.minOrb_orb]
        · simp only [Machine.upd_same, h6d, hC6.one]
          grind)
    ⟨e3.wb_right, 0, by simp [c3], Nat.zero_le _, hr3, fun x hx => by
      grind⟩
  have hC' := hC.of_frame hf'.1
  rw [hd, hC'.rN] at htest
  have hdN' : d = N := by omega
  rw [hdN'] at hI
  subst hk1
  refine ⟨c', 3 + (k2 + (1 + k)), .seq e1 (.seq e2 (.seq e3 e)), ?_, hw', hf', fun x hx => ?_⟩
  all_goals (grind [Chazelle.Core.Cluster.unv_le, Chazelle.Core.Cluster.minOrb_le])

end att

end

end Chazelle.Core.Cluster
