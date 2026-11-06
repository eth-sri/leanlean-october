module

public import Chazelle.Core.ShotListCut2
public import Chazelle.Core.SweepPrimAbs

/-!
# Shooting at a list of arcs with holes, part 5: one shot and the running minimum

The **leaf** of the cutting recursion shoots at one piece (level-3 registers `R + 70 … R + 73`)
with the ray shooter `sh` (`ShooterOK`) and keeps the first hit over the pieces shot so far:
flag `R + 20`, position `R + 21`, `R + 22`, and the abscissa record (`absKey`) of its point in
`R + 24 … R + 27`.  Two hits on one ray are compared by abscissa (`absCmp`), in the direction of
the ray (`R + 35`: the bit `σ = 1`).

* `firstHit_union_*`, `noHit_union`: the first hit on a union;
* `BestOK`: the running minimum describes the first hit on the union `S` of the pieces shot;
* `leaf_exec`: one shot extends `S` by the piece.
-/

namespace Chazelle.Core

namespace ShotList

open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)

@[expose] public section

/-! ## First hits on unions -/

theorem noHit_union {A B : Set Point} {p : Point} {σ : ℝ} (hA : NoHit A p σ) (hB : NoHit B p σ) :
    NoHit (A ∪ B) p σ := fun t ht h => h.elim (hA t ht) (hB t ht)

theorem firstHit_union_left {A B : Set Point} {p : Point} {σ t : ℝ} (hA : FirstHit A p σ t)
    (hB : NoHit B p σ) : FirstHit (A ∪ B) p σ t :=
  ⟨hA.1, Or.inl hA.2.1, fun t' h1 h2 h => h.elim (hA.2.2 t' h1 h2) (hB t' h1)⟩

theorem firstHit_union_right {A B : Set Point} {p : Point} {σ t : ℝ} (hA : NoHit A p σ)
    (hB : FirstHit B p σ t) : FirstHit (A ∪ B) p σ t :=
  ⟨hB.1, Or.inr hB.2.1, fun t' h1 h2 h => h.elim (hA t' h1) (hB.2.2 t' h1 h2)⟩

theorem firstHit_union_le {A B : Set Point} {p : Point} {σ t t' : ℝ} (hA : FirstHit A p σ t)
    (hB : FirstHit B p σ t') (h : t ≤ t') : FirstHit (A ∪ B) p σ t :=
  ⟨hA.1, Or.inl hA.2.1, fun s h1 h2 hs => hs.elim (hA.2.2 s h1 h2)
    (hB.2.2 s h1 (lt_of_lt_of_le h2 h))⟩

theorem firstHit_union_le' {A B : Set Point} {p : Point} {σ t t' : ℝ} (hA : FirstHit A p σ t)
    (hB : FirstHit B p σ t') (h : t' ≤ t) : FirstHit (A ∪ B) p σ t' := by
  have := firstHit_union_le hB hA h
  rwa [Set.union_comm] at this

/-- On a ray, the parameters compare like the abscissae (in the direction of the ray). -/
theorem ray_lt_iff {p : Point} {σ t t' : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    t < t' ↔ (if σ = 1 then (rayPt p σ t).1 < (rayPt p σ t').1
      else (rayPt p σ t').1 < (rayPt p σ t).1) := by
  rcases hσ with rfl | rfl
  · simp
  · simp only [rayPt_fst, show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte]; constructor <;> intro <;>
      linarith

/-! ## Copying records -/

/-- An abscissa record survives a copy of its four words. -/
theorem absRec_copy {P : Polygon} {c c' : Config} {r r' : ℕ} {x R : ℝ} (h : AbsRec P c r x R)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg (r' + 1) = c.nreg (r + 1))
    (h2 : c'.nreg (r' + 2) = c.nreg (r + 2)) (h3 : c'.nreg (r' + 3) = c.nreg (r + 3)) :
    AbsRec P c' r' x R := by
  obtain ⟨hR, hk⟩ := h
  refine ⟨hR, ?_⟩
  rcases hk with ⟨k, hx⟩ | ⟨k, hx⟩ | ⟨k, hx, s, hs, hl, he⟩
  · exact Or.inl ⟨h0.trans k, hx⟩
  · exact Or.inr (Or.inl ⟨h0.trans k, hx⟩)
  · refine Or.inr (Or.inr ⟨h0.trans k, hx, s, ?_, hl, he⟩)
    have e1 : r' + 1 + 1 = r' + 2 := by omega
    have e2 : r + 1 + 1 = r + 2 := by omega
    have e3 : r' + 1 + 2 = r' + 3 := by omega
    have e4 : r + 1 + 2 = r + 3 := by omega
    exact NFLoc.symPtIn_copy hs h1 (by rw [e1, e2]; exact h2) (by rw [e3, e4]; exact h3)

/-- An origin survives a copy of its three words. -/
theorem originIn_copy {c c' : Config} {r r' : ℕ} {o : Origin} (h : OriginIn c r o)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg (r' + 1) = c.nreg (r + 1))
    (h2 : c'.nreg (r' + 2) = c.nreg (r + 2)) : OriginIn c' r' o := by
  cases o with
  | sym p => exact NFLoc.symPtIn_copy h h0 h1 h2
  | walk x => exact ⟨h0.trans h.1, h1.trans h.2.1, h2.trans h.2.2⟩

/-! ## The shooter with an edge bound on its hits -/

/-- **`ShooterOK` with the edge of the hit position in range** (spec amendments G9, G10: `ShooterOK`
now states the bound itself, and `shooterOKE_of` gives this contract from it). -/
def ShooterOKE (sh : Stmt) (B : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) : Prop :=
  Meets sh B
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
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
    (fun P c c' => ∀ M (o : Origin), ModelDescAt c.nmem (rd c bShoot 0) (Qof P) M →
      OriginIn c (bandReg bShoot 5) o →
        let A := M.arcSet (M.key (Qof P) ⟨rd c bShoot 1, rd c bShoot 2⟩)
          (M.key (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩)
        (rd c' bShoot 10 = 1 → ∃ t, FirstHit A (o.eval M (Qof P)) (dirOf (rd c bShoot 8)) t ∧
          ProperPos M (Qof P) P.n ⟨rd c' bShoot 11, rd c' bShoot 12⟩ ∧
          rd c' bShoot 11 < M.W.n ∧
          M.pos (Qof P) ⟨rd c' bShoot 11, rd c' bShoot 12⟩ =
            Visibility.rayPt (o.eval M (Qof P)) (dirOf (rd c bShoot 8)) t) ∧
        (rd c' bShoot 10 ≠ 1 → NoHit A (o.eval M (Qof P)) (dirOf (rd c bShoot 8))))
    (fun _ c => F (rd c bShoot 9))

/-- **`ShooterOK` gives `ShooterOKE`** (the two contracts coincide since amendment G9). -/
theorem shooterOKE_of {sh : Stmt} {B : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (h : ShooterOK sh B F X Ok) : ShooterOKE sh B F X Ok := h

/-! ## The running minimum -/

/-- **The running minimum** at `R` describes the first hit of the ray from `z` in direction `σ`
on `S` (in the chain model `M` of `C`). -/
def BestOK (P : Polygon) (C : Chain) (R : ℕ) (c : Config) (S : Set Point) (z : Point) (σ : ℝ) :
    Prop :=
  c.nreg (R + 20) ≤ 1 ∧
    (c.nreg (R + 20) = 1 → ∃ t, FirstHit S z σ t ∧
      ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg (R + 21), c.nreg (R + 22)⟩ ∧
      c.nreg (R + 21) < (chainModel C).W.n ∧
      (chainModel C).pos (Qof P) ⟨c.nreg (R + 21), c.nreg (R + 22)⟩ = rayPt z σ t ∧
      AbsRec P c (R + 24) (rayPt z σ t).1 C.radius) ∧
    (c.nreg (R + 20) ≠ 1 → NoHit S z σ)

/-! ## The programs -/

/-- The shooter's inputs: model descriptor, the piece, the origin, direction, weight bound and
context. -/
def setList (R : ℕ) : List (ℕ × ℕ) := [(140000, R), (140001, R + 70), (140002, R + 71),
  (140003, R + 72), (140004, R + 73), (140005, R + 3), (140006, R + 4), (140007, R + 5),
  (140008, R + 6), (140009, R + 7), (140013, R + 8)]

/-- Setting up the shooter. -/
def leafSet (R : ℕ) : Stmt := block (copies (setList R))

/-- The candidate's position and the inputs of `absKey`. -/
def keyList (R : ℕ) : List (ℕ × ℕ) := [(R + 244, 140011), (R + 245, 140012), (50200, R + 34),
  (50201, 140011), (50202, 140012)]

/-- The candidate's abscissa record. -/
def recList (R : ℕ) : List (ℕ × ℕ) :=
  [(R + 240, 50210), (R + 241, 50211), (R + 242, 50212), (R + 243, 50213)]

/-- The candidate: its position into `R + 244`, `R + 245`, its abscissa record into
`R + 240 … R + 243`. -/
def leafKey (R : ℕ) : Stmt :=
  .seq (block (copies (keyList R))) (.seq absKey (block (copies (recList R))))

/-- The copies accepting the candidate. -/
def accList (R : ℕ) : List (ℕ × ℕ) := [(R + 21, R + 244), (R + 22, R + 245), (R + 24, R + 240),
  (R + 25, R + 241), (R + 26, R + 242), (R + 27, R + 243)]

/-- Accept the candidate. -/
def leafAcc (R : ℕ) : Stmt := .seq (.instr (.constN (R + 20) 1)) (block (copies (accList R)))

/-- Two abscissa records into the inputs of `absCmp`. -/
def cmpLoad (R u v : ℕ) : List (ℕ × ℕ) := [(50201, R + u), (50202, R + u + 1),
  (50203, R + u + 2), (50204, R + u + 3), (50205, R + v), (50206, R + v + 1),
  (50207, R + v + 2), (50208, R + v + 3)]

/-- The bits `cand < best` (`R + 246`) and `best < cand` (`R + 247`) of the abscissae. -/
def leafCmp (R : ℕ) : Stmt :=
  .seq (block (copies (cmpLoad R 240 24))) (.seq absCmp (.seq (block [.copyN (R + 246) 50210])
    (.seq (block (copies (cmpLoad R 24 240))) (.seq absCmp (block [.copyN (R + 247) 50210])))))

/-- Accept if the candidate comes first along the ray. -/
def leafDec (R : ℕ) : Stmt :=
  .ifLtN (R + 30) (R + 35) (.ifLtN (R + 30) (R + 246) (leafAcc R) .skip)
    (.ifLtN (R + 30) (R + 247) (leafAcc R) .skip)

/-- A hit: accept it if there is no minimum yet, else compare. -/
def leafHit (R : ℕ) : Stmt :=
  .seq (leafKey R) (.ifLtN (R + 20) (R + 31) (leafAcc R) (.seq (leafCmp R) (leafDec R)))

/-- **The leaf**: one shot at the piece of level `3`, and the running minimum. -/
def leaf (sh : Stmt) (R : ℕ) : Stmt :=
  .seq (leafSet R) (.seq sh (.ifLtN (R + 31) 140010 .skip (.ifLtN 140010 (R + 31) .skip
    (leafHit R))))

/-! ## Execution of the blocks -/

/-- A block of copies, with the side conditions of `copies_exec` discharged by `simp`/`omega`. -/
theorem copies_run {P : Polygon} {W : ℕ} (l : List (ℕ × ℕ)) (c : Config) (hw : WordsBounded W c)
    (hd : ∀ p ∈ l, ∀ q ∈ l, p.1 ≠ q.2) (hnd : (l.map Prod.fst).Nodup) :
    ∃ c', Exec P W (block (copies l)) c c' l.length ∧ (∀ p ∈ l, c'.nreg p.1 = c.nreg p.2) ∧
      FrameB (fun r => (l.map Prod.fst).contains r) c c' := by
  obtain ⟨c', e, h1, h2, h3, h4, h5, h6⟩ := copies_exec l c hw hd hnd
  refine ⟨c', e, h1, fun r hr => h2 r (by simpa using hr), fun r _ => by rw [h3], h4, h5, h6⟩

/-- **Setting up the shooter.** -/
theorem leafSet_exec {P : Polygon} {W : ℕ} {R : ℕ} (hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) :
    ∃ c' k, Exec P W (leafSet R) c c' k ∧ k = 11 ∧ (∀ p ∈ setList R, c'.nreg p.1 = c.nreg p.2) ∧
      FrameB (fun r => ((setList R).map Prod.fst).contains r) c c' := by
  have h := hR; unfold RegsOK at h
  obtain ⟨c', e, h1, h2⟩ := copies_run (P := P) (setList R) c hw (by
    simp only [setList, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      q (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp <;> omega)
    (by simp [setList])
  exact ⟨c', _, e, rfl, h1, h2⟩

/-- A register of the caller's block is not written by a primitive. -/
theorem bprim_R' {R : ℕ} (hR : RegsOK R) {r : ℕ} (h1 : R ≤ r) (h2 : r < R + 300) :
    Bprim r = false := by
  have := bprim_R hR (i := r - R) (by omega)
  rwa [show R + (r - R) = r by omega] at this

/-- The write set of `leafKey`. -/
def Bkey (R : ℕ) (r : ℕ) : Bool :=
  decide (R + 240 ≤ r ∧ r < R + 246) || Bprim r || decide (50200 ≤ r ∧ r < 50210)

/-- **The abscissa record of the candidate.** -/
theorem leafKey_exec {P : Polygon} {W : ℕ} {R : ℕ} (hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hHW : hostWords P.n ≤ W) {H : Host} {C : Chain}
    (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg (R + 34)))
    (hC : ChainDescAt c.nmem (c.nreg (R + 34)) (Qof P) H C)
    (hreg : ∀ H', HostAt c.nmem (c.nmem (c.nreg (R + 34))) H' → HostRegular P.n H')
    (he : c.nreg 140011 < (chainModel C).W.n)
    (hp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg 140011, c.nreg 140012⟩)
    (hy : |((chainModel C).pos (Qof P) ⟨c.nreg 140011, c.nreg 140012⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 16700 ≤ W) :
    ∃ c' k, Exec P W (leafKey R) c c' k ∧ k ≤ 16720 ∧ c'.nreg (R + 244) = c.nreg 140011 ∧
      c'.nreg (R + 245) = c.nreg 140012 ∧
      AbsRec P c' (R + 240) ((chainModel C).pos (Qof P) ⟨c.nreg 140011, c.nreg 140012⟩).1
        C.radius ∧ FrameB (Bkey R) c c' := by
  have h := hR; unfold RegsOK at h
  obtain ⟨c₁, e₁, v₁, f₁⟩ := copies_run (P := P) (keyList R) c hw (by
    simp only [keyList, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl) q (rfl | rfl | rfl | rfl | rfl) <;> simp <;> omega)
    (by simp [keyList]; omega)
  simp only [keyList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₁
  obtain ⟨v44, v45, v00, v01, v02⟩ := v₁
  have k₁ : ∀ r, r ≠ R + 244 → r ≠ R + 245 → ¬ (50200 ≤ r ∧ r < 50203) → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => f₁.1 r (by simp [keyList]; omega)
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k₁ _ (by unfold ALLOC; omega)
    (by unfold ALLOC; omega) (by unfold ALLOC; omega)
  have hM1 : c₁.nmem = c.nmem := f₁.2.2.1
  have hC1 : ChainDescAt c₁.nmem (c₁.nreg 50200) (Qof P) H C := by rw [hM1, v00]; exact hC
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, -⟩ := absKey_meets P W c₁ e₁.wb_right
    ⟨hG, hHW, by rw [hA1, hM1, v00]; exact hwf, H, C, hC1,
      ⟨by rw [v01]; exact he, by rw [v01, v02]; exact hp, by rw [v01, v02]; exact hy⟩,
      by rw [hM1, v00]; exact hreg⟩ (by rw [hA1]; show _ + 16700 ≤ W; omega)
  replace hk₂ : k₂ ≤ 16700 := hk₂
  have ar := post₂ H C hC1
  have F₂ := exec_frameB e₂ wr_absKey
  obtain ⟨c₃, e₃, v₃, f₃⟩ := copies_run (P := P) (recList R) c₂ e₂.wb_right (by
    simp only [recList, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl) q (rfl | rfl | rfl | rfl) <;> simp <;> omega)
    (by simp [recList])
  simp only [recList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₃
  obtain ⟨w0, w1, w2, w3⟩ := v₃
  have k₃ : ∀ r, ¬ (R + 240 ≤ r ∧ r < R + 244) → c₃.nreg r = c₂.nreg r :=
    fun r hr => f₃.1 r (by simp [recList]; omega)
  have r₂ : ∀ r, Bprim r = false → c₂.nreg r = c₁.nreg r := F₂.1
  have l1 : (keyList R).length = 5 := rfl
  have l3 : (recList R).length = 4 := rfl
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, ?_, ?_, ?_, ?_⟩
  · rw [k₃ _ (by omega), r₂ _ (bprim_R' hR (by omega) (by omega)), v44]
  · rw [k₃ _ (by omega), r₂ _ (bprim_R' hR (by omega) (by omega)), v45]
  · have ar' : AbsRec P c₂ 50210 ((chainModel C).pos (Qof P)
        ⟨c₁.nreg 50201, c₁.nreg 50202⟩).1 C.radius := ar
    rw [v01, v02] at ar'
    exact absRec_copy ar' w0 (by rw [w1]) (by rw [w2]) (by rw [w3])
  · refine ((frameB_mono f₁ (fun r hr => ?_)).trans (frameB_mono F₂ (fun r hr => ?_))).trans
      (frameB_mono f₃ (fun r hr => ?_))
    · simp [keyList] at hr; simp only [Bkey, Bool.or_eq_true, decide_eq_true_eq]; omega
    · simp only [Bkey, hr, Bool.or_true, Bool.true_or]
    · simp [recList] at hr; simp only [Bkey, Bool.or_eq_true, decide_eq_true_eq]; omega

/-- **Accepting the candidate.** -/
theorem leafAcc_exec {P : Polygon} {W : ℕ} {R : ℕ} (_hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (leafAcc R) c c' k ∧ k = 7 ∧ c'.nreg (R + 20) = 1 ∧
      c'.nreg (R + 21) = c.nreg (R + 244) ∧ c'.nreg (R + 22) = c.nreg (R + 245) ∧
      c'.nreg (R + 24) = c.nreg (R + 240) ∧ c'.nreg (R + 25) = c.nreg (R + 241) ∧
      c'.nreg (R + 26) = c.nreg (R + 242) ∧ c'.nreg (R + 27) = c.nreg (R + 243) ∧
      FrameB (fun r => decide (R + 20 ≤ r ∧ r < R + 28)) c c' := by
  have e₁ := Exec.constN (P := P) hw (R + 20) 1 hW
  set c₁ : Config := { c with nreg := upd c.nreg (R + 20) 1 } with hc₁
  have r₁ : ∀ r, r ≠ R + 20 → c₁.nreg r = c.nreg r := fun r hr => by rw [hc₁]; simp [upd, hr]
  obtain ⟨c₂, e₂, v₂, f₂⟩ := copies_run (P := P) (accList R) c₁ e₁.wb_right (by
    simp only [accList, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl) q (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp)
    (by simp [accList])
  simp only [accList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₂
  obtain ⟨a1, a2, a4, a5, a6, a7⟩ := v₂
  have ex : Exec P W (leafAcc R) c c₂ (1 + (accList R).length) := .seq e₁ e₂
  refine ⟨c₂, _, ex, rfl, ?_, by rw [a1, r₁ _ (by omega)], by rw [a2, r₁ _ (by omega)],
    by rw [a4, r₁ _ (by omega)], by rw [a5, r₁ _ (by omega)], by rw [a6, r₁ _ (by omega)],
    by rw [a7, r₁ _ (by omega)], ?_⟩
  · have g : ((accList R).map Prod.fst).contains (R + 20) = false := by simp [accList]
    rw [f₂.1 _ g, hc₁]; simp
  · have fa : FrameB (fun r => decide (R + 20 ≤ r ∧ r < R + 28)) c c₁ :=
      frameB_mono (exec_frameB e₁ (show wr (Bone (R + 20)) (.instr (.constN (R + 20) 1)) = true by
        simp [wr, wrOK, Bone])) (fun r hr => by simp only [Bone, beq_iff_eq] at hr; simp [hr])
    have fb : FrameB (fun r => decide (R + 20 ≤ r ∧ r < R + 28)) c₁ c₂ :=
      frameB_mono f₂ (fun r hr => by
        simp [accList] at hr; simp only [decide_eq_true_eq]; omega)
    exact fa.trans fb

/-- The write set of `leafCmp`. -/
def Bcmp2 (R : ℕ) (r : ℕ) : Bool :=
  decide (R + 246 ≤ r ∧ r < R + 248) || Bprim r || decide (50200 ≤ r ∧ r < 50210)

theorem cmpLoad_run {P : Polygon} {W : ℕ} {R u v : ℕ} (hR : RegsOK R) (hu : u + 4 ≤ 300)
    (hv : v + 4 ≤ 300) (c : Config) (hw : WordsBounded W c) :
    ∃ c', Exec P W (block (copies (cmpLoad R u v))) c c' 8 ∧
      (∀ i, i < 4 → c'.nreg (50201 + i) = c.nreg (R + u + i)) ∧
      (∀ i, i < 4 → c'.nreg (50205 + i) = c.nreg (R + v + i)) ∧
      FrameB (fun r => decide (50200 ≤ r ∧ r < 50210)) c c' := by
  have h := hR; unfold RegsOK at h
  obtain ⟨c', e, v', f⟩ := copies_run (P := P) (cmpLoad R u v) c hw (by
    simp only [cmpLoad, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      q (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp <;> omega)
    (by simp [cmpLoad])
  simp only [cmpLoad, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v'
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ := v'
  refine ⟨c', e, fun i hi => ?_, fun i hi => ?_, frameB_mono f (fun r hr => by
    simp [cmpLoad] at hr; simp only [decide_eq_true_eq]; omega)⟩
  · interval_cases i
    · exact a0
    · exact a1
    · exact a2
    · exact a3
  · interval_cases i
    · exact b0
    · exact b1
    · exact b2
    · exact b3

/-- An abscissa record read from `R + u …` into the input slot at `s`. -/
theorem absRec_moved {P : Polygon} {c c' : Config} {r s : ℕ} {x R : ℝ} (h : AbsRec P c r x R)
    (hc : ∀ i, i < 4 → c'.nreg (s + i) = c.nreg (r + i)) : AbsRec P c' s x R :=
  absRec_copy h (by simpa using hc 0 (by omega)) (hc 1 (by omega)) (hc 2 (by omega))
    (hc 3 (by omega))

/-- **Comparing the abscissae** of the candidate (record at `R + 240`) and of the minimum
(record at `R + 24`). -/
theorem leafCmp_exec {P : Polygon} {W : ℕ} {R : ℕ} (hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {xc xb Rd : ℝ}
    (hc : AbsRec P c (R + 240) xc Rd) (hb : AbsRec P c (R + 24) xb Rd)
    (hroom : c.nreg ALLOC + 600 ≤ W) :
    ∃ c' k, Exec P W (leafCmp R) c c' k ∧ k ≤ 600 ∧ BitIs c' (R + 246) (xc < xb) ∧
      BitIs c' (R + 247) (xb < xc) ∧ FrameB (Bcmp2 R) c c' := by
  have h := hR; unfold RegsOK at h
  -- first comparison
  obtain ⟨c₁, e₁, a₁, b₁, f₁⟩ := cmpLoad_run (P := P) (u := 240) (v := 24) hR (by omega)
    (by omega) c hw
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := f₁.1 _ (by simp [ALLOC])
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, -⟩ := absCmp_meets P W c₁ e₁.wb_right
    ⟨hG, hW, xc, xb, Rd, absRec_moved hc (fun i hi => by rw [a₁ i hi]),
      absRec_moved hb (fun i hi => by rw [b₁ i hi])⟩ (by rw [hA1]; show _ + 260 ≤ W; omega)
  replace hk₂ : k₂ ≤ 260 := hk₂
  have bit₂ := post₂ xc xb Rd (absRec_moved hc (fun i hi => by rw [a₁ i hi]))
    (absRec_moved hb (fun i hi => by rw [b₁ i hi]))
  have F₂ := exec_frameB e₂ wr_absCmp
  have e₃ := Exec.copyN (P := P) e₂.wb_right (R + 246) 50210
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg (R + 246) (c₂.nreg 50210) } with hc₃
  have w₃ := e₃.wb_right
  -- registers of `c` in the band of `R` survive
  have keep3 : ∀ r, R ≤ r → r < R + 300 → r ≠ R + 246 → c₃.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [hc₃]; simp only [upd, h3, ↓reduceIte]
    rw [F₂.1 r (bprim_R' hR h1 h2), f₁.1 r (by simp only [decide_eq_false_iff_not]; omega)]
  have hA3 : c₃.nreg ALLOC = c.nreg ALLOC := by
    rw [hc₃]; simp only [upd, show ALLOC ≠ R + 246 by unfold ALLOC; omega, ↓reduceIte]
    rw [F₂.1 _ (by simp [Bprim, ALLOC]), hA1]
  -- second comparison
  obtain ⟨c₄, e₄, a₄, b₄, f₄⟩ := cmpLoad_run (P := P) (u := 24) (v := 240) hR (by omega)
    (by omega) c₃ w₃
  have hA4 : c₄.nreg ALLOC = c.nreg ALLOC := by rw [f₄.1 _ (by simp [ALLOC]), hA3]
  have mv : ∀ {u : ℕ} {x : ℝ}, u + 4 ≤ 246 → AbsRec P c (R + u) x Rd →
      ∀ {s : ℕ} {cc : Config}, (∀ i, i < 4 → cc.nreg (s + i) = c₃.nreg (R + u + i)) →
        AbsRec P cc s x Rd := fun hu hx s cc hcc =>
    absRec_moved hx (fun i hi => by
      rw [hcc i hi, keep3 _ (by omega) (by omega) (by omega)])
  obtain ⟨c₅, k₅, e₅, hk₅, post₅, -⟩ := absCmp_meets P W c₄ e₄.wb_right
    ⟨hG, hW, xb, xc, Rd, mv (by omega) hb a₄, mv (by omega) hc b₄⟩
    (by rw [hA4]; show _ + 260 ≤ W; omega)
  replace hk₅ : k₅ ≤ 260 := hk₅
  have bit₅ := post₅ xb xc Rd (mv (by omega) hb a₄) (mv (by omega) hc b₄)
  have F₅ := exec_frameB e₅ wr_absCmp
  have e₆ := Exec.copyN (P := P) e₅.wb_right (R + 247) 50210
  have ex : Exec P W (leafCmp R) c _ _ :=
    .seq e₁ (.seq e₂ (.seq (Exec.block_cons e₃ (Exec.block_nil w₃))
      (.seq e₄ (.seq e₅ (Exec.block_cons e₆ (Exec.block_nil e₆.wb_right))))))
  refine ⟨_, _, ex, by omega, ?_, ?_, ?_⟩
  · -- the first bit survives
    have b3 : BitIs c₃ (R + 246) (xc < xb) :=
      ⟨by rw [hc₃]; simp only [upd_same]; exact bit₂.1,
        by rw [hc₃]; simp only [upd_same]; exact bit₂.2⟩
    refine b3.of_eq ?_
    · simp only [upd, show R + 246 ≠ R + 247 by omega, ↓reduceIte]
      rw [F₅.1 _ (bprim_R' hR (by omega) (by omega)),
        f₄.1 _ (by simp only [decide_eq_false_iff_not]; omega)]
  · exact ⟨by simp only [upd_same]; exact bit₅.1, by simp only [upd_same]; exact bit₅.2⟩
  · have g1 : FrameB (Bcmp2 R) c c₁ := frameB_mono f₁ (fun r hr => by simp [Bcmp2, hr])
    have g2 : FrameB (Bcmp2 R) c₁ c₂ := frameB_mono F₂ (fun r hr => by simp [Bcmp2, hr])
    have g3 : FrameB (Bcmp2 R) c₂ c₃ := frameB_mono (exec_frameB e₃
      (show wr (Bone (R + 246)) (.instr (.copyN (R + 246) 50210)) = true by
        simp [wr, wrOK, Bone])) (fun r hr => by
          simp only [Bone, beq_iff_eq] at hr; subst hr; simp [Bcmp2])
    have g4 : FrameB (Bcmp2 R) c₃ c₄ := frameB_mono f₄ (fun r hr => by simp [Bcmp2, hr])
    have g5 : FrameB (Bcmp2 R) c₄ c₅ := frameB_mono F₅ (fun r hr => by simp [Bcmp2, hr])
    have g6 : FrameB (Bcmp2 R) c₅ _ := frameB_mono (exec_frameB e₆
      (show wr (Bone (R + 247)) (.instr (.copyN (R + 247) 50210)) = true by
        simp [wr, wrOK, Bone])) (fun r hr => by
          simp only [Bone, beq_iff_eq] at hr; subst hr; simp [Bcmp2])
    exact g1.trans (g2.trans (g3.trans (g4.trans (g5.trans g6))))

/-! ## The running minimum after one hit -/

/-- The running minimum depends only on its registers. -/
theorem BestOK.congr {P : Polygon} {C : Chain} {R : ℕ} {c c' : Config} {S : Set Point} {z : Point}
    {σ : ℝ} (h : BestOK P C R c S z σ) (e0 : c'.nreg (R + 20) = c.nreg (R + 20))
    (e1 : c'.nreg (R + 21) = c.nreg (R + 21)) (e2 : c'.nreg (R + 22) = c.nreg (R + 22))
    (e4 : c'.nreg (R + 24) = c.nreg (R + 24)) (e5 : c'.nreg (R + 24 + 1) = c.nreg (R + 24 + 1))
    (e6 : c'.nreg (R + 24 + 2) = c.nreg (R + 24 + 2))
    (e7 : c'.nreg (R + 24 + 3) = c.nreg (R + 24 + 3)) : BestOK P C R c' S z σ := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨by rw [e0]; exact h0, fun hf => ?_, fun hf => h2 (by rw [← e0]; exact hf)⟩
  obtain ⟨t, ht, hp, he, hpos, ha⟩ := h1 (by rw [← e0]; exact hf)
  exact ⟨t, ht, by rw [e1, e2]; exact hp, by rw [e1]; exact he, by rw [e1, e2]; exact hpos,
    absRec_copy ha e4 e5 e6 e7⟩

theorem dirOf_eq_one {v : ℕ} (h : v = 1) : dirOf v = 1 := by simp [dirOf, h]

theorem dirOf_ne_one {v : ℕ} (h : v ≠ 1) : dirOf v = -1 := by simp [dirOf, h]

/-- The write set of `leafHit`. -/
def Bhit (R : ℕ) (r : ℕ) : Bool :=
  decide (R + 20 ≤ r ∧ r < R + 28) || decide (R + 240 ≤ r ∧ r < R + 250) || Bprim r ||
    decide (50200 ≤ r ∧ r < 50210)

theorem bhit_range {R r : ℕ} (h : (R + 20 ≤ r ∧ r < R + 28) ∨ (R + 240 ≤ r ∧ r < R + 250) ∨
    (50200 ≤ r ∧ r < 50210)) : Bhit R r = true := by
  unfold Bhit
  rcases h with h | h | h <;> simp [h]

theorem bhit_prim {R r : ℕ} (h : Bprim r = true) : Bhit R r = true := by simp [Bhit, h]

/-- **A hit updates the running minimum.** -/
theorem leafHit_exec {P : Polygon} {W : ℕ} {R : ℕ} (hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hHW : hostWords P.n ≤ W) {H : Host} {C : Chain}
    (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg (R + 34)))
    (hC : ChainDescAt c.nmem (c.nreg (R + 34)) (Qof P) H C)
    (hreg : ∀ H', HostAt c.nmem (c.nmem (c.nreg (R + 34))) H' → HostRegular P.n H')
    {S A : Set Point} {z : Point} {σ t : ℝ} (hA : FirstHit A z σ t)
    (he : c.nreg 140011 < (chainModel C).W.n)
    (hp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg 140011, c.nreg 140012⟩)
    (hpos : (chainModel C).pos (Qof P) ⟨c.nreg 140011, c.nreg 140012⟩ = rayPt z σ t)
    (hz : |z.2| < C.radius) (h30 : c.nreg (R + 30) = 0) (h31 : c.nreg (R + 31) = 1)
    (hσb : BitIs c (R + 35) (c.nreg (R + 6) = 1)) (hσ : σ = dirOf (c.nreg (R + 6)))
    (hbest : BestOK P C R c S z σ) (hroom : c.nreg ALLOC + 17400 ≤ W) :
    ∃ c' k, Exec P W (leafHit R) c c' k ∧ k ≤ 17400 ∧ BestOK P C R c' (S ∪ A) z σ ∧
      FrameB (Bhit R) c c' := by
  have h := hR; unfold RegsOK at h
  have hP3 : P.n + 3 ≤ W := by unfold hostWords at hHW; omega
  have hy : |((chainModel C).pos (Qof P) ⟨c.nreg 140011, c.nreg 140012⟩).2| < C.radius := by
    rw [hpos]; simpa using hz
  obtain ⟨c₁, k₁, e₁, hk₁, p44, p45, rc, f₁⟩ := leafKey_exec (P := P) hR c hw hG hHW hwf hC
    hreg he hp hy (by omega)
  rw [hpos] at rc
  have k1 : ∀ r, R ≤ r → r < R + 240 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r (by simp only [Bkey, bprim_R' hR h1 (by omega), Bool.or_false, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]; omega)
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := f₁.1 _ (by
    unfold ALLOC
    simp only [Bkey, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega)
  have best₁ : BestOK P C R c₁ S z σ := hbest.congr (k1 _ (by omega) (by omega))
    (k1 _ (by omega) (by omega)) (k1 _ (by omega) (by omega)) (k1 _ (by omega) (by omega))
    (k1 _ (by omega) (by omega)) (k1 _ (by omega) (by omega)) (k1 _ (by omega) (by omega))
  have w₁ := e₁.wb_right
  have fB : ∀ {B : ℕ → Bool} {c₀ c' : Config}, FrameB B c₀ c' → (∀ r, B r = true → Bhit R r) →
      FrameB (Bhit R) c₀ c' := fun h hB => frameB_mono h hB
  have f₁' : FrameB (Bhit R) c c₁ := fB f₁ (fun r hr => by
    simp only [Bkey, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with (h | h) | h
    · exact bhit_range (Or.inr (Or.inl ⟨h.1, by omega⟩))
    · exact bhit_prim h
    · exact bhit_range (Or.inr (Or.inr h)))
  -- the acceptance
  have accept : ∀ (cc : Config), WordsBounded W cc → FrameB (Bhit R) c cc →
      (∀ r, R + 240 ≤ r → r < R + 246 → cc.nreg r = c₁.nreg r) →
      (NoHit S z σ ∨ ∃ tb, FirstHit S z σ tb ∧ t ≤ tb) →
      ∃ c' k, Exec P W (leafAcc R) cc c' k ∧ k = 7 ∧ BestOK P C R c' (S ∪ A) z σ ∧
        FrameB (Bhit R) c c' := by
    intro cc hcc fcc hr hS
    obtain ⟨c', k, ex, hk, a0, a1, a2, a4, a5, a6, a7, fa⟩ := leafAcc_exec (P := P) hR cc hcc
      (by omega)
    refine ⟨c', k, ex, hk, ⟨by rw [a0], fun _ => ⟨t, ?_, ?_, ?_, ?_, ?_⟩, fun h' => absurd a0 h'⟩,
      fcc.trans (fB fa (fun r hr => by
        simp only [decide_eq_true_eq] at hr; exact bhit_range (Or.inl hr)))⟩
    · rcases hS with hS | ⟨tb, htb, hle⟩
      · exact firstHit_union_right hS hA
      · exact firstHit_union_le' htb hA hle
    · rw [a1, a2, hr _ (by omega) (by omega), hr _ (by omega) (by omega), p44, p45]; exact hp
    · rw [a1, hr _ (by omega) (by omega), p44]; exact he
    · rw [a1, a2, hr _ (by omega) (by omega), hr _ (by omega) (by omega), p44, p45]; exact hpos
    · exact absRec_copy rc (by rw [a4, hr _ (by omega) (by omega)])
        (by rw [show R + 24 + 1 = R + 25 by omega, a5, hr _ (by omega) (by omega)])
        (by rw [show R + 24 + 2 = R + 26 by omega, a6, hr _ (by omega) (by omega)])
        (by rw [show R + 24 + 3 = R + 27 by omega, a7, hr _ (by omega) (by omega)])
  have c20 : c₁.nreg (R + 20) = c.nreg (R + 20) := k1 _ (by omega) (by omega)
  have c31 : c₁.nreg (R + 31) = 1 := by rw [k1 _ (by omega) (by omega), h31]
  by_cases hf : c₁.nreg (R + 20) < c₁.nreg (R + 31)
  · -- no minimum yet
    have hno : NoHit S z σ := best₁.2.2 (by omega)
    obtain ⟨c', k, ex, hk, hb, fr⟩ := accept c₁ w₁ f₁' (fun _ _ _ => rfl) (Or.inl hno)
    exact ⟨c', _, .seq e₁ (.ifLtN_true hf ex), by omega, hb, fr⟩
  -- compare with the minimum
  have hf1 : c₁.nreg (R + 20) = 1 := by have := best₁.1; omega
  obtain ⟨tb, htb, hpb, heb, hposb, rb⟩ := best₁.2.1 hf1
  obtain ⟨c₂, k₂, e₂, hk₂, b46, b47, f₂⟩ := leafCmp_exec (P := P) hR c₁ w₁ hG hP3 rc rb
    (by rw [hA1]; omega)
  have k2 : ∀ r, R ≤ r → r < R + 246 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    f₂.1 r (by simp only [Bcmp2, bprim_R' hR h1 (by omega), Bool.or_false, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]; omega)
  have f₂' : FrameB (Bhit R) c c₂ := f₁'.trans (fB f₂ (fun r hr => by
    simp only [Bcmp2, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with (h | h) | h
    · exact bhit_range (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · exact bhit_prim h
    · exact bhit_range (Or.inr (Or.inr h))))
  -- keeping the minimum
  have keep : tb ≤ t → BestOK P C R c₂ (S ∪ A) z σ := fun hle => by
    refine ⟨by rw [k2 _ (by omega) (by omega)]; exact best₁.1, fun _ => ⟨tb, ?_, ?_, ?_, ?_, ?_⟩,
      fun h' => absurd (by rw [k2 _ (by omega) (by omega)]; exact hf1) h'⟩
    · exact firstHit_union_le htb hA hle
    · rw [k2 _ (by omega) (by omega), k2 _ (by omega) (by omega)]; exact hpb
    · rw [k2 _ (by omega) (by omega)]; exact heb
    · rw [k2 _ (by omega) (by omega), k2 _ (by omega) (by omega)]; exact hposb
    · exact absRec_copy rb (k2 _ (by omega) (by omega)) (k2 _ (by omega) (by omega))
        (k2 _ (by omega) (by omega)) (k2 _ (by omega) (by omega))
  have r35 : c₂.nreg (R + 35) = c.nreg (R + 35) := by
    rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega)]
  have r30 : c₂.nreg (R + 30) = 0 := by
    rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega), h30]
  have hr₂ : ∀ r, R + 240 ≤ r → r < R + 246 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    k2 r (by omega) h2
  have w₂ := e₂.wb_right
  have hσ1 : σ = 1 ∨ σ = -1 := by rw [hσ]; unfold dirOf; split_ifs <;> simp
  by_cases hs : c₂.nreg (R + 30) < c₂.nreg (R + 35)
  · -- `σ = 1`: accept iff `xc < xb`
    have hv : c.nreg (R + 6) = 1 := hσb.2.1 (by have := hσb.1; rw [← r35]; omega)
    have hσe : σ = 1 := by rw [hσ]; exact dirOf_eq_one hv
    have ord := ray_lt_iff (p := z) (t := t) (t' := tb) hσ1
    rw [ite_yes _ _ hσe] at ord
    by_cases hb : c₂.nreg (R + 30) < c₂.nreg (R + 246)
    · have hlt : t < tb := ord.2 (b46.2.1 (by have := b46.1; omega))
      obtain ⟨c', k, ex, hk, hbest', fr⟩ := accept c₂ w₂ f₂' hr₂ (Or.inr ⟨tb, htb, hlt.le⟩)
      exact ⟨c', _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_true hs (.ifLtN_true hb ex)))),
        by omega, hbest', fr⟩
    · have hge : tb ≤ t := by
        by_contra hcon
        exact hb (by rw [r30]; have := b46.2.2 (ord.1 (not_le.1 hcon)); omega)
      exact ⟨c₂, _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_true hs (.ifLtN_false hb
        (.skip w₂))))), by omega, keep hge, f₂'⟩
  · -- `σ = -1`: accept iff `xb < xc`
    have hv : c.nreg (R + 6) ≠ 1 := fun h' => hs (by rw [r30, r35]; have := hσb.2.2 h'; omega)
    have hσe : σ ≠ 1 := by rw [hσ, dirOf_ne_one hv]; norm_num
    have ord := ray_lt_iff (p := z) (t := t) (t' := tb) hσ1
    rw [ite_no _ _ hσe] at ord
    by_cases hb : c₂.nreg (R + 30) < c₂.nreg (R + 247)
    · have hlt : t < tb := ord.2 (b47.2.1 (by have := b47.1; omega))
      obtain ⟨c', k, ex, hk, hbest', fr⟩ := accept c₂ w₂ f₂' hr₂ (Or.inr ⟨tb, htb, hlt.le⟩)
      exact ⟨c', _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_false hs (.ifLtN_true hb ex)))),
        by omega, hbest', fr⟩
    · have hge : tb ≤ t := by
        by_contra hcon
        exact hb (by rw [r30]; have := b47.2.2 (ord.1 (not_le.1 hcon)); omega)
      exact ⟨c₂, _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_false hs (.ifLtN_false hb
        (.skip w₂))))), by omega, keep hge, f₂'⟩

end

end ShotList

end Chazelle.Core
