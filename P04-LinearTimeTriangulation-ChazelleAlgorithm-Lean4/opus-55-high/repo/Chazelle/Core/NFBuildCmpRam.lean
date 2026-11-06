module

public import Chazelle.Core.NFBuildRen
public import Chazelle.Core.NFBuildSpec
public import Chazelle.Core.SortRam

/-!
# WP-C (BuildNF), RAM part 1: the direction and key-comparison routines in band `bBuild`

The direction procedure `NFLoc.locDir` and the key decision `WalkKey.cmpPos` of double
identification, renamed into the band `bBuild` by `σ` (`NFBuildRen`):

* `dirR = locDir.ren σ`: the model descriptor at `r40000`, the walk edge in `r40002`; the
  direction code of the edge in `r10502` (`dirR_exec`);
* `cmpR = cmpPos.ren σ`: the query position in `r10500, r10501`, its direction code in `r10502`,
  the compared position in `r10011, r10012`, `r40102 = 1` on entry; the decision `keyDec` in
  `r40102` (`cmpR_exec`).
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK WalkKey NFLoc

@[expose] public section

/-- The direction procedure in band `bBuild`. -/
def dirR : Stmt := Stmt.ren σ locDir

/-- The key decision in band `bBuild`. -/
def cmpR : Stmt := Stmt.ren σ cmpPos

/-- The registers `dirR` writes. -/
def BdirR (r : ℕ) : Bool := Bdir (σ r)

theorem σ_10502 : σ 10502 = 10502 := by decide

/-- **The direction procedure in band `bBuild`.** -/
theorem dirR_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (d : Config)
    (hw : WordsBounded W d) (hDW : d.nreg 40000 + 6 ≤ W)
    (hCW : LocChainWF P W d.nmem (d.nreg 40000)) {M : Model}
    (hM : ModelDescAt d.nmem (d.nreg 40000) (Qof P) M) (he : d.nreg 40002 < M.W.n) :
    ∃ d' k, Exec P W dirR d d' k ∧ k ≤ 5100 ∧ FrameB BdirR d d' ∧
      d'.nreg 10502 = dirCode M (d.nreg 40002) := by
  have hw' : WordsBounded W (cfgRen σ d) := (wordsBounded_ren σ_σ d).2 hw
  obtain ⟨c', k, ex, hk, hfr, hdir⟩ := locDir_ok P W (cfgRen σ d) hw'
    ⟨hG, hW, hDW, hCW, M, hM, he⟩
  refine ⟨cfgRen σ c', k, exec_of_ren σ_σ ex, hk, ⟨fun r hr => ?_, fun r hr => ?_, hfr.2.2.1,
    hfr.2.2.2.1, hfr.2.2.2.2⟩, ?_⟩
  · have := hfr.1 (σ r) hr
    simp only [cfgRen_nreg, σ_σ] at this ⊢
    exact this
  · have := hfr.2.1 (σ r) hr
    simp only [cfgRen, σ_σ] at this ⊢
    exact this
  · rw [cfgRen_nreg, σ_10502, hdir M hM]
    rfl

/-- The registers `cmpR` writes. -/
def BcmpR (r : ℕ) : Bool := decide (10000 ≤ r ∧ r < 10500) || decide (r = 40102)

theorem wr_cmpPos' : wr (fun r => BcmpR (σ r)) cmpPos = true := by decide

theorem wr_cmpR : wr BcmpR cmpR = true := by
  rw [cmpR, wr_ren σ_σ]; exact wr_cmpPos'


/-- **The key decision in band `bBuild`.** -/
theorem cmpR_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (d : Config)
    (hw : WordsBounded W d) (h1 : d.nreg 40102 = 1) (hxn : d.nreg 10501 ≤ P.n) :
    ∃ d' k, Exec P W cmpR d d' k ∧ k ≤ 260 ∧ FrameB BcmpR d d' ∧
      d'.nreg 40102 = (if keyDec (Qof P) P.n ⟨d.nreg 10500, d.nreg 10501⟩ (d.nreg 10502)
        ⟨d.nreg 10011, d.nreg 10012⟩ then 1 else 0) := by
  have hw' : WordsBounded W (cfgRen σ d) := (wordsBounded_ren σ_σ d).2 hw
  obtain ⟨c', k, ex, hk, hr⟩ := cmpPos_exec (P := P) hG hW (cfgRen σ d) hw' h1 hxn
  have ex' := exec_of_ren σ_σ ex
  refine ⟨cfgRen σ c', k, ex', hk, exec_frameB ex' wr_cmpR, ?_⟩
  rw [cfgRen_nreg, show σ 40102 = 50102 by decide, hr]
  rfl

/-! ## Write sets -/

theorem σ_cases (r : ℕ) : (40000 ≤ r ∧ r < 41000 ∧ σ r = r + 10000) ∨
    (50000 ≤ r ∧ r < 51000 ∧ σ r = r - 10000) ∨ (41000 ≤ r ∧ r < 42000 ∧ σ r = r + 49000) ∨
    (90000 ≤ r ∧ r < 91000 ∧ σ r = r - 49000) ∨
    ((r < 40000 ∨ (42000 ≤ r ∧ r < 50000) ∨ (51000 ≤ r ∧ r < 90000) ∨ 91000 ≤ r) ∧ σ r = r) := by
  unfold σ; split_ifs <;> omega

theorem BdirR_true {r : ℕ} (h : BdirR r = true) :
    (10000 ≤ r ∧ r < 10503) ∨ (40030 ≤ r ∧ r < 40100) := by
  unfold BdirR Bdir at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases σ_cases r with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ <;>
    rw [h3] at h <;> omega

theorem BcmpR_true {r : ℕ} (h : BcmpR r = true) : (10000 ≤ r ∧ r < 10500) ∨ r = 40102 := by
  unfold BcmpR at h; simp at h; omega

theorem wr_dirR : wr BdirR dirR = true := by
  rw [dirR, wr_ren σ_σ]
  simp only [BdirR, σ_σ]
  exact wr_locDir

/-! ## One half of the comparison -/

/-- Direction of the query edge `qe`, then the decision of the position `(se, sh)` against the
query `(qe, qh)`: the direction code into `dd`, the decision bit into `dst`. -/
def halfS (qe qh se sh dd dst : ℕ) : Stmt :=
  .seq (.instr (.copyN 40002 qe))
    (.seq dirR (.seq (block [.copyN dd 10502, .copyN 10500 qe, .copyN 10501 qh, .copyN 10011 se,
      .copyN 10012 sh, .constN 40102 1]) (.seq cmpR (.instr (.copyN dst 40102)))))

/-- The registers `halfS` writes (outside its two outputs). -/
def Bhalf (r : ℕ) : Bool :=
  decide (10000 ≤ r ∧ r < 10503) || decide (40000 < r ∧ r < 40103)

/-- The registers `halfS` writes. -/
def BhalfS (dd dst r : ℕ) : Bool := Bhalf r || decide (r = dd) || decide (r = dst)

/-- The write set of `halfS`. -/
theorem wr_halfS {qe qh se sh dd dst : ℕ} : wr (BhalfS dd dst) (halfS qe qh se sh dd dst) = true := by
  have h1 : wr (BhalfS dd dst) dirR = true :=
    wr_mono (fun r hr => by
      rcases BdirR_true hr with h | h <;> simp [BhalfS, Bhalf] <;> omega) wr_dirR
  have h2 : wr (BhalfS dd dst) cmpR = true :=
    wr_mono (fun r hr => by
      rcases BcmpR_true hr with h | h <;> simp [BhalfS, Bhalf] <;> omega) wr_cmpR
  simp only [halfS, wr, block, wrOK, h1, h2, Bool.and_true, Bool.true_and]
  simp [BhalfS, Bhalf]

/-- **One half of the comparison.**  The registers `qe, qh, se, sh, dd, dst` lie in
`42100 … 42199`, the outputs are distinct from each other and from the inputs. -/
theorem halfS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (d : Config)
    (hw : WordsBounded W d) {qe qh se sh dd dst : ℕ}
    (hr : ∀ x ∈ [qe, qh, se, sh, dd, dst], 42100 ≤ x ∧ x < 42200)
    (hdd : dd ∉ [qe, qh, se, sh, dst]) (hdst : dst ∉ [qe, qh, se, sh])
    (hDW : d.nreg 40000 + 6 ≤ W) (hCW : LocChainWF P W d.nmem (d.nreg 40000)) {M : Model}
    (hM : ModelDescAt d.nmem (d.nreg 40000) (Qof P) M) (he : d.nreg qe < M.W.n)
    (hqh : d.nreg qh ≤ P.n) :
    ∃ d' k, Exec P W (halfS qe qh se sh dd dst) d d' k ∧ k ≤ 5400 ∧
      d'.nreg dd = dirCode M (d.nreg qe) ∧
      d'.nreg dst = (if keyDec (Qof P) P.n ⟨d.nreg qe, d.nreg qh⟩ (dirCode M (d.nreg qe))
        ⟨d.nreg se, d.nreg sh⟩ then 1 else 0) ∧
      FrameB (BhalfS dd dst) d d' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hdd hdst
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, ⟨e1, e2⟩, ⟨f1, f2⟩⟩ := hr
  obtain ⟨n1, n2, n3, n4, n5⟩ := hdd
  obtain ⟨m1, m2, m3, m4⟩ := hdst
  -- the edge
  have x₁ := Exec.copyN (P := P) hw 40002 qe
  set d₁ : Config := { d with nreg := upd d.nreg 40002 (d.nreg qe) } with hd₁
  have w₁ : WordsBounded W d₁ := x₁.wb_right
  have r₁ : ∀ r, r ≠ 40002 → d₁.nreg r = d.nreg r := fun r hr => by rw [hd₁]; simp [hr]
  obtain ⟨d₂, k₂, x₂, hk₂, f₂, dir₂⟩ := dirR_exec (P := P) hG hW d₁ w₁
    (by rw [r₁ _ (by omega)]; exact hDW) (by rw [r₁ _ (by omega)]; exact hCW)
    (M := M) (by rw [r₁ _ (by omega)]; exact hM) (by rw [hd₁]; simp; exact he)
  have r₂ : ∀ r, BdirR r = false → d₂.nreg r = d₁.nreg r := f₂.1
  have nb : ∀ r, 42100 ≤ r → BdirR r = false := fun r hr => by
    by_contra h; have := BdirR_true (Bool.not_eq_false _ ▸ h); omega
  have w₂ := x₂.wb_right
  have v : ∀ r, 42100 ≤ r → r < 42200 → d₂.nreg r = d.nreg r := fun r h1 h2 => by
    rw [r₂ r (nb r h1), r₁ r (by omega)]
  rw [show d₁.nreg 40002 = d.nreg qe by rw [hd₁]; simp] at dir₂
  -- the loads
  obtain ⟨d₃, k₃, x₃, hk₃, q⟩ : ∃ d₃ k₃, Exec P W (block [.copyN dd 10502, .copyN 10500 qe,
      .copyN 10501 qh, .copyN 10011 se, .copyN 10012 sh, .constN 40102 1]) d₂ d₃ k₃ ∧ k₃ = 6 ∧
      (d₃.nreg dd = dirCode M (d.nreg qe) ∧ d₃.nreg 10500 = d.nreg qe ∧
        d₃.nreg 10501 = d.nreg qh ∧ d₃.nreg 10011 = d.nreg se ∧ d₃.nreg 10012 = d.nreg sh ∧
        d₃.nreg 40102 = 1 ∧ d₃.nreg 10502 = dirCode M (d.nreg qe) ∧
        ∀ r, r ≠ dd → r ≠ 10500 → r ≠ 10501 → r ≠ 10011 → r ≠ 10012 → r ≠ 40102 →
          d₃.nreg r = d₂.nreg r) ∧ d₃.nmem = d₂.nmem := by
    exec_block
    · omega
    · refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_⟩, rfl⟩ <;>
        simp (disch := omega) only [upd_same, upd_other]
      all_goals first
        | exact dir₂
        | (rw [v _ (by omega) (by omega)])
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := q.1
  have w₃ := x₃.wb_right
  obtain ⟨d₄, k₄, x₄, hk₄, f₄, bit₄⟩ := cmpR_exec (P := P) hG hW d₃ w₃ q6 (by rw [q3]; exact hqh)
  rw [q2, q3, q4, q5, q7] at bit₄
  have w₄ := x₄.wb_right
  have ex : Exec P W (halfS qe qh se sh dd dst) d
      { d₄ with nreg := upd d₄.nreg dst (d₄.nreg 40102) } (1 + (k₂ + (k₃ + (k₄ + 1)))) :=
    x₁.seq (x₂.seq (x₃.seq (x₄.seq (Exec.copyN w₄ dst 40102))))
  have hwr := wr_halfS (qe := qe) (qh := qh) (se := se) (sh := sh) (dd := dd) (dst := dst)
  refine ⟨_, _, ex, by omega, ?_, ?_, exec_frameB ex hwr⟩
  · simp only [upd_other _ _ _ n5]
    rw [f₄.1 _ (by
      unfold BcmpR; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega), q1]
  · simp only [upd_same]
    rw [bit₄]

/-! ## Descriptors survive changes of memory above them -/

/-- A host layout depends only on the memory below its end. -/
theorem hostAt_agree {m m' : ℕ → ℕ} {B E : ℕ} {H : Host} (h : HostAt m B H)
    (hE : B + 3 * H.length + 4 ≤ E) (hm : ∀ a, a < E → m' a = m a) : HostAt m' B H := by
  refine ⟨by rw [hm _ (by omega)]; exact h.1, fun i hi => ?_⟩
  have hh := h.2 i hi
  have e1 := hm (B + 1 + 3 * i) (by omega)
  have e2 := hm (B + 2 + 3 * i) (by omega)
  have e3 := hm (B + 3 + 3 * i) (by omega)
  generalize H.getD i (.run 0 0) = it at hh ⊢
  cases it with
  | run a l => obtain ⟨h1, h2, h3⟩ := hh; exact ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩
  | pt x =>
    cases x with
    | vtx j => obtain ⟨h1, h2⟩ := hh; exact ⟨e1.trans h1, e2.trans h2⟩
    | onEdge e hh' => obtain ⟨h1, h2, h3⟩ := hh; exact ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩

/-- **A well-formed model descriptor survives every change of memory at or above its bound.** -/
theorem desc_agree {P : Polygon} {E : ℕ} {m m' : ℕ → ℕ} {D : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hM : ModelDescAt m D (Qof P) M)
    (hm : ∀ a, a < E → m' a = m a) : ModelDescAt m' D (Qof P) M ∧ ModelDescWF P E m' D := by
  have hD := hwf.1
  have e0 := hm D (by omega)
  rcases hM with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, hbit, rfl⟩
  · obtain ⟨hC6, hCW⟩ := hwf.2 h0
    obtain ⟨hl, hwfH, hHE, hs⟩ := hCW H C hC
    obtain ⟨hH, hP, h2, h3, h4, h5⟩ := hC
    have e1 := hm (D + 1) (by omega)
    have hH' : HostAt m' (m' (D + 1)) H := by
      rw [e1]; exact hostAt_agree hH (by omega) hm
    have hC' : ChainDescAt m' (D + 1) (Qof P) H C :=
      ⟨hH', hP, by rw [hm _ (by omega)]; exact h2, by rw [hm _ (by omega)]; exact h3,
        by rw [hm _ (by omega)]; exact h4, by rw [hm _ (by omega)]; exact h5⟩
    refine ⟨Or.inl ⟨by rw [e0]; exact h0, H, C, hC', rfl⟩, hD, fun _ => ⟨hC6, fun H' C' hC'' => ?_⟩⟩
    have hHH := hostAt_unique hC''.1 hC'.1
    subst hHH
    have hCC := chain_eq_of_desc hC'' hC'
    subst hCC
    exact ⟨hl, hwfH, by rw [e1]; exact hHE, hs⟩
  · refine ⟨Or.inr ⟨by rw [e0]; exact h1, by rw [hm _ (by omega)]; exact hbit, rfl⟩, hD,
      fun h0 => absurd (e0.symm.trans h0) (by omega)⟩


end

end BuildRam

end Chazelle.Core
