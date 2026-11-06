module

public import Chazelle.MacT
public import Chazelle.Core.NFDecompBfs
public import Mathlib.Data.List.GetD
public import Chazelle.Programs.Tactics
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.SpecNF
public import Chazelle.Core.FactsAttach

namespace Chazelle.Core
@[expose] public section
namespace ShootCut
def pad (m : ℕ → ℕ) (A Z : ℕ) : ℕ → ℕ := fun a => if a < A then m a else Z
theorem pad_lt {m : ℕ → ℕ} {A Z a : ℕ} (h : a < A) : pad m A Z a = m a := ite_eq_left h
theorem pad_ge {m : ℕ → ℕ} {A Z a : ℕ} (h : A ≤ a) : pad m A Z a = Z := ite_eq_right by_omega
theorem robust_pad {A : ℕ} {m : ℕ → ℕ} {Φ : ztjx → Prop} (h : Robust A m Φ) (Z : ℕ) :
    Φ ztrui := h _ fun _ ha => pad_lt ha
variable {O : OracleIface} {P : Polygon} {m : ℕ → ℕ} {h A : ℕ}

/-- The address of the entry `(g, i)`. -/
def entryAddr (m : ℕ → ℕ) (h g i : ℕ) : ℕ := m ztwjz + 3 * i

/-- **The grade table lies below its bound** (handle words, powers of two, halving table). -/
theorem grade_low (hR : Robust A m fun m' => GradeRaw O P m' h A) :
    h + 3 < A ∧ (∀ j, j ≤ topGrade P.n + 1 → m ztgn + 2 + j < A) ∧
      (∀ x, x ≤ P.n → m ztbba + x < A) := by
  -- the handle `h` itself
  have hh : ztpox := by
    zuhbt
    have := (robust_pad hR ztegi).1
    zuimc

  have h1 : ztsir := by
    zuhbt
    have := (robust_pad hR (A + P.n + 1)).2.1.1
    rw [pad_ge (show A ≤ h + 1 by omega), pad_ge (show A ≤ A + P.n + 1 by omega)] at this
    omega
  have h3 : ztsit := by
    zuhbt
    have := (robust_pad hR ztbo).2.2.1 0 ztbg
    rw [pad_ge (show A ≤ h + 3 by omega), pad_ge (show A ≤ A + 1 + 0 by omega)] at this
    omega
  refine ⟨h3, fun j hj => ?_, fun x hx => ?_⟩
  · zuhbt
    have := ((robust_pad hR (2 ^ j + 1)).2.1.2.2.1 j hj).1
    rw [pad_lt h1, pad_ge (show A ≤ m ztgn + 2 + j by omega)] at this
    omega
  · zuhbt
    have := (robust_pad hR (x / 2 + 1)).2.2.1 x hx
    rw [pad_lt (show h + 3 < A by omega), pad_ge (show A ≤ m ztbba + x by omega)] at this
    omega

/-- **The grade context carries a halving table** (finding R-D3). -/
theorem gradeCtx_halves (O : OracleIface) : (gradeCtx O).Halves := by
  intro P m g A hh
  obtain ⟨h1, -, h3⟩ := grade_low hh
  exact ⟨h1, fun x hx => ⟨h3 x hx, hh.holds.2.2.1 x hx⟩⟩

/-- **The entries lie below the bound**: the row word, the entry and its three words. -/
theorem grade_entry (hR : Robust A m fun m' => GradeRaw O P m' h A) {g i : ℕ} (hg : g < m h)
    (hi : i < gradeCount P.n g) :
    h + 2 < A ∧ m zteu + g < A ∧ entryAddr m h g i + 2 < A := by
  have hh : ztpox := by
    zuhbt
    have := (robust_pad hR ztegi).1
    zuimc

  -- a descriptor whose words are all the padding value `Z > n` is impossible
  have key : ∀ Z, A ≤ Z → P.n < Z → ∀ D, A ≤ D →
      ¬ (∃ (H : Host) (C : Chain), ChainDescAt ztrui D zta H C ∧
        C.m = gradeLen P.n g i) := by
    rintro Z hZA hZn D hD ⟨H, C, hC, hm⟩
    have e2 := hC.2.2.2.1
    rw [pad_ge by_omega] at e2
    have : gradeLen P.n g i ≤ P.n := by unfold gradeLen; omega
    omega
  have h2 : ztsis := by
    zucuw

    obtain ⟨H, C, N, hC, -, -, -, -, -, hm, -⟩ := (robust_pad hR Z).2.2.2 g i
      ztdmb hi
    zueca
    simp only [pad_ge (show A ≤ h + 2 by omega)]
    rw [pad_ge (show A ≤ Z + g by omega), pad_ge ztkxl]
    omega
  have hr : ztzjl := by
    zucuw

    obtain ⟨H, C, N, hC, -, -, -, -, -, hm, -⟩ := (robust_pad hR Z).2.2.2 g i
      ztdmb hi
    zueca
    rw [pad_lt h2, pad_ge (show A ≤ m zteu + g by omega), pad_ge ztkxl]
    omega
  have hE : entryAddr m h g i < A := by
    zucuw

    obtain ⟨H, C, N, hC, -, -, -, -, -, hm, -⟩ := (robust_pad hR Z).2.2.2 g i
      ztdmb hi
    zueca
    unfold entryAddr at hA
    rw [pad_lt h2, pad_lt hr, pad_ge (show A ≤ m ztwjz + 3 * i by omega)]
    omega
  -- the descriptor word is below the bound (`ChainWF`)
  obtain ⟨H₀, C₀, N₀, -, hwf₀, -⟩ := hR.holds.2.2.2 g i hg hi
  have hD : m ztqmm + 5 ≤ A := by unfold entryAddr; exact hwf₀.1
  have hE2 : entryAddr m h g i + 2 < A := by
    zuhbt
    set Z := A + m ztqmm + 1
    obtain ⟨H, C, N, -, -, -, -, -, -, -, -, -, -, e1, -⟩ := (robust_pad hR Z).2.2.2 g i
      ztdmb hi
    have eE : m ztwjz + 3 * i = entryAddr m h g i := rfl
    rw [pad_lt h2, pad_lt hr, eE, pad_ge (show A ≤ entryAddr m h g i + 2 by omega),
      pad_ge (show A ≤ Z by omega), pad_lt hE] at e1
    omega
  omega
end ShootCut
open Set Filter Topology
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (rayHit rayHitSet rayHit_union hitParam_eq_rayHit FreeAt shoot)
namespace Sweep
theorem firstHit_unique {A : Set Point} {p : Point} {σ t t' : ℝ} (h : FirstHit A p σ t)
    (h' : FirstHit A p σ t') : t = t' := by
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd h.2.1 (h'.2.2 t h.1 hlt)
  · omega
  · exact absurd h'.2.1 (h.2.2 t' h'.1 hgt)
variable {A B : Set Point} (C : Chain)
/-- A first hit on `B` that lies in `A ⊆ B` is the first hit on `A`. -/
theorem firstHit_of_subset (hAB : A ⊆ B) {p : Point} {σ t : ℝ}
    (h : FirstHit B p σ t) (ht : rayPt p σ t ∈ A) : FirstHit A p σ t :=
  ⟨h.1, ht, fun t' h1 h2 hA => h.2.2 t' h1 h2 (hAB hA)⟩

/-- The answer of one shooter call: a first hit at `t` (`some t`) or no hit (`none`). -/
def FirstHitOpt (A : Set Point) (p : Point) (σ : ℝ) : Option ℝ → Prop
  | some t => FirstHit A p σ t
  | none => NoHit A p σ

/-- The minimum of two optional parameters (`none` is `+∞`). -/
noncomputable def omin : Option ℝ → Option ℝ → Option ℝ
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, b => b

/-- **First hit on a union**: the answer for `A ∪ B` is the minimum of the answers. -/
theorem firstHitOpt_union {p : Point} {σ : ℝ} {a b : Option ℝ}
    (ha : FirstHitOpt A p σ a) (hb : FirstHitOpt B p σ b) :
    FirstHitOpt ztbgp p σ (omin a b) := by
  cases a with
  | none =>
    cases b with
    | none =>
      zujbo
      zucov
      · tauto
      · tauto
    | some tb =>
      refine ⟨hb.1, Or.inr hb.2.1, fun t' h1 h2 hmem => ?_⟩
      zucov
      · tauto
      · exact hb.2.2 t' h1 h2 h
  | some ta =>
    cases b with
    | none =>
      refine ⟨ha.1, Or.inl ha.2.1, fun t' h1 h2 hmem => ?_⟩
      zucov
      · exact ha.2.2 t' h1 h2 h
      · tauto
    | some tb =>
      show FirstHit ztbgp p σ (min ta tb)
      refine ⟨lt_min ha.1 hb.1, ?_, fun t' h1 h2 hmem => ?_⟩
      · rcases min_choice ta tb with h | h
        · zvmwc; exact Or.inl ha.2.1
        · zvmwc; exact Or.inr hb.2.1
      · zucov
        · exact ha.2.2 t' h1 (lt_of_lt_of_le h2 ztff) h
        · exact hb.2.2 t' h1 (lt_of_lt_of_le h2 ztgh) h

/-! ## The union of the two chains of a junction -/

/-- **The first hit of `C` below its top**: the earlier of the slit-free first hits of `C₁` and
`C₂` (inside the common box). -/
theorem whole_hitParam_eq_min (J : Merge.Junction) {z : Point} (hz : z.2 ≤ J.whole.top.2)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    J.whole.hitParam z σ =
      min (rayHit J.whole.radius J.left.set z σ) (rayHit J.whole.radius J.right.set z σ) := by
  rw [hitParam_eq_rayHit _ hz, J.whole_set, rayHit_union _ _ _ _ hσ]

/-- Below the top of `C₁`, its slit-free first hit is the first hit in the model of `C₁`. -/
theorem left_hitParam_eq (J : Merge.Junction) {z : Point} (hz : z.2 ≤ J.left.top.2) (σ : ℝ) :
    rayHit J.whole.radius J.left.set z σ = J.left.hitParam z σ :=
  (hitParam_eq_rayHit J.left hz σ).symm

/-- Below the top of `C₂`, its slit-free first hit is the first hit in the model of `C₂`. -/
theorem right_hitParam_eq (J : Merge.Junction) {z : Point} (hz : z.2 ≤ J.right.top.2) (σ : ℝ) :
    rayHit J.whole.radius J.right.set z σ = J.right.hitParam z σ :=
  (hitParam_eq_rayHit J.right hz σ).symm

/-- **Above the top of a chain the ray never meets it**: the slit-free first hit is the exit
from the box. -/
theorem rayHit_eq_empty_of_above (C : Chain) {z : Point} (hz : C.top.2 < z.2) (r σ : ℝ) :
    rayHit r C.set z σ = rayHit r ∅ z σ := by
  unfold rayHit
  zucr
  zufso
  simp only [rayHitSet, mem_ofPred_eq, mem_empty_iff_false, or_false]
  constructor
  · rintro ⟨ht, h | h⟩
    · simp_all
    · have := C.snd_le_top_of_mem_set h
      zueze

  simp_all

/-- **Freeness for the union**: below the top of `C`, a direction is free for `C` iff the
initial part of the ray stays in the box and off both chains. -/
theorem freeAt_whole_iff (J : Merge.Junction) {z : Point} (hz : z.2 ≤ J.whole.top.2) (σ : ℝ) :
    FreeAt J.whole z σ ↔ ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ Chain.box J.whole.radius ∧
      rayPt z σ t ∉ J.left.set ∧ rayPt z σ t ∉ J.right.set := by
  unfold FreeAt
  have key : ∀ t, rayPt z σ t ∈ J.whole.dom ↔ rayPt z σ t ∈ Chain.box J.whole.radius ∧
      rayPt z σ t ∉ J.left.set ∧ rayPt z σ t ∉ J.right.set := by
    zujbn
    have h := Merge.not_mem_dom_iff J.whole (p := rayPt z σ t) by_simp_all
    zukpk
    grind
  simp_all

/-- **The first hit of a chain as a first hit on the complement of its domain**: for a free
direction below the top, the ray first leaves the domain at `C.hitParam z σ`. -/
theorem firstHit_compl_dom {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (h : FreeAt C z σ) : FirstHit C.domᶜ z σ ztbtm := by
  obtain ⟨h1, h2, h3⟩ := Merge.hit_of_freeAt C hz hσ h
  exact ⟨h1, h2, fun t ht1 ht2 hmem => hmem (h3 t ht1 ht2)⟩

/-- **The first hit of a chain on any part of the complement of its domain** containing the
first-hit point is at the first-hit parameter. -/
theorem firstHit_of_compl_dom {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (h : FreeAt C z σ) {A : Set Point} (hA : A ⊆ C.domᶜ)
    (hmem : rayPt z σ ztbtm ∈ A) : FirstHit A z σ ztbtm :=
  firstHit_of_subset hA (firstHit_compl_dom C hz hσ h) hmem
end Sweep
open Chazelle.Machine (Stmt)

/-- **WP-D: the sweep, with height-coded queries** (`SweepSpec` plus the query height condition). -/
def SweepSpecH : Prop :=
  ∃ (mk : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ)
    (X : MemCtx) (Ok : Polygon → Model → Prop), X.CapLocal → Bs ⊆ oracleBands →
    ShooterOK sh Bs F X Ok →
    Meets ztkbc ztdwg
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P c.nmem ztefy ztm ∧
        rd c bSweep 5 ≤ X.cap P c.nmem ztefy ∧ rd c bSweep 7 ≤ 1 ∧
        JunctionWF P ztm c.nmem ztcds ztcdt ztcdu ∧
        ∃ H J N₁ N₂ L, JunctionAt c.nmem ztcds ztcdt ztcdu
            zta H J ∧
          J.P.Simple ∧
          Ok P ztbw ∧ Ok P ztj ∧
          NFWithin c.nmem ztwb ztm N₁ ∧
          NFWithin c.nmem ztrl ztm N₂ ∧
          IsNF ztbw zta N₁ ∧ IsNF ztj zta N₂ ∧
          (chainModel J.left).DegLe ztwjx ztbwd ∧
          (chainModel J.right).DegLe ztwis ztbwd ∧
          (chainModel J.left).Semigranular ztwjx ztbro ∧
          (chainModel J.right).Semigranular ztwis ztbro ∧
          rd c bSweep 9 = L.length ∧ rd c bSweep 8 + 3 * L.length ≤ c.nreg ALLOC ∧
          ChordListAt c.nmem ztiae L ∧
          ztybp ∧
          (rd c bSweep 7 = 1 → ∃ L₁ : List zte, L = sweepEndQ N₂.chords ++ L₁ ∧
            L₁.length ≤ 3) ∧
          ∀ q ∈ L, ((chainModel ztzxx).pos zta ztpo).2 =
            ((Qof P).vtx zteut).2)
      (fun P c c' => ∀ H J (L : List zte),
        JunctionAt c.nmem ztcds ztcdt ztcdu zta H J →
        rd c bSweep 9 = L.length → ChordListAt c.nmem ztiae L →
        ∃ R : List ztpl, c.nreg ALLOC ≤ rd c' bSweep 11 ∧
          rd c' bSweep 11 + 4 * L.length ≤ c'.nreg ALLOC ∧ R.length = L.length ∧
          ResultListAt c'.nmem ztrvs R ∧
          ∀ j, j < L.length →
            SeesInWhole J zta ztdae ztwzi ztxkj)
      (fun _ c => κ ztbwd *
        ztwqz *
        (F ztbro +
          Nat.clog 2 ztwqz + 1))
end
namespace DownMath
@[expose] public section
open Merge (Junction)

/-! ## Host polygons -/
variable (Q : Polygon) (n : ℕ) (H₁ H₂ : Host) (a ℓ : ℕ) {x N j : ℕ}
theorem host_poly_n (H : Host) : (H.poly Q).n = (H.pts Q.n).length := by
  zulad

/-- The vertices of the host polygon are the evaluated host points. -/
theorem host_poly_vtx (H : Host) {i : ℕ} (hi : i < (H.pts Q.n).length) :
    (H.poly Q).vtx i = ((H.pts Q.n).getD i ztga).eval Q := by
  zumra
theorem pts_append : (H₁ ++ H₂).pts n = H₁.pts n ++ H₂.pts n := by
  zujnh
theorem pts_cons (it : HostItem) (H : Host) :
    Host.pts n (it :: H) = it.pts n ++ H.pts n := by
  rfl
theorem run_pts_length (n a ℓ : ℕ) : ((HostItem.run a ℓ).pts n).length = ℓ + 1 := by
  zumpk
theorem run_pts_getD (n a ℓ : ℕ) {k : ℕ} (hk : k ≤ ℓ) :
    ((HostItem.run a ℓ).pts n).getD k ztga = .vtx ztxyt := by
  zulaj

/-- **The points of a run item inside a host.** -/
theorem pts_append_run {k : ℕ} (hk : k ≤ ℓ) :
    ((H₁ ++ HostItem.run a ℓ :: H₂).pts n).getD ((H₁.pts n).length + k) ztga =
      .vtx ztxyt := by
  rw [pts_append, pts_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right by_omega,
    Nat.add_sub_cancel_left, List.getElem?_append_left (by rw [run_pts_length]; omega),
    ← List.getD_eq_getElem?_getD, run_pts_getD n a ℓ hk]
theorem pts_append_run_length :
    (H₁.pts n).length + ℓ + 1 ≤ ((H₁ ++ HostItem.run a ℓ :: H₂).pts n).length := by
  rw [pts_append, pts_cons, List.length_append, List.length_append, run_pts_length]
  omega

/-! ## M-M1 -/

/-- The vertex `k` of a chain of a host polygon is the evaluated host point at index
`(s + k) mod N`. -/
theorem chain_vertex_host {Q : Polygon} {H : Host} {C : Chain} (hP : C.P = H.poly Q) (k : ℕ) :
    C.vertex k = ((H.pts Q.n).getD (zttw % (H.pts Q.n).length) ztga).eval Q := by
  have hn := C.n_pos
  rw [hP, host_poly_n] at hn
  zugil
  rw [hP, host_poly_n, host_poly_vtx Q H zthp]

/-- **M-M1.**  If the host points at the three junction positions (the shared vertex of `J` and
its two neighbours) are vertices of `Q` with pairwise distinct indices, distinct heights give
`SharedGeneric J`. -/
theorem sharedGeneric_of_vtx {Q : Polygon} (hdh : DistinctHeights Q) {H : Host} {J : Junction}
    (hP : J.P = H.poly Q) {a b c : ℕ} (ha : a < Q.n) (hb : b < Q.n) (hc : c < Q.n)
    (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c)
    (hu : (H.pts Q.n).getD (zthax % (H.pts Q.n).length) ztga = .vtx a)
    (hv : (H.pts Q.n).getD (ztnlw % (H.pts Q.n).length) ztga = .vtx b)
    (hw : (H.pts Q.n).getD (ztztq % (H.pts Q.n).length) ztga = .vtx c) :
    SharedGeneric J := by
  have hP' : J.whole.P = H.poly Q := hP
  have eU : sharedU J = Q.vtx a := by
    unfold sharedU; rw [chain_vertex_host hP', show J.whole.s = J.s from rfl, hu]; rfl
  have eV : sharedV J = Q.vtx b := by
    unfold sharedV; rw [chain_vertex_host hP', show J.whole.s = J.s from rfl, hv]; rfl
  have eW : sharedW J = Q.vtx c := by
    unfold sharedW; rw [chain_vertex_host hP', show J.whole.s = J.s from rfl, hw]; rfl
  zusk
  · rw [eU, eV]; tauto
  · rw [eW, eV]; exact hdh c b hc hb hcb
  · rw [eU, eW]; tauto

/-- Small distinct offsets give distinct residues. -/
theorem add_mod_ne {n x i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    (x + i) % n ≠ (x + j) % n := by
  zuq
  have h' : i % n = j % n := Nat.ModEq.add_left_cancel' x h
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h'
  omega

/-- `(x + 1) mod N = j ≥ 1` gives `x mod N = j - 1`. -/
theorem mod_pred (hN : 0 < N) (h : zthf % N = j) (hj : 1 ≤ j) :
    x % N = j - 1 := by
  rw [Nat.add_mod] at h
  have hlt := Nat.mod_lt x hN
  rcases Nat.lt_or_ge 1 N with h1 | h1
  · zvnnn at h
    rcases Nat.lt_or_ge (x % N + 1) N with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h; omega
    · rw [show x % N + 1 = N by omega, Nat.mod_self] at h; omega
  grind

/-- `x mod N = j` with `j + 1 < N` gives `(x + 1) mod N = j + 1`. -/
theorem mod_succ (h : x % N = j) (hj : j + 1 < N) : zthf % N = j + 1 := by
  rw [Nat.add_mod, h, Nat.mod_eq_of_lt (show 1 < N by omega), Nat.mod_eq_of_lt hj]

/-- **M-M1, run form (padding rule M2).**  If the host is `H₁ ++ run a ℓ :: H₂` and the shared
vertex of `J` is the host point `k` of the run with `1 ≤ k < ℓ` (so both host neighbours are
points of the same run, i.e. three consecutive vertices of `Q`), then `SharedGeneric J`. -/
theorem sharedGeneric_run {Q : Polygon} (hn : 3 ≤ Q.n) (hdh : DistinctHeights Q)
    {H₁ H₂ : Host} {a ℓ k : ℕ} {J : Junction} (hP : J.P = (H₁ ++ HostItem.run a ℓ :: H₂).poly Q)
    (hk1 : 1 ≤ k) (hkl : k < ℓ)
    (hj : ztnlw % J.P.n = (H₁.pts Q.n).length + k) : SharedGeneric J := by
  set H := H₁ ++ HostItem.run a ℓ :: H₂ with hH
  set N := (H.pts Q.n).length with hN
  have hPn : J.P.n = N := by rw [hP, host_poly_n]
  rw [hPn] at hj
  have hlen : (H₁.pts Q.n).length + ℓ + 1 ≤ N := pts_append_run_length Q.n H₁ H₂ a ℓ
  zumeb
  have hu : zthax % N = (H₁.pts Q.n).length + ztie := by
    have e : J.s + J.m₁ = zthax + 1 := by_omega
    zvmwe at hj
    rw [mod_pred by_omega hj by_omega]; omega
  have hw : ztztq % N = (H₁.pts Q.n).length + zts := by
    rw [← add_assoc, mod_succ hj by_omega]; omega
  have hv : ztnlw % N = (H₁.pts Q.n).length + k := hj
  zufvu
  have e1 : a + ztie + 1 = a + k := by_omega
  have e2 : a + ztie + 2 = a + zts := by_omega
  have d1 := add_mod_ne (x := a + ztie) ztimc ztpdq
    (by omega : (0 : ℕ) ≠ 1)
  have d2 := add_mod_ne (x := a + ztie) ztpdr ztpdq
    (by omega : (2 : ℕ) ≠ 1)
  have d3 := add_mod_ne (x := a + ztie) ztimc ztpdr
    (by omega : (0 : ℕ) ≠ 2)
  rw [add_zero, e1] at d1
  zvmws at d2
  rw [add_zero, e2] at d3
  refine sharedGeneric_of_vtx hdh hP ztjkl ztjkl
    ztjkl d1 d2 d3 ?_ ?_ ?_
  · rw [hu]; exact pts_append_run Q.n H₁ H₂ a ℓ by_omega
  · zvmyq; exact pts_append_run Q.n H₁ H₂ a ℓ by_omega
  · zunft; exact pts_append_run Q.n H₁ H₂ a ℓ by_omega
end
end DownMath
namespace DrvR
@[expose] public section
def chunks (C : ℕ) (s a L : ℕ) : List zte :=
  if L = 0 then [] else if L ≤ C ∨ C = 0 then [ztqvx]
  else ztqvw :: chunks C ztkee ztjnt zthbe
termination_by L
decreasing_by omega

/-- The leaves of a run item `.run a ℓ` at host offset `p`: the interior points `1 … ℓ - 1`,
split at the wrap-around of the `Q` indices. -/
def runLeaves (n C p a ℓ : ℕ) : List zte :=
  if ℓ < 3 then [] else
    if ztdf % n + ztdit ≤ n - 1 then chunks C ztr ztwwo ztdit
    else chunks C ztr ztwwo ztwqo ++
      chunks C ztbajv 0 ztbajw

/-- The leaves of a host whose first point has offset `p`. -/
def hostLeaves (n C : ℕ) : ℕ → Host → List zte
  | _, [] => []
  | p, .run a ℓ :: H => runLeaves n C p a ℓ ++ hostLeaves n C ztkbv H
  | p, .pt _ :: H => hostLeaves n C ztr H

/-! ## Chunks -/
theorem chunks_zero (C s a : ℕ) : chunks C s a 0 = [] := by
  rw [chunks]; simp
variable {C s a L : ℕ}
theorem chunks_le (h0 : L ≠ 0) (h : L ≤ C ∨ C = 0) :
    chunks C s a L = [ztqvx] := by
  rw [chunks, ite_eq_right h0, ite_eq_left h]
theorem chunks_gt (h0 : L ≠ 0) (h : C < L) (hC : C ≠ 0) :
    chunks C s a L = ztqvw :: chunks C ztkee ztjnt zthbe := by
  rw [chunks, ite_eq_right h0, ite_eq_right by_omega]

/-- The pieces of a segment: inside it, nonempty, at most `C` edges, `Q` start shifted like the
host start. -/
theorem mem_chunks {C : ℕ} (hC : 1 ≤ C) : ∀ (L s a : ℕ) (x : ℕ × ℕ × ℕ), x ∈ chunks C s a L →
    s ≤ x.1 ∧ x.1 + x.2.1 ≤ s + L ∧ 1 ≤ x.2.1 ∧ x.2.1 ≤ C ∧ x.2.2 + s = a + x.1 := by
  zumgg
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro s a x hx
    zujsh
    · rw [h0, chunks_zero] at hx; simp_all
    zujto
    · rw [chunks_le h0 ztvca] at hx
      grind
    · rw [chunks_gt h0 by_omega by_omega] at hx
      grind

/-- The number of pieces of a segment. -/
theorem chunks_length {C : ℕ} (hC : 1 ≤ C) : ∀ (L s a : ℕ), (chunks C s a L).length * C ≤ L + C - 1 := by
  zumgg
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro s a
    zujsh
    · rw [h0, chunks_zero]; simp
    zujto
    · rw [chunks_le h0 ztvca]; grind
    · rw [chunks_gt h0 by_omega by_omega]
      have := ih zthbe by_omega ztkee ztjnt
      simp only [List.length_cons, Nat.succ_mul]
      omega

/-! ## Leaves of a run -/

/-- **A leaf of the run item `.run a ℓ` at host offset `q`**: strictly inside the run, nonempty,
at most `C` edges, no wrap-around, and its `Q` start is the run vertex at its host start. -/
def LeafIn (n C q a ℓ : ℕ) (x : ℕ × ℕ × ℕ) : Prop :=
  q + 1 ≤ x.1 ∧ x.1 + x.2.1 + 1 ≤ q + ℓ ∧ 1 ≤ x.2.1 ∧ x.2.1 ≤ C ∧ x.2.2 + x.2.1 + 1 ≤ n ∧
    x.2.2 = (a + (x.1 - q)) % n

/-- A piece of a segment of the run interior is a leaf. -/
theorem leafIn_of_seg {n C p a ℓ s0 u L : ℕ} (hC : 1 ≤ C) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ chunks C s0 u L) (hs0 : p + 1 ≤ s0) (hend : s0 + L + 1 ≤ p + ℓ)
    (hnu : u + L + 1 ≤ n) (hmod : u = (a + zttzt) % n) : LeafIn n C p a ℓ x := by
  obtain ⟨h1, h2, h4, h5, h6⟩ := mem_chunks hC _ _ _ x hx
  refine ⟨by_omega, by_omega, h4, h5, by_omega, ?_⟩
  have e : x.2.2 = u + ztued := by_omega
  rw [e, show a + (x.1 - p) = a + zttzt + ztued by omega, ← Nat.mod_add_mod, ← hmod,
    Nat.mod_eq_of_lt by_omega]
theorem mem_runLeaves {n C p a ℓ : ℕ} (hC : 1 ≤ C) (hn : 1 ≤ n) (hℓ : ℓ < n) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ runLeaves n C p a ℓ) : LeafIn n C p a ℓ x := by
  zuiao
  have hq := Nat.mod_add_div ztdf n
  unfold runLeaves at hx
  split_ifs at hx with h3 hw
  · simp_all
  · exact leafIn_of_seg hC hx ztbhw by_omega by_omega
      by_simp
  · zuoy
    · exact leafIn_of_seg hC hx ztbhw by_omega by_omega
        by_simp
    · refine leafIn_of_seg hC hx by_omega by_omega by_omega ?_
      rw [show a + (p + 1 + ztwkq - p) = 0 + n * (ztdf / n + 1) by
        rw [Nat.mul_add, Nat.mul_one]; omega, Nat.add_mul_mod_self_left, Nat.zero_mod]

/-! ## Leaves of a host -/
theorem mem_hostLeaves {n C : ℕ} (hC : 1 ≤ C) (hn : 1 ≤ n) : ∀ (H : Host) (p : ℕ),
    HostWF n H → ∀ x ∈ hostLeaves n C p H, ∃ H₁ a ℓ H₂, H = H₁ ++ HostItem.run a ℓ :: H₂ ∧
      LeafIn n C ztoeb a ℓ x
  | [], p, _, x, hx => by_tauto
  | .run a ℓ :: H, p, hwf, x, hx => by
    rw [hostLeaves, List.mem_append] at hx
    have hit := hwf (.run a ℓ) (List.mem_cons_self ..)
    zujpe
    zufhg
    zuky
    · exact ⟨[], a, ℓ, H, rfl, by simpa [Host.pts] using mem_runLeaves hC hn hit.2 hx⟩
    · obtain ⟨H₁, a', ℓ', H₂, e, hL⟩ := mem_hostLeaves hC hn H ztkbv hwf' x hx
      refine ⟨HostItem.run a ℓ :: H₁, a', ℓ', H₂, by_simp_all, ?_⟩
      zunhn
      grind
  | .pt y :: H, p, hwf, x, hx => by
    rw [hostLeaves] at hx
    zufhg
    obtain ⟨H₁, a', ℓ', H₂, e, hL⟩ := mem_hostLeaves hC hn H ztr hwf' x hx
    refine ⟨HostItem.pt y :: H₁, a', ℓ', H₂, by_simp_all, ?_⟩
    zuojm
    rwa [show ((HostItem.pt y).pts n).length = 1 from rfl,
      show p + (1 + (H₁.pts n).length) = p + 1 + (H₁.pts n).length by omega]
end
end DrvR
namespace FuseAsm
@[expose] public section
open Chazelle.Merge (lend rend FreeAt shoot freeAt_vertex shoot_vertex)
theorem getD_lt {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  simp_all
variable (J : Merge.Junction)

/-- The chords of `C` shot from the queries `Z` whose direction is free. -/
def shots (Z : Set ztdgb) : Set ztf :=
  {d | ∃ x ∈ Z, FreeAt J.whole x.1 x.2 ∧ d = shoot J.whole x.1 x.2}
theorem shots_union (Z Z' : Set ztdgb) : shots J (Z ∪ Z') = shots J Z ∪ shots J Z' := by
  zufsm
  simp only [shots, Set.mem_union, Set.mem_ofPred_eq]
  grind

/-- Queries whose direction is not free contribute nothing: dropping them keeps the shots. -/
theorem shots_eq_of {Z Z' : Set ztdgb} (hsub : Z ⊆ Z')
    (hfree : ∀ x ∈ Z', FreeAt J.whole x.1 x.2 → x ∈ Z) : shots J Z = shots J Z' := by
  zufsm
  constructor
  · rintro ⟨x, hx, hf, rfl⟩; exact ⟨x, hsub hx, hf, rfl⟩
  · rintro ⟨x, hx, hf, rfl⟩; exact ⟨x, hfree x hx hf, hf, rfl⟩

/-- The chord-end queries of a family. -/
def endQ (S : Set ztf) : Set ztdgb :=
  {x | ∃ c ∈ S, x = (lend c, 1)} ∪ {x | ∃ c ∈ S, x = (rend c, -1)}

/-- The vertex queries at vertex `k` of `C`. -/
def vtxQ (k : ℕ) : Set ztdgb := {(J.whole.vertex k, 1), (J.whole.vertex k, -1)}

/-- The vertex queries at the tops of `C₁` and `C₂`. -/
def topQ : Set ztdgb := vtxQ J J.left.topIdx ∪ vtxQ J ztrw

/-- The cap query. -/
def capQ : Set ztdgb := {x | SharedExtremum J ∧ x = (capOrigin J, capDir J)}
theorem shots_vtxQ (k : ℕ) :
    shots J (vtxQ J k) = {d | ∃ σ : ℝ, ztdd ∧ J.whole.DirFree k σ ∧
      d = J.whole.chordSet k σ} := by
  zufsm
  simp only [shots, vtxQ, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hf, rfl⟩
    zudsl
    · tauto
    · exact ⟨-1, Or.inr rfl, (freeAt_vertex _ _ _).1 hf, (shoot_vertex _ _ _)⟩
  · rintro ⟨σ, hσ | hσ, hf, rfl⟩ <;> subst hσ
    · tauto
    · exact ⟨_, Or.inr rfl, (freeAt_vertex _ _ _).2 hf, (shoot_vertex _ _ _).symm⟩
theorem shared_eq_shots : J.sharedChords = shots J ztuda := by
  rw [shots_vtxQ]; rfl
theorem top_eq_shots : topChords J = shots J (topQ J) := by
  rw [topQ, shots_union, shots_vtxQ, shots_vtxQ]
  zufsm
  simp only [topChords, topIdxs, Finset.mem_insert, Finset.mem_singleton, Set.mem_union,
    Set.mem_ofPred_eq]
  simp
theorem cap_eq_shots : capChords J = shots J (capQ J) := by
  zufsm
  simp only [capChords, shots, capQ, Set.mem_ofPred_eq]
  simp
variable (S₁ S₂ : Set (Set Point))
theorem fusion_eq_shots :
    J.fusion S₁ S₂ = shots J (endQ ztbzc) ∪ shots J ztuda := by
  rw [← shared_eq_shots, endQ, shots_union]
  zufsm
  simp only [Merge.Junction.fusion, shots, Set.mem_union, Set.mem_ofPred_eq]
  simp

/-- **The fused family as a set of shots.** -/
theorem fused_eq_shots :
    J.fusion S₁ S₂ ∪ glueChords J =
      shots J (endQ ztbzc ∪ vtxQ J J.m₁ ∪ topQ J ∪ capQ J) := by
  rw [fusion_eq_shots, glueChords, top_eq_shots, cap_eq_shots, shots_union, shots_union,
    shots_union]
  ac_rfl

/-! ## The answers of the sweep -/

/-- The triples of the answers with flag `1`. -/
def collect (R : List ztpl) : List zte :=
  (R.filter (fun r => r.1 == 1)).map (fun r => r.2)

/-- The geometric queries of a query list of side `i`. -/
def geoQ (Q : Polygon) (i : ℕ) (L : List zte) : Set ztdgb :=
  {x | ∃ q ∈ L, x = ((chainModel ztgi).pos Q ⟨q.1, q.2.1⟩, dirOf q.2.2)}
end
end FuseAsm
namespace Restore
@[expose] public section
open Chazelle.Machine (Stmt Exec)

/-- **An execution of cost `0` changes nothing.** -/
theorem exec_zero {P : Polygon} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hk : k = 0) : c' = c := by
  induction h with
  | skip _ => rfl
  | instr _ _ _ _ => omega
  | seq _ _ ih₁ ih₂ =>
    rw [ih₂ by_omega, ih₁ by_omega]
  | ifLtN_true _ _ _ => omega
  | ifLtN_false _ _ _ => omega
  | ifLtR_true _ _ _ => omega
  | ifLtR_false _ _ _ => omega
  | whileLtN_false _ _ => omega
  | whileLtN_true _ _ _ _ _ => omega
  | whileLtR_false _ _ => omega
  | whileLtR_true _ _ _ _ _ => omega

/-- **The arc-cutter costs at least one step**: from any configuration meeting its
precondition (with room), `1 ≤ G γ`. -/
theorem cutter_cost_pos {cu : Stmt} {B : Finset ℕ} {G H : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (h : CutterOK cu B G H X Ok) {P : Polygon} {W : ℕ}
    {c : Config} (hw : WordsBounded W c)
    (hpre : GoodEnv P ∧ hostWords P.n ≤ W ∧ X.holds P c.nmem zthzu ztm ∧
      rd c bCut 9 ≤ X.cap P c.nmem zthzu ∧
      ModelDescWF P ztm c.nmem ztfub ∧
      ∃ M, ModelDescAt c.nmem ztfub zta M ∧ Ok P M ∧
        ProperPos M zta P.n ztbgi ∧
        ProperPos M zta P.n ztxu ∧
        rd c bCut 1 < M.W.n ∧ rd c bCut 3 < M.W.n ∧
        ztxrd ∧
        ztxre ∧
        M.arcWt ztzua
          ztzub ≤ rd c bCut 9)
    (hroom : c.nreg ALLOC + G ztbit ≤ W) : 1 ≤ G ztbit := by
  obtain ⟨c', k, -, -, hpost, -⟩ := h P W c hw hpre hroom
  obtain ⟨M, hM, -⟩ := hpre.2.2.2.2.2
  obtain ⟨-, -, hq, hq1, -⟩ := hpost M hM
  omega

/-- The configuration `c` with the hit-flag register of the shooter set to `v`. -/
def withFlag (c : Config) (v : ℕ) : Config :=
  { c with nreg := upd c.nreg (bandReg bShoot 10) v }
variable (c : Config) (v : ℕ)
theorem withFlag_rd {i : ℕ} (hi : i ≠ 10) (_hi' : i < 10000) :
    rd ztmb bShoot i = rd c bShoot i := by
  unfold rd withFlag bandReg
  simp_all
theorem withFlag_flag : rd ztmb bShoot 10 = v := by
  rfl
theorem withFlag_alloc : (withFlag c v).nreg ALLOC = c.nreg ALLOC := by
  rfl
theorem withFlag_originIn (o : Origin) :
    OriginIn ztmb ztbpu o ↔ OriginIn c ztbpu o := by
  rfl
theorem withFlag_wb {W : ℕ} {c : Config} (hw : WordsBounded W c) {v : ℕ} (hv : v ≤ W) :
    WordsBounded W ztmb := by
  obtain ⟨h1, h2⟩ := hw
  refine ztpfj
  unfold withFlag
  zubi
  zujgy
  grind

/-- **The ray-shooter costs at least one step**: from any configuration meeting its
precondition (with room), `1 ≤ F γ`. -/
theorem shooter_cost_pos {sh : Stmt} {B : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (h : ShooterOK sh B F X Ok) {P : Polygon} {W : ℕ}
    {c : Config} (hw : WordsBounded W c)
    (hpre : GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c.nmem ztefx ztm ∧
      rd c bShoot 9 ≤ X.cap P c.nmem ztefx ∧
      ModelDescWF P ztm c.nmem ztbrn ∧
      (c.nmem ztbrn = 0 → ∀ H C, ChainDescAt c.nmem ztfih zta H C →
        HostRegular (Qof P).n H) ∧
      ∃ M, ModelDescAt c.nmem ztbrn zta M ∧ Ok P M ∧
        ProperPos M zta P.n ztnp ∧
        ProperPos M zta P.n ztnq ∧
        rd c bShoot 1 < M.W.n ∧ rd c bShoot 3 < M.W.n ∧
        ztwwl ∧
        ztwwm ∧
        M.arcWt ztwwa
          ztwwb ≤ rd c bShoot 9 ∧
        ∃ o : Origin, o.Lt P.n M ∧ OriginIn c ztbpu o ∧
          (ztbnv ∨ (M.InnerPt ztwle ∧
            ∀ x, o = .walk x → ProperPos M zta P.n x)) ∧
          o.eval M zta ∉ M.arcSet ztwwa
            ztwwb)
    (hroom : c.nreg ALLOC + F ztcdr ≤ W) : 1 ≤ F ztcdr := by
  by_contra hF
  have hF0 : F ztcdr = 0 := by_omega
  obtain ⟨hG, hWh, hX, hcap, hwf, hreg, M, hM, hOk, hp1, hp2, he1, he2, hi1, hi2, hwt, o, hoLt,
    hoIn, hoK, hoA⟩ := hpre
  have hW1 : ztbla := le_trans ztdmm hWh
  have r : ∀ v i, i ≠ 10 → i < 10000 → rd ztmb bShoot i = rd c bShoot i :=
    fun v i h1 h2 => withFlag_rd c v h1 h2
  -- run the shooter from `c` with flag `v`
  have run : ∀ v, v ≤ 1 → ∃ c', c' = withFlag c v ∧
      (∀ M' (o' : Origin), ModelDescAt c.nmem ztbrn zta M' →
        OriginIn c ztbpu o' →
        (rd c' bShoot 10 = 1 → ∃ t, FirstHit (M'.arcSet (M'.key zta ⟨rd c bShoot 1,
            rd c bShoot 2⟩) (M'.key (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩))
          ztzxj ztbqc t) ∧
        (rd c' bShoot 10 ≠ 1 → NoHit (M'.arcSet (M'.key zta ⟨rd c bShoot 1,
            rd c bShoot 2⟩) (M'.key (Qof P) ⟨rd c bShoot 3, rd c bShoot 4⟩))
          ztzxj ztbqc)) := by
    zuml
    have hwv := withFlag_wb hw (le_trans hv hW1)
    have pre' : GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P (withFlag c v).nmem ztznu
          ztmzw ∧
        rd ztmb bShoot 9 ≤ X.cap P (withFlag c v).nmem ztznu ∧
        ModelDescWF P ztmzw (withFlag c v).nmem
          ztxop ∧
        ((withFlag c v).nmem ztxop = 0 → ∀ H C,
          ChainDescAt (withFlag c v).nmem (rd ztmb bShoot 0 + 1) zta H C →
          HostRegular (Qof P).n H) ∧
        ∃ M, ModelDescAt (withFlag c v).nmem ztxop zta M ∧ Ok P M ∧
          ProperPos M zta P.n ztxep ∧
          ProperPos M zta P.n ztwvj ∧
          rd ztmb bShoot 1 < M.W.n ∧ rd ztmb bShoot 3 < M.W.n ∧
          (rd ztmb bShoot 2 = 0 ∨
            M.InnerPt (M.pos zta ztxep)) ∧
          (rd ztmb bShoot 4 = 0 ∨
            M.InnerPt (M.pos zta ztwvj)) ∧
          M.arcWt (M.key zta ztxep)
            ztbarh ≤
              rd ztmb bShoot 9 ∧
          ∃ o : Origin, o.Lt P.n M ∧ OriginIn ztmb ztbpu o ∧
            (ztbnv ∨ (M.InnerPt ztwle ∧
              ∀ x, o = .walk x → ProperPos M zta P.n x)) ∧
            o.eval M zta ∉ M.arcSet (M.key zta ⟨rd ztmb bShoot 1,
              rd ztmb bShoot 2⟩)
              ztbarh := by
      simp only [r v 0 by_decide by_decide, r v 1 by_decide by_decide,
        r v 2 by_decide by_decide, r v 3 by_decide by_decide,
        r v 4 by_decide by_decide, r v 9 by_decide by_decide,
        r v 13 by_decide by_decide, withFlag_alloc, withFlag_originIn]
      exact ⟨hG, hWh, hX, hcap, hwf, hreg, M, hM, hOk, hp1, hp2, he1, he2, hi1, hi2, hwt, o, hoLt,
        hoIn, hoK, hoA⟩
    obtain ⟨c', k, ex, hk, hpost, -⟩ := h P W ztmb hwv pre'
      by_tauto
    beta_reduce at hk
    rw [r v 9 by_decide by_decide, hF0] at hk
    have hc' := exec_zero ex by_omega
    refine ⟨c', hc', fun M' o' hM' ho' => ?_⟩
    have hM'' : ModelDescAt (withFlag c v).nmem ztxop zta M' := by
      tauto
    have ho'' : OriginIn ztmb ztbpu o' := (withFlag_originIn c v o').2 ho'
    grind
  obtain ⟨c₁, rfl, h₁⟩ := run 1 le_rfl
  obtain ⟨c₀, rfl, h₀⟩ := run 0 by_omega
  obtain ⟨t, ht0, htA, -⟩ := (h₁ M o hM hoIn).1 (withFlag_flag c 1)
  exact (h₀ M o hM hoIn).2 by_positivity t ht0 htA
end
end Restore
namespace Setup
open Machine Machine.Stmt Programs
@[expose] public section
variable {P : Polygon} {W : ℕ} {n : ℕ} (c0 c : Config) {α : Type} {p : Prop}
/-- `whileLtN` with a bounded body cost `B`, a strictly decreasing measure `μ`, and a quantity
`Ψ` growing by at most the cost of each iteration: the whole loop lets `Ψ` grow by at most its
cost. -/
theorem whileLtN_acc {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (μ : Config → ℕ) (B : ℕ) (Ψ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ k ≤ B ∧ μ c' < μ c ∧ Ψ c' ≤ Ψ c + k)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ zthb * μ c + 2 ∧ Ψ c' ≤ Ψ c + k := by
  induction hn : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · obtain ⟨c₁, k₁, hb, hI₁, hk₁, hμ, hΨ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂, hΨ'⟩ := ih ztgne by_omega hI₁ rfl
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', ?_, by_omega⟩
      have : zthb * ztcec ≤ zthb * n := Nat.mul_le_mul_left _ by_omega
      grind
    · zulfw

/-! ## Arithmetic -/

/-- `⌈i/5⌉ = (i + 4) / 5`. -/
theorem ceilBeta_eq (i : ℕ) : Cost.ceilBeta i = ztetg / 5 := by
  zumqp
  rw [Cost.beta_eq]
  zudmc
  · zumlu
    have h : i ≤ 5 * ztzzn := by_omega
    have h' : (i : ℝ) ≤ 5 * ((ztetg / 5 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  · rcases Nat.eq_zero_or_pos ztzzn with h0 | hpos
    · omega
    · have hlt : ztetg / 5 - 1 < ⌈(1 / 5 : ℝ) * i⌉₊ := by
        rw [Nat.lt_ceil]
        have h : 5 * ztzhr < i := by_omega
        have h' : ((5 * ztzhr : ℕ) : ℝ) < i := by exact_mod_cast h
        grind
      omega

/-- `2^p ≤ 2 n` for the top grade `p` (`n ≥ 1`). -/
theorem pow_topGrade_le (hn : 1 ≤ n) : 2 ^ topGrade n ≤ 2 * n := by
  zuhrf
  rcases Nat.eq_zero_or_pos ztzul with h0 | hpos
  · grind
  · have hlt : 2 ^ ztzck < n - 1 :=
      (Nat.lt_clog_iff_pow_lt by_norm_num).mp by_omega
    have : 2 ^ Nat.clog 2 ztkl = 2 * 2 ^ ztzck := by
      zufac
    omega

/-- `p < 2 n` for the top grade `p` (`n ≥ 1`). -/
theorem topGrade_lt (hn : 1 ≤ n) : topGrade n < 2 * n :=
  lt_of_lt_of_le (Nat.lt_two_pow_self) (pow_topGrade_le hn)

/-! ## The program -/

/-- Constants and the start of the doubling loop. -/
def initS : Stmt :=
  block [.inputSize 20000, .constN 20001 1, .constN 20009 5, .constN 20013 2,
    .subN 20002 20000 20001, .constN 20003 1, .constN 20004 0]

/-- The doubling loop: afterwards `20004` holds `p` and `20003` holds `2^p`. -/
def loopA : Stmt :=
  .whileLtN 20003 20002 (block [.addN 20003 20003 20003, .addN 20004 20004 20001])

/-- The header `n, p` at `S = ALLOC`, the allocator bumped by two, the table pointers and the
loop registers initialised. -/
def headerS : Stmt :=
  block [.copyN 20012 9999, .storeN 20012 20000, .addN 20010 20012 20001, .storeN 20010 20004,
    .addN 9999 9999 20013, .addN 20010 20010 20001, .addN 20011 20010 20004,
    .addN 20011 20011 20013, .constN 20003 1, .constN 20005 0, .constN 20007 0,
    .constN 20008 0, .addN 20006 20004 20013]

/-- One table entry: store `2^i` and `⌈i/5⌉`, advance. -/
def bodyB : Stmt :=
  .seq (block [.storeN 20010 20003, .storeN 20011 20007, .addN 20003 20003 20003,
      .addN 20010 20010 20001, .addN 20011 20011 20001, .addN 9999 9999 20013,
      .addN 20005 20005 20001])
    (.seq (.ifLtN 20008 20001 (block [.addN 20007 20007 20001, .addN 20008 20008 20009]) .skip)
      (block [.subN 20008 20008 20001]))

/-- The table loop, `i = 0 … p + 1`. -/
def loopB : Stmt := .whileLtN 20005 20006 bodyB

/-- The handle into `coreReg 0`. -/
def finS : Stmt := block [.copyN 230000 20012]

/-- **The setup program.** -/
def prog : Stmt := .seq initS (.seq loopA (.seq headerS (.seq loopB finS)))

/-! ## Invariants -/

/-- The setup frame relative to the entry configuration `c0`: registers outside band `2`,
`coreReg 0` and the allocator, the real files, the output and the memory below the entry
allocator are unchanged. -/
def SFr (c0 c : Config) : Prop :=
  (∀ r, (r < 20000 ∨ 30000 ≤ r) → r ≠ 9999 → r ≠ 230000 → c.nreg r = c0.nreg r) ∧
    c.rreg = c0.rreg ∧ c.rmem = c0.rmem ∧ c.output = c0.output ∧
    ∀ a, a < c0.nreg 9999 → c.nmem a = c0.nmem a

/-- The invariant of the doubling loop. -/
def InvA (W n : ℕ) (c0 c : Config) : Prop :=
  WordsBounded W c ∧ SFr c0 c ∧ c.nreg 9999 = c0.nreg 9999 ∧ c.nmem = c0.nmem ∧
    c.nreg 20000 = n ∧ c.nreg 20001 = 1 ∧ c.nreg 20002 = n - 1 ∧ c.nreg 20009 = 5 ∧
    c.nreg 20013 = 2 ∧ c.nreg 20003 = 2 ^ c.nreg 20004 ∧ c.nreg 20004 ≤ topGrade n

/-- The invariant of the table loop (record base `S`). -/
def InvB (W n S : ℕ) (c0 c : Config) : Prop :=
  WordsBounded W c ∧ SFr c0 c ∧ S = c0.nreg 9999 ∧
    c.nreg 20000 = n ∧ c.nreg 20001 = 1 ∧ c.nreg 20009 = 5 ∧ c.nreg 20013 = 2 ∧
    c.nreg 20004 = topGrade n ∧ c.nreg 20012 = S ∧ c.nreg 20006 = topGrade n + 2 ∧
    c.nreg 20005 ≤ topGrade n + 2 ∧ c.nreg 20003 = 2 ^ c.nreg 20005 ∧
    c.nreg 20010 = S + 2 + c.nreg 20005 ∧ c.nreg 20011 = S + topGrade n + 4 + c.nreg 20005 ∧
    c.nreg 20007 = ztlko / 5 ∧
    c.nreg 20008 + c.nreg 20005 = 5 * (ztlko / 5) ∧
    c.nreg 9999 = S + 2 + 2 * c.nreg 20005 ∧
    c.nmem S = n ∧ c.nmem ztbgu = topGrade n ∧
    ∀ j, j < c.nreg 20005 →
      c.nmem (S + 2 + j) = 2 ^ j ∧ c.nmem (S + topGrade n + 4 + j) = (j + 4) / 5

/-! ## The pieces -/

/-- The initial block. -/
theorem initS_spec (c : Config) (hc : WordsBounded W c) (hW : P.n + 5 ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k = 7 ∧ InvA W P.n c c' ∧ c'.nreg 20004 = 0 := by
  zujqm
  exec_block
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · refine ⟨rfl, ⟨by_omega, ⟨fun r hr h1 h2 => ?_, rfl, rfl, rfl, by_simp_all⟩, rfl, rfl,
      by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      by simp, by_simp⟩, by config_simp⟩
    zup

/-- The doubling loop computes the top grade. -/
theorem loopA_spec (hI : InvA W P.n c0 c)
    (hq0 : c.nreg 20004 = 0) (hn : 1 ≤ P.n) (hW : 2 * P.n ≤ W) :
    ∃ c' k, Exec P W loopA c c' k ∧ k ≤ 4 * topGrade P.n + 2 ∧ InvA W P.n c0 c' ∧
      c'.nreg 20004 = topGrade P.n := by
  zullb
  obtain ⟨c', k, he, hI', ht, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 20003) (b := 20002)
    (body := block [.addN 20003 20003 20003, .addN 20004 20004 20001]) (InvA W P.n c0)
    (fun c => topGrade P.n - c.nreg 20004) 2 ztcvf (fun c h htest => by
      obtain ⟨hw, hfr, hA, hm, h0, h1, h2, h9, h13, h3, h4⟩ := h
      have hlt : c.nreg 20004 < topGrade P.n := by
        zuhrf
        rw [Nat.lt_clog_iff_pow_lt by_norm_num]
        omega
      have hpow : 2 ^ ztrlt ≤ 2 ^ topGrade P.n := Nat.pow_le_pow_right by_norm_num hlt
      have hpow' : 2 ^ ztrlt = 2 ^ c.nreg 20004 + 2 ^ c.nreg 20004 := by
        omega
      have hq : c.nreg 20004 < 2 ^ c.nreg 20004 := Nat.lt_two_pow_self
      exec_block
      · omega
      · config_simp; omega
      · obtain ⟨hr, hrr, hrm, ho, hmem⟩ := hfr
        refine ⟨⟨by_omega, ⟨fun r hr' h1' h2' => ?_, hrr, hrm, ho, hmem⟩, hA, hm, by_simp_all,
          by simp_all, by_simp_all, by_simp_all,
          by simp_all, ?_, ?_⟩, by_omega, ?_⟩
        · zufpj
        · simp_all
        · simp_all
        · config_simp; omega) hI
  refine ⟨c', k, he, by_omega, hI', ?_⟩
  obtain ⟨-, -, -, -, -, -, h2, -, -, h3, h4⟩ := hI'
  refine le_antisymm h4 ?_
  zuhrf
  zudwq
  omega

/-- The header block starts the table loop. -/
theorem headerS_spec (hI : InvA W P.n c0 c)
    (hp : c.nreg 20004 = topGrade P.n) (hW : c0.nreg 9999 + 2 * topGrade P.n + 6 ≤ W) :
    ∃ c' k, Exec P W headerS c c' k ∧ k = 13 ∧ InvB W P.n (c0.nreg 9999) c0 c' ∧
      c'.nreg 20005 = 0 := by
  obtain ⟨hw, ⟨hr, hrr, hrm, ho, hmem⟩, hA, hm, h0, h1, h2, h9, h13, h3, h4⟩ := hI
  unfold headerS
  exec_block
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · omega
  · omega
  · omega
  · omega
  · config_simp; omega
  · refine ⟨rfl, ⟨by_omega, ⟨fun r hr' h1' h2' => ?_, hrr, hrm, ho, fun a ha => ?_⟩, rfl,
      by tauto, by_tauto, by_tauto,
      by tauto, by_tauto, by_tauto,
      by simp_all, by_simp, by_simp,
      by config_simp; omega, by config_simp; omega,
      by config_simp, by config_simp, by config_simp; omega,
      ?_, ?_, fun j hj => by_simp_all⟩, by config_simp⟩
    · zufpj
    · config_simp
      rw [hA, h1, hp]
      zup
      zucjq
    · simp_all
    simp_all

/-- An `if` with a false condition. -/
theorem iteF [Decidable p] (h : ¬ p) (a b : α) :
    ztfhz = b := by zumxk

/-- An `if` with a true condition. -/
theorem iteT [Decidable p] (h : p) (a b : α) :
    ztfhz = a := by zumxk

/-- The table-loop invariant after one iteration, from the effect of the body. -/
theorem bodyB_post {W n S : ℕ} {c0 c c' : Config} (hI : InvB W n S c0 c)
    (hw' : WordsBounded W c')
    (hreg : ∀ r, r ≠ 20003 → r ≠ 20010 → r ≠ 20011 → r ≠ 9999 → r ≠ 20005 → r ≠ 20007 →
      r ≠ 20008 → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output)
    (hmem : c'.nmem = upd (upd c.nmem (c.nreg 20010) (c.nreg 20003)) (c.nreg 20011) (c.nreg 20007))
    (hlt : c.nreg 20005 < topGrade n + 2)
    (h3 : c'.nreg 20003 = c.nreg 20003 + c.nreg 20003)
    (h10 : c'.nreg 20010 = c.nreg 20010 + 1) (h11 : c'.nreg 20011 = c.nreg 20011 + 1)
    (hA : c'.nreg 9999 = c.nreg 9999 + 2) (h5 : c'.nreg 20005 = c.nreg 20005 + 1)
    (h7 : c'.nreg 20007 = ztrlv / 5)
    (h8 : c'.nreg 20008 + c.nreg 20005 + 1 = 5 * (ztrlv / 5)) :
    InvB W n S c0 c' := by
  obtain ⟨hw, ⟨hr, hrr0, hrm0, ho0, hmem0⟩, hS, g0, g1, g9, g13, g4, g12, g6, gi, g3, g10, g11,
    g7, g8, gA, gm0, gm1, gmj⟩ := hI
  have hmem' : ∀ a, c'.nmem a = if a = S + topGrade n + 4 + c.nreg 20005 then ztlko / 5
      else if a = S + 2 + c.nreg 20005 then 2 ^ c.nreg 20005 else c.nmem a := by
    zumgj
    rw [hmem, Machine.upd_apply, Machine.upd_apply, g11, g10, g7, g3]
  refine ⟨hw', ⟨fun r h1 h2 h3' => ?_, hrr.trans hrr0, hrm.trans hrm0, ho.trans ho0,
    fun a ha => ?_⟩, hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hreg r by_omega by_omega by_omega h2 by_omega by_omega by_omega]
    grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · omega
  · grind
  · omega
  · omega
  · omega
  · omega
  · omega
  · grind
  · grind
  · zun
    rw [h5] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [hmem', hmem', iteF by_omega, iteF by_omega, iteF by_omega,
        iteF by_omega]
      grind
    · subst hj
      grind

/-- One iteration of the table loop. -/
theorem bodyB_spec {W S : ℕ} (c0 c : Config) (hI : InvB W P.n S c0 c)
    (ht : c.nreg 20005 < c.nreg 20006) (hn : 1 ≤ P.n) (hW : S + 8 * P.n + 9 ≤ W) :
    ∃ c' k, Exec P W bodyB c c' k ∧ InvB W P.n S c0 c' ∧ k ≤ 11 ∧
      topGrade P.n + 2 - c'.nreg 20005 < topGrade P.n + 2 - c.nreg 20005 ∧
      c'.nreg 9999 ≤ c.nreg 9999 + k := by
  have hI0 := hI
  obtain ⟨hw, -, -, g0, g1, g9, g13, g4, g12, g6, gi, g3, g10, g11, g7, g8, gA, -, -, -⟩ := hI
  have hlt : c.nreg 20005 < topGrade P.n + 2 := by_omega
  zullb
  have hpl := topGrade_lt hn
  have hpow : 2 ^ ztrlu ≤ 2 ^ ztegi :=
    Nat.pow_le_pow_right by_norm_num by_omega
  have hpow2 : 2 ^ ztegi = 4 * 2 ^ topGrade P.n := by_grind
  have hpow' : 2 ^ ztrlu = 2 ^ c.nreg 20005 + 2 ^ c.nreg 20005 := by
    omega
  unfold bodyB
  refine spec_seq ?_
  exec_block
  · grind
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · by_cases hT : c.nreg 20008 < 1
    · zujl
      zuek
      exec_block
      · config_simp; omega
      · config_simp; omega
      · refine ⟨bodyB_post hI0 ‹_› ztjwe rfl rfl rfl ?_ hlt
          (by config_simp) (by config_simp; rw [g1]) (by config_simp; rw [g1])
          (by config_simp; rw [g13]) (by config_simp; rw [g1]) ?_ ?_, by_omega, ?_, ?_⟩
        · config_simp; simp (disch := omega) only [Machine.upd_other]
        · config_simp
        · config_simp; omega
        · config_simp; omega
        · config_simp; omega
        · config_simp; omega
    · zujl
      zudx
      zurc
      exec_block
      refine ⟨bodyB_post hI0 ‹_› ztjwe rfl rfl rfl ?_ hlt
        (by config_simp) by_simp_all by_simp_all
        by_simp_all by_simp_all ?_ ?_, by_omega, ?_, ?_⟩
      · simp_all
      · config_simp
      · config_simp; omega
      · config_simp; omega
      · config_simp; omega
      simp_all

/-- The table loop writes both tables. -/
theorem loopB_spec {W S : ℕ} (c0 c : Config) (hI : InvB W P.n S c0 c)
    (hi : c.nreg 20005 = 0) (hn : 1 ≤ P.n) (hW : S + 8 * P.n + 9 ≤ W) :
    ∃ c' k, Exec P W loopB c c' k ∧ k ≤ 13 * ztegi + 2 ∧ InvB W P.n S c0 c' ∧
      c'.nreg 20005 = topGrade P.n + 2 ∧ c'.nreg 9999 ≤ c.nreg 9999 + k := by
  obtain ⟨c', k, he, hI', ht, hk, hΨ⟩ := whileLtN_acc (P := P) (a := 20005) (b := 20006)
    (body := bodyB) (InvB W P.n S c0) (fun c => topGrade P.n + 2 - c.nreg 20005) 11
    ztqnj ztcvf
    (fun c h htest => bodyB_spec c0 c h htest hn hW) hI
  refine ⟨c', k, he, by_omega, hI', ?_, hΨ⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, h6, hle, -⟩ := hI'
  omega

/-! ## The specification -/

/-- **WP-L: the setup phase meets `SetupSpec`** with the program `Setup.prog` and the constant
`κ = 64`. -/
theorem prog_meets : SetupSpec := by
  refine ⟨prog, 64, ?_⟩
  intro P W c hw ⟨hge, _hn3⟩ hroom
  have hn := hge.1.1
  zuhp
  have hc0 : coreReg 0 = 230000 := rfl
  zvnek at hroom
  have hpl := topGrade_lt (by omega : 1 ≤ P.n)
  obtain ⟨c1, k1, e1, hk1, hI1, hq1⟩ := initS_spec c hw (P := P) by_nlinarith
  obtain ⟨c2, k2, e2, hk2, hI2, hq2⟩ := loopA_spec c c1 hI1 hq1 by_omega by_nlinarith
  have hA2 := hI2.2.2.1
  obtain ⟨c3, k3, e3, hk3, hI3, hi3⟩ := headerS_spec c c2 hI2 hq2 by_nlinarith
  have hA3 : c3.nreg 9999 = c.nreg 9999 + 2 := by
    have := hI3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    omega
  obtain ⟨c4, k4, e4, hk4, hI4, hi4, hΨ⟩ := loopB_spec c c3 hI3 hi3 by_omega by_nlinarith
  obtain ⟨hw4, ⟨hr, hrr, hrm, ho, hmem⟩, -, -, -, -, -, -, g12, -, -, -, -, -, -, -, gA, gm0,
    gm1, gmj⟩ := hI4
  have e5c := Exec.copyN (P := P) hw4 230000 20012
  have e5 : Exec P W finS c4 { c4 with nreg := upd c4.nreg 230000 _ } 1 :=
    Exec.block_cons e5c (Exec.block_nil e5c.wb_right)
  refine ⟨_, k1 + (k2 + (k3 + ztfsx)), e1.seq (e2.seq (e3.seq (e4.seq e5))), by_nlinarith,
    ?_, ?_⟩
  · rw [hAL, hc0]
    simp only [Machine.upd_same, ne_eq, not_false_eq_true, Machine.upd_other,
      Nat.reduceEqDiff]
    rw [g12, gA, hi4]
    zucng
    have hr' := hm
    refine ⟨?_, ?_, fun i hi => ?_, by_omega⟩
    · grind
    · grind
    · rw [hr' _ by_omega, hr' _ by_omega, ceilBeta_eq]
      grind
  · refine ⟨fun r hr1 hr2 => ?_, by_simp_all, by_simp_all,
      by simp_all,
      ho, ?_, ?_⟩
    · simp only [phaseBands, bandOf, Finset.mem_Icc, not_and_or, not_le] at hr1
      zvnek at hr2
      zup
      grind
    · zummm
      zup
      omega
    · zummm
      zup
      omega
end
end Setup
public section

/-- **WP-L (proved)**: the setup phase (`Setup.prog`, constant `κ = 64`). -/
theorem setupSpec : SetupSpec := Setup.prog_meets
end
namespace DownMath
@[expose] public section
def cntG (A B x : ℕ) : ℕ := 2 * A * x + A + 2 * A * B + 8 * A * B * x

/-- The threshold exponent: `8 A ≤ 2^L` and `32 A B ≤ 2^L`. -/
def cntL (A B : ℕ) : ℕ := Nat.clog 2 (8 * A + 32 * A * B)

/-- The threshold level `λ*`: from it on the levels contract. -/
def cntLam (A B : ℕ) : ℕ := 5 * (5 * cntL A B + 16)

/-- The count constant above the threshold (`2520` covers the transition). -/
def cntBase (A B : ℕ) : ℕ := 8 * A * B + A + 2520

/-- **The count bound of level `λ`** (the `cnt` of (I3)). -/
def cnt (A B lam : ℕ) : ℕ :=
  if cntLam A B ≤ lam then cntBase A B else ztdue^[cntLam A B - lam] ztjsv

/-- The bound on all count constants. -/
def cntMax (A B : ℕ) : ℕ := ztdue^[cntLam A B] ztjsv
variable {A : ℕ}
theorem le_cntG (hA : 1 ≤ A) (B x : ℕ) : x ≤ cntG A B x := by
  have : x ≤ 2 * A * x := by
    calc x = 1 * x := (one_mul x).symm
      _ ≤ 2 * A * x := Nat.mul_le_mul_right _ by_omega
  unfold cntG; omega
theorem iterate_le_iterate (hA : 1 ≤ A) (B x : ℕ) {k k' : ℕ} (h : k ≤ k') :
    ztdue^[k] x ≤ ztdue^[k'] x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  rw [add_comm k d, Function.iterate_add_apply]
  generalize ztdue^[k] x = y
  induction d with
  | zero => simp
  | succ d ih =>
    zudtl
    exact ih.trans (le_cntG hA B _)
theorem cntBase_le_cnt (hA : 1 ≤ A) (B lam : ℕ) : cntBase A B ≤ cnt A B lam := by
  unfold cnt
  split_ifs
  · omega
  · zujvc

/-- **The count constants are bounded.** -/
theorem cnt_le_cntMax (hA : 1 ≤ A) (B lam : ℕ) : cnt A B lam ≤ cntMax A B := by
  unfold cnt cntMax
  split_ifs
  · zujvc
  · exact iterate_le_iterate hA B _ ztjkm

/-! ## The threshold -/
theorem le_two_pow_cntL (A B : ℕ) : 8 * A + 32 * A * B ≤ 2 ^ cntL A B :=
  Nat.le_pow_clog by_norm_num _

/-- **Contraction above the threshold**: with `b = ⌈βλ⌉`, `b' = ⌈β(b + 11)⌉`,
`8 A 2^b' ≤ 2^b` and `32 A B ≤ 2^b`. -/
theorem big_of_ge {A B lam : ℕ} (h : cntLam A B ≤ lam) :
    8 * A * 2 ^ Cost.ceilBeta ztblw ≤ 2 ^ Cost.ceilBeta lam ∧
      32 * A * B ≤ 2 ^ Cost.ceilBeta lam := by
  have hL := le_two_pow_cntL A B
  set L := cntL A B
  rw [Setup.ceilBeta_eq lam, Setup.ceilBeta_eq]
  unfold cntLam at h
  set b := zttru / 5 with hb
  have hbL : 5 * L + 16 ≤ b := by_omega
  have hb' : (b + 11 + 4) / 5 + L ≤ b := by_omega
  have hpow : 2 ^ ztflt * 2 ^ L ≤ 2 ^ b := by
    zunvh; exact Nat.pow_le_pow_right by_norm_num hb'
  have hLb : 2 ^ L ≤ 2 ^ b := Nat.pow_le_pow_right by_norm_num by_omega
  constructor
  · calc 8 * A * 2 ^ ztflt ≤ 2 ^ L * 2 ^ ztflt :=
          Nat.mul_le_mul_right _ by_omega
      _ ≤ 2 ^ b := by_grind
  · omega

/-! ## One level -/

/-- **The arithmetic of one level.**  From (I3) `K 2^b ≤ c (2^p + 2^b)` and the level bound
`K' G ≤ A ((K + 1) G + B (n + 4 K))` with `2^b' ≤ G`: (I3) `K' 2^b' ≤ c' (2^p + 2^b')` holds
either for `c' ≥ cntG A B c`, or for `c' = c` in the contracting case. -/
theorem step_arith {p b b' K K' n c c' A B G : ℕ}
    (hK : K * 2 ^ b ≤ c * ztele) (hb : b ≤ p) (hb' : b' ≤ b) (hn : n ≤ 2 ^ p + 1)
    (hG : 2 ^ b' ≤ G) (hK' : K' * G ≤ A * ztxln)
    (hc : cntG A B c ≤ c' ∨
      (c' = c ∧ A ≤ c ∧ 8 * A * B ≤ c ∧ 8 * A * 2 ^ b' ≤ 2 ^ b ∧ 32 * A * B ≤ 2 ^ b)) :
    K' * 2 ^ b' ≤ c' * (2 ^ p + 2 ^ b') := by
  have hY1 : 1 ≤ 2 ^ b' := Nat.one_le_two_pow
  have hYX : 2 ^ b' ≤ 2 ^ b := Nat.pow_le_pow_right by_norm_num hb'
  have hXP : 2 ^ b ≤ 2 ^ p := Nat.pow_le_pow_right by_norm_num hb
  set P := 2 ^ p
  set X := 2 ^ b
  set Y := 2 ^ b'
  have hG0 : 0 < G := by_omega
  have h1 : K' * Y ≤ A * ztbr * Y + A * B * ztbhx := by
    apply Nat.le_of_mul_le_mul_right _ hG0
    calc K' * Y * G = K' * G * Y := by_ring
      _ ≤ A * ztxln * Y := Nat.mul_le_mul_right _ hK'
      _ = A * ztbr * Y * G + A * B * ztbhx * Y := by_ring
      _ ≤ A * ztbr * Y * G + A * B * ztbhx * G :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ hG) _
      _ = (A * ztbr * Y + A * B * ztbhx) * G := by_ring
  have hK2 : K * X ≤ 2 * c * P := by
    calc K * X ≤ c * (P + X) := hK
      _ ≤ c * (P + P) := Nat.mul_le_mul_left _ by_omega
      _ = 2 * c * P := by_ring
  have hn2 : n ≤ 2 * P := by_omega
  have eAn : A * B * n ≤ 2 * A * B * P := by
    calc A * B * n ≤ A * B * (2 * P) := Nat.mul_le_mul_left _ hn2
      _ = 2 * A * B * P := by_ring
  have e0 : K' * Y ≤ A * ztemy + A * Y + A * B * n + 4 * A * B * K := by
    grind
  rcases hc with hc | ⟨rfl, hAc, hABc, h8, h32⟩
  · have eKY : A * ztemy ≤ 2 * A * c * P := by
      calc A * ztemy ≤ A * ztsyp := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hYX)
        _ ≤ A * ztptv := Nat.mul_le_mul_left _ hK2
        _ = 2 * A * c * P := by_ring
    have eK : 4 * A * B * K ≤ 8 * A * B * c * P := by
      have : K ≤ K * X := Nat.le_mul_of_pos_right _ by_omega
      calc 4 * A * B * K ≤ 4 * A * B * ztsyp := Nat.mul_le_mul_left _ this
        _ ≤ 4 * A * B * ztptv := Nat.mul_le_mul_left _ hK2
        _ = 8 * A * B * c * P := by_ring
    have hP1 : ztrzy := Nat.one_le_two_pow
    calc K' * Y ≤ A * ztemy + A * Y + A * B * n + 4 * A * B * K := e0
      _ ≤ 2 * A * c * P + A * Y + 2 * A * B * P + 8 * A * B * c * P := by_omega
      _ ≤ cntG A B c * P + cntG A B c * Y := by
          unfold cntG
          grind
      _ ≤ c' * P + c' * Y :=
          Nat.add_le_add zttbc zttbc
      _ = c' * (P + Y) := by_ring
  · have hK2' : K * X ≤ 2 * zthgd := by_grind
    have eKY : 4 * ztyok ≤ c' * P := by
      have : 8 * ztyok ≤ 2 * zthgd := by
        calc 8 * ztyok = K * (8 * A * Y) := by_ring
          _ ≤ K * X := Nat.mul_le_mul_left _ h8
          _ ≤ 2 * zthgd := hK2'
      omega
    have eK : 16 * ztjgh ≤ c' * P := by
      have : 32 * ztjgh ≤ 2 * zthgd := by
        calc 32 * ztjgh = K * (32 * A * B) := by_ring
          _ ≤ K * X := Nat.mul_le_mul_left _ h32
          _ ≤ 2 * zthgd := hK2'
      omega
    have eN : 4 * ztpvj ≤ c' * P := by
      calc 4 * ztpvj ≤ 4 * (2 * A * B * P) := Nat.mul_le_mul_left _ eAn
        _ = 8 * A * B * P := by_ring
        _ ≤ c' * P := Nat.mul_le_mul_right _ hABc
    have eA : A * Y ≤ c' * Y := Nat.mul_le_mul_right _ hAc
    grind

/-- **(I3) across one level.**  Let `16 ≤ λ ≤ p`, `μ = ⌈βλ⌉ + 11`, and let the counts `K` (level
`λ`) and `K'` (level `μ`) satisfy the level bound with `2^⌈βμ⌉ ≤ G`.  If (I3) holds at `λ` with
`cnt A B λ`, it holds at `μ` with `cnt A B μ`. -/
theorem cnt_step {A B : ℕ} (hA : 1 ≤ A) {lam p K K' n G : ℕ} (h16 : 16 ≤ lam) (hlp : lam ≤ p)
    (hK : K * 2 ^ Cost.ceilBeta lam ≤ cnt A B lam * ztdyg)
    (hn : n ≤ 2 ^ p + 1) (hG : 2 ^ Cost.ceilBeta ztblw ≤ G)
    (hK' : K' * G ≤ A * ztxln) :
    K' * 2 ^ Cost.ceilBeta ztblw ≤
      cnt A B ztblw * (2 ^ p + 2 ^ Cost.ceilBeta ztblw) := by
  have hbl : ztuki := Cost.ceilBeta_le lam
  have hμ : Cost.ceilBeta lam + 11 < lam := Cost.ceilBeta_add_eleven_lt h16
  have hb' : Cost.ceilBeta ztblw ≤ Cost.ceilBeta lam := by
    rw [Setup.ceilBeta_eq, Setup.ceilBeta_eq lam]; omega
  refine step_arith hK (hbl.trans hlp) hb' hn hG hK' ?_
  by_cases hbig : cntLam A B ≤ Cost.ceilBeta lam + 11
  · -- both levels above the threshold
    have hlam : cntLam A B ≤ lam := by_omega
    right
    have e1 : cnt A B lam = cntBase A B := by unfold cnt; simp_all
    have e2 : cnt A B ztblw = cntBase A B := by unfold cnt; simp_all
    obtain ⟨h8, h32⟩ := big_of_ge hlam
    zuea
    refine ⟨rfl, by unfold cntBase; omega, by unfold cntBase; omega, h8, h32⟩
  · -- the next level is below the threshold
    left
    have e2 : cnt A B ztblw =
        ztdue^[cntLam A B - ztblw] ztjsv := by
      unfold cnt; simp_all
    obtain ⟨k, hk, ek⟩ : ∃ k, k + 1 ≤ cntLam A B - (Cost.ceilBeta lam + 11) ∧
        cnt A B lam = ztdue^[k] ztjsv := by
      by_cases hl : cntLam A B ≤ lam
      · exact ⟨0, by_omega, by unfold cnt; simp_all⟩
      · exact ⟨cntLam A B - lam, by_omega, by unfold cnt; simp_all⟩
    rw [e2, ek, ← Function.iterate_succ_apply' ztdue]
    exact iterate_le_iterate hA B _ hk

/-! ## The transition -/

/-- **(I3) after the transition.**  The top-chain map is `γ'_p`-granular with cap `4`, so by
Lemma 2.3 (`c 4 = 840`, size `2 (n - 1)`) `K₀ (γ'_p + 1) ≤ 840 (2 (n - 1) + 1)`; the transition
keeps at most `K₀` chords (T4).  Then (I3) holds at `λ = p`. -/
theorem cnt_trans (hA : 1 ≤ A) (B : ℕ) {K K₀ n p : ℕ} (hn : n - 1 ≤ 2 ^ p)
    (hK₀ : K₀ * ztfsd ≤ 840 * ztxfv) (hK : K ≤ K₀) :
    K * 2 ^ Cost.ceilBeta p ≤ cnt A B p * ztmaf := by
  have hg : 2 ^ Cost.ceilBeta p ≤ gradeGran p + 1 := by unfold gradeGran; omega
  have hc := cntBase_le_cnt hA B p
  have hP1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  calc K * 2 ^ Cost.ceilBeta p ≤ K₀ * ztfsd := Nat.mul_le_mul hK hg
    _ ≤ 840 * ztxfv := hK₀
    _ ≤ 2520 * 2 ^ p := by_omega
    _ ≤ cntBase A B * 2 ^ p := Nat.mul_le_mul_right _ (by unfold cntBase; omega)
    _ ≤ cnt A B p * ztmaf := Nat.mul_le_mul hc ztfoi
end
end DownMath
namespace OutGeom
open Set Filter Topology
open Chazelle.Visibility
open Chazelle.Mountain (TrapData topVtx botVtx sideVtxSet)
open Chazelle.Jordan (simple_vtx_inj simple_openEdge_not_mem_other simple_openEdge_ne_vtx
  exists_openEdge_of_mem_boundary simple_endpoint_of_mem_two succIdx_lt simple_vtx_succ_ne)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext point_ext_iff continuous_lerp)
@[expose] public section
variable {Q : Polygon} (hQ : Q.Simple) (hdh : DistinctHeights Q) (D : TrapData Q)

/-! ## Vertices at the side heights -/
include hdh in
/-- The top vertex is the only vertex at the top height. -/
theorem vtx_eq_top (hQ : Q.Simple) {k : ℕ} (hk : k < Q.n) (hy : (Q.vtx k).2 = D.y₂) :
    k = D.top := by
  zuct
  exact hdh k D.top hk ztjhy hne (hy.trans (D.top_snd hQ).symm)
include hdh in
/-- The bottom vertex is the only vertex at the bottom height. -/
theorem vtx_eq_bot (hQ : Q.Simple) {k : ℕ} (hk : k < Q.n) (hy : (Q.vtx k).2 = D.y₁) :
    k = D.bot := by
  zuct
  exact hdh k D.bot hk ztjhw hne (hy.trans (D.bot_snd hQ).symm)
include hQ in
/-- The top vertex lies on the closed top side. -/
theorem top_x_mem : edgeX Q D.i D.y₂ ≤ (Q.vtx D.top).1 ∧ (Q.vtx D.top).1 ≤ edgeX Q D.j D.y₂ := by
  have h := D.isTrap.topVtx_mem hQ D.free
  exact ztugq
include hQ in
/-- The bottom vertex lies on the closed bottom side. -/
theorem bot_x_mem : edgeX Q D.i D.y₁ ≤ (Q.vtx D.bot).1 ∧ (Q.vtx D.bot).1 ≤ edgeX Q D.j D.y₁ := by
  have h := D.isTrap.botVtx_mem hQ D.free
  exact ztugq

/-! ## Boundary points of the open sides -/
include hQ in
/-- A boundary point `z` of height `y₀` near which the points on the `ε`-side of the line are in
the region is a vertex (a non-vertex boundary point lies inside a non-horizontal edge, whose
points on the `ε`-side would be boundary points of the region). -/
theorem side_bdry_vtx {z : Point} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hz : z ∈ Q.boundary)
    (hdh : DistinctHeights Q)
    (hnear : ∀ᶠ p' in 𝓝 z, 0 < ε * (p'.2 - z.2) → p' ∈ D.region) :
    ∃ m, m < Q.n ∧ Q.vtx m = z := by
  by_contra hv
  zugrj
  obtain ⟨e, he, t, ht, hzt⟩ := exists_openEdge_of_mem_boundary Q hz (fun m hm h => hv m hm h.symm)
  set a := Q.vtx e with ha
  set b := Q.vtx ztwki with hb
  zudov
  have hab :=
    hdh e _ he (succIdx_lt Q he) (Chazelle.Jordan.succIdx_ne Q hn3 he).symm
  -- move along the edge towards the `ε` side
  set d : ℝ := ε * ztti with hd
  have hd0 : ztpnz := by
    grind
  set g : ℝ → Point := fun s => lerp a b (t + s * d) with hg
  have hgc : Continuous g := (continuous_lerp a b).comp ztepq
  have hg0 : g 0 = z := by_grind
  have htend : Tendsto g (𝓝[>] 0) (𝓝 z) := by
    rw [← hg0]; exact (hgc.tendsto 0).mono_left nhdsWithin_le_nhds
  zulka
  have htend' : Tendsto (fun s : ℝ => t + s * d) (𝓝[>] 0) (𝓝 t) := by
    have hc : Continuous (fun s : ℝ => t + s * d) := by fun_prop
    have := hc.tendsto 0
    simp only [zero_mul, add_zero] at this
    zuhv
  have hev2 := htend'.eventually ztvxj
  obtain ⟨s, ⟨h1, h2⟩, hs⟩ := ((hev1.and hev2).and self_mem_nhdsWithin).exists
  zuesg
  have hy : (g s).2 - z.2 = s * d * ztti := by
    simp only [hg, lerp_snd]; rw [hzt, lerp_snd]; ring
  have hpos : 0 < ε * ((g s).2 - z.2) := by
    zujka
    have : ε * (s * d * ztti) = s * (d * d) := by_grind
    zubk
    exact mul_pos hs0 ztvzh
  have hreg := h1 hpos
  have hmem : g s ∈ Q.boundary := ⟨e, he, Chazelle.Geometry.lerp_mem_segment _ _ h2.1.le h2.2.le⟩
  exact (D.region_subset_interior hQ hreg).2 hmem
include hQ hdh in
/-- **The only boundary point of the open top side is the top vertex.** -/
theorem top_bdry {x : ℝ} (hx1 : edgeX Q D.i D.y₂ < x) (hx2 : x < edgeX Q D.j D.y₂)
    (hb : (ztbnt : Point) ∈ Q.boundary) : (ztbnt : Point) = Q.vtx D.top := by
  obtain ⟨m, hm, hmz⟩ := side_bdry_vtx hQ D ztbt hb hdh ztswn
  have  := vtx_eq_top hdh D hQ hm ztqfa
  simp_all
include hQ hdh in
/-- **The only boundary point of the open bottom side is the bottom vertex.** -/
theorem bot_bdry {x : ℝ} (hx1 : edgeX Q D.i D.y₁ < x) (hx2 : x < edgeX Q D.j D.y₁)
    (hb : (ztbqn : Point) ∈ Q.boundary) : (ztbqn : Point) = Q.vtx D.bot := by
  obtain ⟨m, hm, hmz⟩ := side_bdry_vtx hQ D ztp hb hdh (D.isTrap.near_bot hx1 hx2)
  have  := vtx_eq_bot hdh D hQ hm ztqfa
  simp_all
include hQ hdh in
/-- A point of the open top side other than the top vertex is an interior point of the closure
of the region lying on a chord. -/
theorem top_chord_pt {x : ℝ} (hx1 : edgeX Q D.i D.y₂ < x) (hx2 : x < edgeX Q D.j D.y₂)
    (hne : (ztbnt : Point) ≠ Q.vtx D.top) :
    ∃ c ∈ chords Q, (ztbnt : Point) ∈ c ∧ (ztbnt : Point) ∈ Q.filled \ Q.boundary ∧
      (ztbnt : Point) ∈ closure D.region := by
  have hc := D.isTrap.top_mem_closure hx1 hx2
  have hnb := fun hb => hne (top_bdry hQ hdh D hx1 hx2 hb)
  rcases D.isTrap.top_side hQ D.free hx1 hx2 with hb | ⟨c, hc', hmem⟩
  · simp_all
  · exact ztgsz
include hQ hdh in
/-- A point of the open bottom side other than the bottom vertex is an interior point of the
closure of the region lying on a chord. -/
theorem bot_chord_pt {x : ℝ} (hx1 : edgeX Q D.i D.y₁ < x) (hx2 : x < edgeX Q D.j D.y₁)
    (hne : (ztbqn : Point) ≠ Q.vtx D.bot) :
    ∃ c ∈ chords Q, (ztbqn : Point) ∈ c ∧ (ztbqn : Point) ∈ Q.filled \ Q.boundary ∧
      (ztbqn : Point) ∈ closure D.region := by
  have hc := D.isTrap.bot_mem_closure hx1 hx2
  have hnb := fun hb => hne (bot_bdry hQ hdh D hx1 hx2 hb)
  rcases D.isTrap.bot_side hQ D.free hx1 hx2 with hb | ⟨c, hc', hmem⟩
  · simp_all
  · exact ztgsz
include hQ in
/-- **A chord touches the region on its open top or bottom side.** -/
theorem touch_cases {c : Set Point} (hc : c ∈ chords Q) {z : Point} (hzc : z ∈ c)
    (hzD : z ∈ Q.filled \ Q.boundary) (hzU : z ∈ closure D.region) :
    (z.2 = D.y₂ ∧ edgeX Q D.i D.y₂ < z.1 ∧ z.1 < edgeX Q D.j D.y₂) ∨
      (z.2 = D.y₁ ∧ edgeX Q D.i D.y₁ < z.1 ∧ z.1 < edgeX Q D.j D.y₁) := by
  obtain ⟨h1, h2, h3, h4⟩ := closure_trapSet_subset Q D.i D.j D.y₁ D.y₂ hzU
  have hnotU := fun h =>
    (D.region_subset_freeRegion hQ h).2 ⟨c, hc, hzc⟩
  have hnotL := fun e =>
    hzD.2 ⟨D.i, D.isTrap.hi, D.isTrap.mem_edgeL h1 h2 e⟩
  have hnotR := fun e =>
    hzD.2 ⟨D.j, D.isTrap.hj, D.isTrap.mem_edgeR h1 h2 e⟩
  have h3' : edgeX Q D.i z.2 < z.1 := by_grind
  have h4' : z.1 < edgeX Q D.j z.2 := by_grind
  zuff
  · zudt
    · exact absurd ⟨h1, h2, h3', h4'⟩ hnotU
    simp_all
  simp_all
include hQ hdh in
/-- **The ends of a chord through the open top side**: its left end is the left corner or the
top vertex, its right end the top vertex or the right corner. -/
theorem top_chord_ends {a b : ℝ} (hch : IsHChord Q D.y₂ a b) {z : Point}
    (hz : z ∈ hseg D.y₂ a b) (hzD : z ∈ Q.filled \ Q.boundary)
    (hz1 : edgeX Q D.i D.y₂ < z.1) (hz2 : z.1 < edgeX Q D.j D.y₂) :
    edgeX Q D.i D.y₂ ≤ a ∧ (a = edgeX Q D.i D.y₂ ∨ a = (Q.vtx D.top).1) ∧
      b ≤ edgeX Q D.j D.y₂ ∧ (b = edgeX Q D.j D.y₂ ∨ b = (Q.vtx D.top).1) := by
  zubpe
  zukl
  have hLb : (ztduh : Point) ∈ Q.boundary :=
    ⟨D.i, D.isTrap.hi, D.isTrap.mem_edgeL hy12 le_rfl rfl⟩
  have hRb : (ztijf : Point) ∈ Q.boundary :=
    ⟨D.j, D.isTrap.hj, D.isTrap.mem_edgeR hy12 le_rfl rfl⟩
  have hza' : a < z.1 := by
    zukmu
    · zubh
    · zugkl
      have : z = (zttes : Point) := by_grind
      zujlq
  have hzb' : z.1 < b := by
    zukmv
    · zubh
    · zugkl
      have : z = (zttfn : Point) := by_grind
      zujlr
  have ha1 : edgeX Q D.i D.y₂ ≤ a := by
    zuso
    zuhco
  have hb1 : b ≤ edgeX Q D.j D.y₂ := by
    zuso
    zuhcn
  refine ztony
  · zukkv
    · right
      have := top_bdry hQ hdh D h by_linarith hch.left_mem
      grind
    simp_all
  · zukkx
    · right
      have := top_bdry hQ hdh D by_linarith h hch.right_mem
      grind
    simp_all
include hQ hdh in
/-- **The ends of a chord through the open bottom side.** -/
theorem bot_chord_ends {a b : ℝ} (hch : IsHChord Q D.y₁ a b) {z : Point}
    (hz : z ∈ hseg D.y₁ a b) (hzD : z ∈ Q.filled \ Q.boundary)
    (hz1 : edgeX Q D.i D.y₁ < z.1) (hz2 : z.1 < edgeX Q D.j D.y₁) :
    edgeX Q D.i D.y₁ ≤ a ∧ (a = edgeX Q D.i D.y₁ ∨ a = (Q.vtx D.bot).1) ∧
      b ≤ edgeX Q D.j D.y₁ ∧ (b = edgeX Q D.j D.y₁ ∨ b = (Q.vtx D.bot).1) := by
  zubpe
  zukl
  have hLb : (ztdug : Point) ∈ Q.boundary :=
    ⟨D.i, D.isTrap.hi, D.isTrap.mem_edgeL le_rfl hy12 rfl⟩
  have hRb : (ztije : Point) ∈ Q.boundary :=
    ⟨D.j, D.isTrap.hj, D.isTrap.mem_edgeR le_rfl hy12 rfl⟩
  have hza' : a < z.1 := by
    zukmu
    · zubh
    · zugkl
      have : z = (ztnqt : Point) := by_grind
      zujlq
  have hzb' : z.1 < b := by
    zukmv
    · zubh
    · zugkl
      have : z = (ztnrq : Point) := by_grind
      zujlr
  have ha1 : edgeX Q D.i D.y₁ ≤ a := by
    zuso
    zuhco
  have hb1 : b ≤ edgeX Q D.j D.y₁ := by
    zuso
    zuhcn
  refine ztony
  · zukkv
    · right
      have := bot_bdry hQ hdh D h by_linarith hch.left_mem
      grind
    simp_all
  · zukkx
    · right
      have := bot_bdry hQ hdh D by_linarith h hch.right_mem
      grind
    simp_all
include hQ hdh in
/-- **An empty top side**: the top vertex is at both upper corners. -/
theorem top_empty (h : edgeX Q D.j D.y₂ ≤ edgeX Q D.i D.y₂) :
    Q.vtx D.top = (ztduh : Point) ∧
      Q.vtx D.top = (ztijf : Point) := by
  have hle := D.isTrap.edgeX_le_top hQ D.free
  have heq : edgeX Q D.i D.y₂ = edgeX Q D.j D.y₂ := by_grind
  zukl
  have h1 : (ztduh : Point) ∈ Q.edge D.i := D.isTrap.mem_edgeL hy12 le_rfl rfl
  have h2 : (ztduh : Point) ∈ Q.edge D.j := D.isTrap.mem_edgeR hy12 le_rfl heq
  obtain ⟨m, hm, hmp⟩ := Final.exists_vtx_of_mem_two_edges hQ D.isTrap.hi D.isTrap.hj
    ztswm h1 h2
  have hmt := vtx_eq_top hdh D hQ hm ztqez
  simp_all
include hQ hdh in
/-- **An empty bottom side**: the bottom vertex is at both lower corners. -/
theorem bot_empty (h : edgeX Q D.j D.y₁ ≤ edgeX Q D.i D.y₁) :
    Q.vtx D.bot = (ztdug : Point) ∧
      Q.vtx D.bot = (ztije : Point) := by
  have hle := D.isTrap.edgeX_le_bot hQ D.free
  have heq : edgeX Q D.i D.y₁ = edgeX Q D.j D.y₁ := by_grind
  zukl
  have h1 : (ztdug : Point) ∈ Q.edge D.i := D.isTrap.mem_edgeL le_rfl hy12 rfl
  have h2 : (ztdug : Point) ∈ Q.edge D.j := D.isTrap.mem_edgeR le_rfl hy12 heq
  obtain ⟨m, hm, hmp⟩ := Final.exists_vtx_of_mem_two_edges hQ D.isTrap.hi D.isTrap.hj
    ztswm h1 h2
  have hmt := vtx_eq_bot hdh D hQ hm ztqez
  simp_all

/-- A chord of `Q` through a point of height `y`, as a horizontal chord at height `y`. -/
theorem chord_hseg (hQ : Q.Simple) {c : Set Point} (hc : c ∈ chords Q) {z : Point} (hz : z ∈ c) :
    ∃ a b, IsHChord Q z.2 a b ∧ c = hseg z.2 a b := by
  obtain ⟨v, σ, hv, hσ, hdir, rfl, hch⟩ := chords_spec hQ hc
  zumfb
  rw [chordSet_eq_hseg] at hz'
  rw [hz'.1, chordSet_eq_hseg]
  grind
include hQ hdh in
/-- **Left top corner**: if the top vertex is not at the left upper corner, some chord through
the open top side ends at that corner. -/
theorem exists_top_chord_left (hne : (Q.vtx D.top).1 ≠ edgeX Q D.i D.y₂) :
    ∃ c ∈ chords Q, ∃ b, IsHChord Q D.y₂ ztrpd b ∧
      c = hseg D.y₂ ztrpd b ∧
      ∃ z ∈ c, z ∈ Q.filled \ Q.boundary ∧ z ∈ closure D.region := by
  zugpx
  have hlt : edgeX Q D.i D.y₂ < (Q.vtx D.top).1 := by_grind
  set x := (edgeX Q D.i D.y₂ + (Q.vtx D.top).1) / 2 with hx
  have hxa : edgeX Q D.i D.y₂ < x := by_grind
  have hxb : x < (Q.vtx D.top).1 := by_grind
  zukhb
  obtain ⟨c, hc, hzc, hzD, hzU⟩ := top_chord_pt hQ hdh D hxa by_linarith hxne
  zutc
  simp only at hch hzc ⊢
  obtain ⟨-, ha, -, -⟩ := top_chord_ends hQ hdh D hch hzc hzD hxa by_linarith
  zuljl
include hQ hdh in
/-- **Right top corner**: if the top vertex is not at the right upper corner, some chord through
the open top side ends at that corner. -/
theorem exists_top_chord_right (hne : (Q.vtx D.top).1 ≠ edgeX Q D.j D.y₂) :
    ∃ c ∈ chords Q, ∃ a, IsHChord Q D.y₂ a ztrpf ∧
      c = hseg D.y₂ a ztrpf ∧
      ∃ z ∈ c, z ∈ Q.filled \ Q.boundary ∧ z ∈ closure D.region := by
  zugpx
  have hlt : (Q.vtx D.top).1 < edgeX Q D.j D.y₂ := by_grind
  set x := ((Q.vtx D.top).1 + edgeX Q D.j D.y₂) / 2 with hx
  have hxa : (Q.vtx D.top).1 < x := by_grind
  have hxb : x < edgeX Q D.j D.y₂ := by_grind
  zukhb
  obtain ⟨c, hc, hzc, hzD, hzU⟩ := top_chord_pt hQ hdh D by_linarith hxb hxne
  zutc
  zufcu
  obtain ⟨-, -, -, hb⟩ := top_chord_ends hQ hdh D hch hzc hzD by_linarith hxb
  zuljt
include hQ hdh in
/-- **Left bottom corner.** -/
theorem exists_bot_chord_left (hne : (Q.vtx D.bot).1 ≠ edgeX Q D.i D.y₁) :
    ∃ c ∈ chords Q, ∃ b, IsHChord Q D.y₁ ztrpc b ∧
      c = hseg D.y₁ ztrpc b ∧
      ∃ z ∈ c, z ∈ Q.filled \ Q.boundary ∧ z ∈ closure D.region := by
  zugpw
  have hlt : edgeX Q D.i D.y₁ < (Q.vtx D.bot).1 := by_grind
  set x := (edgeX Q D.i D.y₁ + (Q.vtx D.bot).1) / 2 with hx
  have hxa : edgeX Q D.i D.y₁ < x := by_grind
  have hxb : x < (Q.vtx D.bot).1 := by_grind
  zukhc
  obtain ⟨c, hc, hzc, hzD, hzU⟩ := bot_chord_pt hQ hdh D hxa by_linarith hxne
  zutc
  zufcu
  obtain ⟨-, ha, -, -⟩ := bot_chord_ends hQ hdh D hch hzc hzD hxa by_linarith
  zuljl
include hQ hdh in
/-- **Right bottom corner.** -/
theorem exists_bot_chord_right (hne : (Q.vtx D.bot).1 ≠ edgeX Q D.j D.y₁) :
    ∃ c ∈ chords Q, ∃ a, IsHChord Q D.y₁ a ztrpe ∧
      c = hseg D.y₁ a ztrpe ∧
      ∃ z ∈ c, z ∈ Q.filled \ Q.boundary ∧ z ∈ closure D.region := by
  zugpw
  have hlt : (Q.vtx D.bot).1 < edgeX Q D.j D.y₁ := by_grind
  set x := ((Q.vtx D.bot).1 + edgeX Q D.j D.y₁) / 2 with hx
  have hxa : (Q.vtx D.bot).1 < x := by_grind
  have hxb : x < edgeX Q D.j D.y₁ := by_grind
  zukhc
  obtain ⟨c, hc, hzc, hzD, hzU⟩ := bot_chord_pt hQ hdh D by_linarith hxb hxne
  zutc
  zufcu
  obtain ⟨-, -, -, hb⟩ := bot_chord_ends hQ hdh D hch hzc hzD by_linarith hxb
  zuljt

/-! ## Vertices at the corners are ends of the side edges -/

/-- A vertex on an edge, above the lower end of the edge, is its upper end. -/
theorem endpoint_upper (hQ : Q.Simple) {e v : ℕ} (he : e < Q.n) (hv : v < Q.n)
    (hmem : Q.vtx v ∈ Q.edge e) (hbot : edgeBot Q e < (Q.vtx v).2) :
    (v = e ∧ (Q.vtx ztwki).2 < (Q.vtx v).2) ∨
      (v = ztda % Q.n ∧ (Q.vtx e).2 < (Q.vtx v).2) := by
  unfold edgeBot at hbot
  zugrk
  · zumhx

  · zumkx

/-- A vertex on an edge, below the upper end of the edge, is its lower end. -/
theorem endpoint_lower (hQ : Q.Simple) {e v : ℕ} (he : e < Q.n) (hv : v < Q.n)
    (hmem : Q.vtx v ∈ Q.edge e) (htop : (Q.vtx v).2 < edgeTop Q e) :
    (v = e ∧ (Q.vtx v).2 < (Q.vtx ztwki).2) ∨
      (v = ztda % Q.n ∧ (Q.vtx v).2 < (Q.vtx e).2) := by
  unfold edgeTop at htop
  zugrk
  · zumhx

  · zumkx
include hQ in
/-- The top vertex at the left upper corner is an end of the left edge, above the other end. -/
theorem top_left_upper (h : Q.vtx D.top = (ztduh : Point)) :
    (D.top = D.i ∧ (Q.vtx ztxlq).2 < (Q.vtx D.top).2) ∨
      (D.top = ztclh % Q.n ∧ (Q.vtx D.i).2 < (Q.vtx D.top).2) := by
  zukl
  refine endpoint_upper hQ D.isTrap.hi ztjhy ?_ ?_
  · zvmwc; exact D.isTrap.mem_edgeL hy12 le_rfl rfl
  · zuosr; exact lt_of_le_of_lt D.isTrap.botL ztmaq
include hQ in
/-- The top vertex at the right upper corner is an end of the right edge, above the other end. -/
theorem top_right_upper (h : Q.vtx D.top = (ztijf : Point)) :
    (D.top = D.j ∧ (Q.vtx ztdec).2 < (Q.vtx D.top).2) ∨
      (D.top = ztjhx % Q.n ∧ (Q.vtx D.j).2 < (Q.vtx D.top).2) := by
  zukl
  refine endpoint_upper hQ D.isTrap.hj ztjhy ?_ ?_
  · zvmwc; exact D.isTrap.mem_edgeR hy12 le_rfl rfl
  · zuosr; exact lt_of_le_of_lt D.isTrap.botR ztmaq
include hQ in
/-- The bottom vertex at the left lower corner is an end of the left edge, below the other end. -/
theorem bot_left_lower (h : Q.vtx D.bot = (ztdug : Point)) :
    (D.bot = D.i ∧ (Q.vtx D.bot).2 < (Q.vtx ztxlq).2) ∨
      (D.bot = ztclh % Q.n ∧ (Q.vtx D.bot).2 < (Q.vtx D.i).2) := by
  zukl
  refine endpoint_lower hQ D.isTrap.hi ztjhw ?_ ?_
  · zvmwc; exact D.isTrap.mem_edgeL le_rfl hy12 rfl
  · zuoss; exact lt_of_lt_of_le ztmaq D.isTrap.topL
include hQ in
/-- The bottom vertex at the right lower corner is an end of the right edge, below the other
end. -/
theorem bot_right_lower (h : Q.vtx D.bot = (ztije : Point)) :
    (D.bot = D.j ∧ (Q.vtx D.bot).2 < (Q.vtx ztdec).2) ∨
      (D.bot = ztjhx % Q.n ∧ (Q.vtx D.bot).2 < (Q.vtx D.j).2) := by
  zukl
  refine endpoint_lower hQ D.isTrap.hj ztjhw ?_ ?_
  · zvmwc; exact D.isTrap.mem_edgeR le_rfl hy12 rfl
  · zuoss; exact lt_of_lt_of_le ztmaq D.isTrap.topR
end
end OutGeom
namespace OutWalk
open Set Filter Topology Metric
open Chazelle.Visibility
open Chazelle.Mountain (TrapData LeftInside orient)
open Chazelle.Jordan (simple_vtx_inj succIdx_lt)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext point_ext_iff)
open Chazelle.Chain (sidePt)
@[expose] public section
variable {Q : Polygon}

/-! ## Index arithmetic -/

/-- The vertex of `Q` at walk vertex `k` (`b`: the walk is reversed). -/
def wv (b : Bool) (n k : ℕ) : ℕ := if b then n - 1 - k else k

/-- The successor index `(p + 1) % n` (for `p < n`). -/
def nxt (n p : ℕ) : ℕ := if p + 1 < n then p + 1 else 0

/-- The edge of `Q` carried by walk edge `p`. -/
def inp (b : Bool) (n p : ℕ) : ℕ := if b then (if p + 1 < n then n - 2 - p else n - 1) else p
variable {n p : ℕ} {b : Bool} {W : Polygon}
/-- `nxt` is the successor modulo `n`. -/
theorem nxt_eq (hp : p < n) : nxt n p = ztr % n := by
  unfold nxt
  zus
  · zukp
  · zubyy

/-- `nxt` stays below `n`. -/
theorem nxt_lt (hp : p < n) : nxt n p < n := by unfold nxt; grind

/-- `inp` stays below `n`. -/
theorem inp_lt {n p : ℕ} (hp : p < n) : inp b n p < n := by
  zumsy

/-- `wv` stays below `n`. -/
theorem wv_lt {n k : ℕ} (hk : k < n) : wv b n k < n := by
  zumvm

/-- `inp` is an involution below `n`. -/
theorem inp_inp {n p : ℕ} (hp : p < n) : inp b n ztlqg = p := by
  zumsy

/-- `wv` is an involution below `n`. -/
theorem wv_wv {n k : ℕ} (hk : k < n) : wv b n (wv b n k) = k := by
  zumvm

/-- The ends of a walk edge in terms of the carried edge. -/
theorem wv_inp {n p : ℕ} (hp : p < n) :
    (b = false ∧ wv b n p = inp b n p ∧ wv b n zttuo = nxt n ztlqg) ∨
      (b = true ∧ wv b n p = nxt n ztlqg ∧ wv b n zttuo = inp b n p) := by
  cases b
  · tauto
  · right
    refine ztkw <;> simp only [wv, inp, nxt] <;>
      zuwd

/-! ## The walk -/
open Classical in
/-- Whether the interior walk of `Q` is the reversed polygon. -/
noncomputable def revOf (Q : Polygon) : Bool := decide (¬ LeftInside Q)

/-- The interior walk has `n` vertices. -/
theorem walk_n (Q : Polygon) : (interiorWalk Q).n = Q.n := by
  classical
  zugiq

  · rfl
  · zuhcp

/-- The walk vertices are vertices of `Q`. -/
theorem walk_vtx (Q : Polygon) {k : ℕ} (hk : k < Q.n) :
    (interiorWalk Q).vtx k = Q.vtx (wv ztgl Q.n k) := by
  classical
  by_cases h : LeftInside Q
  · have e1 : interiorWalk Q = Q := by unfold interiorWalk; zumxk
    have e2 : revOf Q = false := by unfold revOf; zumxk
    zuihn
  · have e1 : interiorWalk Q = ⟨Q.vertices.reverse⟩ := by unfold interiorWalk; zumxk
    have e2 : revOf Q = true := by unfold revOf; zumxk
    zuea
    zuled

/-- The walk successor. -/
theorem walk_succ (Q : Polygon) {p : ℕ} (hp : p < Q.n) :
    (interiorWalk Q).vtx ztxlt = Q.vtx ztzod := by
  rw [walk_n, ← nxt_eq hp, walk_vtx Q ztquf]

/-! ## The direction of a walk edge next to an interior point -/

/-- If the points just right of a point `z` inside walk edge `p` are interior, the walk edge
goes down (interior on the left). -/
theorem walk_down (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hint : ∀ δ, 0 < δ → δ < δ₀ →
      (ztgbm : Point) ∈ W.filled \ W.boundary) :
    (W.vtx ztwjb).2 < (W.vtx p).2 := by
  zulu

  set x : Point := ztgbm with hx
  have hxb : ztzqt := by
    zudaj

    rw [show (sidePt W p t).1 - ((sidePt W p t).1 + δ) = -δ by ring, abs_neg, abs_of_pos hδ0]
    grind
  zucmt

  have hdet : det a b x = -δ * ztti := by
    zucqy
  zugsb
  · zuijq
  · grind
  grind

/-- If the points just left of a point `z` inside walk edge `p` are interior, the walk edge goes
up. -/
theorem walk_up (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hint : ∀ δ, 0 < δ → δ < δ₀ →
      (ztgbn : Point) ∈ W.filled \ W.boundary) :
    (W.vtx p).2 < (W.vtx ztwjb).2 := by
  zulu

  set x : Point := ztgbn with hx
  have hxb : ztzqt := by
    zudaj

    rw [show (sidePt W p t).1 - ((sidePt W p t).1 - δ) = δ by ring, abs_of_pos hδ0]
    grind
  zucmt

  have hdet : det a b x = δ * ztti := by
    zucqy
  zugsb
  · zuijq
  · grind
  grind

/-! ## The walk along the side edges of a trapezoid -/

/-- A point of the open left side at a middle height, as a point of the open edge `i`. -/
theorem left_mid (hQ : Q.Simple) (D : TrapData Q) :
    ∃ t ∈ Ioo (0 : ℝ) 1, lerp (Q.vtx D.i) (Q.vtx ztxlq) t =
      ((edgeX Q D.i ztzyy, ztcem / 2) : Point) := by
  zuhw
  zucch

  have hmem : (ztpax : Point) ∈ Q.edge D.i :=
    D.isTrap.mem_edgeL hy1.le hy2.le rfl
  zufku
  zucgs
  have hnv : ∀ k, k < Q.n → Q.vtx k ≠ (ztpax : Point) := by
    zumhc
    have e1 : (Q.vtx k).1 = edgeX Q D.i ym := by zupai
    zugkw
    exact D.isTrap.no_vertex k hk by_simp_all by_simp_all
      by_simp_all by_grind
  refine ztzin
  · zubbd
    · zubh
    · exfalso; apply hnv D.i D.isTrap.hi
      grind
  · zugae
    · zubh
    · exfalso; apply hnv _ (succIdx_lt Q D.isTrap.hi)
      simp_all

/-- A point of the open right side at a middle height, as a point of the open edge `j`. -/
theorem right_mid (hQ : Q.Simple) (D : TrapData Q) :
    ∃ t ∈ Ioo (0 : ℝ) 1, lerp (Q.vtx D.j) (Q.vtx ztdec) t =
      ((edgeX Q D.j ztzyy, ztcem / 2) : Point) := by
  zuhw
  zucch

  have hmem : (ztpay : Point) ∈ Q.edge D.j :=
    D.isTrap.mem_edgeR hy1.le hy2.le rfl
  zufku
  zucgs
  have hnv : ∀ k, k < Q.n → Q.vtx k ≠ (ztpay : Point) := by
    zumhc
    have e1 : (Q.vtx k).1 = edgeX Q D.j ym := by zupai
    zugkw
    exact D.isTrap.no_vertex k hk by_simp_all by_simp_all
      by_grind by_simp_all
  refine ztzin
  · zubbd
    · zubh
    · exfalso; apply hnv D.j D.isTrap.hj
      grind
  · zugae
    · zubh
    · exfalso; apply hnv _ (succIdx_lt Q D.isTrap.hj)
      simp_all

/-- The walk point of the open part of an edge of `Q`. -/
theorem walk_pt (_hQ : Q.Simple) {e : ℕ} (he : e < Q.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ t' ∈ Ioo (0 : ℝ) 1, sidePt ztkb ztzmh t' =
      lerp ztgep ztbakx t := by
  have hp := inp_lt (b := revOf Q) he
  have hpp : inp _ Q.n ztzmh = e := inp_inp he
  zucky
  rw [walk_vtx Q hp, walk_succ Q hp, ← nxt_eq he]
  zubyc
  · grind
  · rw [h1, h2, hpp, Geometry.lerp_symm]
    grind

/-- **The walk runs down the left side edge**: walk edge `inp i` starts at the upper end of the
left side edge `i` of the trapezoid. -/
theorem walk_left (hQ : Q.Simple) (D : TrapData Q) :
    (Q.vtx (wv ztgl Q.n ztbamh)).2 <
      (Q.vtx (wv ztgl Q.n ztwpd)).2 := by
  zudg
  zumdm
  have hp := inp_lt (b := revOf Q) hi
  obtain ⟨t, ht, hzt⟩ := left_mid hQ D
  obtain ⟨t', ht', hz'⟩ := walk_pt hQ hi ht
  have hpW : inp ztgl Q.n D.i < (interiorWalk Q).n := by rw [walk_n]; exact hp
  zuhw
  zufhj

  zucgs
  have := walk_down hWs hWo hpW ht' zteau (fun δ hδ hδ' => by
    zugut
    exact D.region_subset_interior hQ ⟨hy1, hy2, by_simp_all, by_grind⟩)
  zufox

/-- **The walk runs up the right side edge**: walk edge `inp j` ends at the upper end of the
right side edge `j` of the trapezoid. -/
theorem walk_right (hQ : Q.Simple) (D : TrapData Q) :
    (Q.vtx (wv ztgl Q.n ztwql)).2 <
      (Q.vtx (wv ztgl Q.n ztbami)).2 := by
  zudg
  zumdp
  have hp := inp_lt (b := revOf Q) hj
  obtain ⟨t, ht, hzt⟩ := right_mid hQ D
  obtain ⟨t', ht', hz'⟩ := walk_pt hQ hj ht
  have hpW : inp ztgl Q.n D.j < (interiorWalk Q).n := by rw [walk_n]; exact hp
  zuhw
  zufhj

  zucgs
  have := walk_up hWs hWo hpW ht' zteau (fun δ hδ hδ' => by
    zugut
    exact D.region_subset_interior hQ ⟨hy1, hy2, by_grind, by_simp_all⟩)
  zufox

/-- The two walk ends of the walk edge carrying edge `e`. -/
theorem walk_ends {n e : ℕ} (he : e < n) :
    (wv b n zthyk = e ∧ wv b n ztzxi = nxt n e) ∨
      (wv b n zthyk = nxt n e ∧ wv b n ztzxi = e) := by
  have hp := inp_lt (b := b) he
  rcases wv_inp (b := b) hp with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · left; zunwo; omega
  · right; zunwo; omega

/-- The upper end of the left side edge is the start of its walk edge. -/
theorem walk_left_upper (hQ : Q.Simple) (D : TrapData Q) {v : ℕ}
    (hv : (v = D.i ∧ (Q.vtx ztxlq).2 < (Q.vtx v).2) ∨
      (v = ztclh % Q.n ∧ (Q.vtx D.i).2 < (Q.vtx v).2)) :
    wv ztgl Q.n ztwpd = v := by
  zuehg

  rcases walk_ends (b := revOf Q) D.isTrap.hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> zvmza at hw <;>
    zuczv
  · rfl
  · grind
  · grind
  · rfl

/-- The lower end of the left side edge is the end of its walk edge. -/
theorem walk_left_lower (hQ : Q.Simple) (D : TrapData Q) {v : ℕ}
    (hv : (v = D.i ∧ (Q.vtx v).2 < (Q.vtx ztxlq).2) ∨
      (v = ztclh % Q.n ∧ (Q.vtx v).2 < (Q.vtx D.i).2)) :
    wv ztgl Q.n ztbamh = v := by
  zuehg

  rcases walk_ends (b := revOf Q) D.isTrap.hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> zvmza at hw <;>
    zuczx
  · grind
  · rfl
  · rfl
  grind

/-- The lower end of the right side edge is the start of its walk edge. -/
theorem walk_right_lower (hQ : Q.Simple) (D : TrapData Q) {v : ℕ}
    (hv : (v = D.j ∧ (Q.vtx v).2 < (Q.vtx ztdec).2) ∨
      (v = ztjhx % Q.n ∧ (Q.vtx v).2 < (Q.vtx D.j).2)) :
    wv ztgl Q.n ztwql = v := by
  zuehh

  rcases walk_ends (b := revOf Q) D.isTrap.hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> zvmza at hw <;>
    zuczv
  · rfl
  · grind
  · grind
  · rfl

/-- The upper end of the right side edge is the end of its walk edge. -/
theorem walk_right_upper (hQ : Q.Simple) (D : TrapData Q) {v : ℕ}
    (hv : (v = D.j ∧ (Q.vtx ztdec).2 < (Q.vtx v).2) ∨
      (v = ztjhx % Q.n ∧ (Q.vtx D.j).2 < (Q.vtx v).2)) :
    wv ztgl Q.n ztbami = v := by
  zuehh

  rcases walk_ends (b := revOf Q) D.isTrap.hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> zvmza at hw <;>
    zuczx
  · grind
  · rfl
  · rfl
  grind
end
end OutWalk
namespace SignK
@[expose] public section
open Set Filter Topology

/-! ## Polynomials by coefficient lists and their eventual sign -/

/-- The polynomial with coefficient list `L`, evaluated at `ε` (Horner form). -/
def pe : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: L, ε => c + ε * pe L ε

/-- The lowest nonzero coefficient exists and is positive. -/
def lexPos : List ℝ → Prop
  | [] => False
  | c :: L => 0 < c ∨ (c = 0 ∧ lexPos L)

/-- The lowest nonzero coefficient exists and is negative. -/
def lexNeg : List ℝ → Prop
  | [] => False
  | c :: L => c < 0 ∨ (c = 0 ∧ lexNeg L)

/-- All coefficients vanish. -/
def allZero : List ℝ → Prop
  | [] => True
  | c :: L => c = 0 ∧ allZero L

/-- Every coefficient list is lexicographically positive, zero or negative. -/
theorem lex_trichotomy (L : List ℝ) : lexPos L ∨ allZero L ∨ lexNeg L := by
  induction L with
  | nil => exact Or.inr (Or.inl trivial)
  | cons c L ih =>
    rcases lt_trichotomy c 0 with h | h | h
    · tauto
    · rcases ih with h' | h' | h'
      · exact Or.inl ztcgy
      · tauto
      tauto
    · tauto

/-- A coefficient polynomial is continuous. -/
theorem continuous_pe (L : List ℝ) : Continuous (pe L) := by
  induction L with
  | nil => exact continuous_const
  | cons c L ih => exact continuous_const.add (continuous_id.mul ih)

/-- `pe (c :: L) 0 = c`. -/
theorem pe_cons_zero (c : ℝ) (L : List ℝ) : pe (c :: L) 0 = c := by
  simp [pe]
variable {L : List ℝ} {ε : ℝ} {p q : Point}
/-- The zero coefficient list gives the zero function. -/
theorem pe_of_allZero (h : allZero L) (ε : ℝ) : pe L ε = 0 := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    zubkx
    simp [pe, h1, ih h2]

/-- A lexicographically positive list gives an eventually positive function. -/
theorem pe_pos_of_lexPos (h : lexPos L) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < pe L ε := by
  induction L with
  | nil => exact h.elim
  | cons c L ih =>
    zulv
    · have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), (0 : ℝ) < pe _ ε :=
        continuous_const.continuousAt.eventually_lt (continuous_pe (c :: L)).continuousAt
          ztmdx
      exact nhdsWithin_le_nhds hc
    · zucrm

      simp_all

/-- A lexicographically negative list gives an eventually negative function. -/
theorem pe_neg_of_lexNeg (h : lexNeg L) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), pe L ε < 0 := by
  induction L with
  | nil => exact h.elim
  | cons c L ih =>
    zulv
    · have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), pe _ ε < (0 : ℝ) :=
        (continuous_pe (c :: L)).continuousAt.eventually_lt continuous_const.continuousAt
          ztmdx
      exact nhdsWithin_le_nhds hc
    · zucrm

      exact mul_neg_of_pos_of_neg hε0 hε

/-- **Eventual sign of a coefficient polynomial**: for all small `ε > 0` the sign of `pe L ε`
is the lexicographic sign of `L`. -/
theorem lex_ev (L : List ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ztgkv ∧ ztgku ∧
      ztgfb := by
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), lexPos L → 0 < pe L ε := by
    by_cases h : lexPos L
    · exact (pe_pos_of_lexPos h).mono by_simp_all
    simp_all
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), lexNeg L → pe L ε < 0 := by
    by_cases h : lexNeg L
    · exact (pe_neg_of_lexNeg h).mono by_simp_all
    simp_all
  filter_upwards [h1, h2] with ε e1 e2
  exact ⟨e1, e2, fun h => pe_of_allZero h ε⟩

/-- At a point where the eventual sign rules hold, positivity is lexicographic positivity. -/
theorem pos_iff_lexPos
    (h : ztgkv ∧ ztgku ∧ ztgfb) :
    0 < pe L ε ↔ lexPos L := by
  refine ⟨fun hp => ?_, h.1⟩
  zuhim
  · zuclh
  · simp_all
  grind

/-- At a point where the eventual sign rules hold, vanishing is `allZero`. -/
theorem zero_iff_allZero
    (h : ztgkv ∧ ztgku ∧ ztgfb) :
    pe L ε = 0 ↔ allZero L := by
  refine ⟨fun hp => ?_, h.2.2⟩
  zuhim
  · simp_all
  · zuclh
  simp_all

/-! ## Homogeneous representation of symbolic points -/

/-- A symbolic point as a function of the shear parameter: abscissa
`(x0 + ε x1) / (d0 + ε d1)`, ordinate `y0 + ε y1`. -/
structure Rep where
  /-- Constant coefficient of the abscissa numerator. -/
  x0 : ℝ
  /-- Linear coefficient of the abscissa numerator. -/
  x1 : ℝ
  /-- Constant coefficient of the denominator. -/
  d0 : ℝ
  /-- Linear coefficient of the denominator. -/
  d1 : ℝ
  /-- Constant coefficient of the ordinate. -/
  y0 : ℝ
  /-- Linear coefficient of the ordinate. -/
  y1 : ℝ
variable {a b : Rep}

/-- Negate numerator and denominator (the machine computes `0 - v`). -/
def Rep.neg (r : Rep) : Rep := ⟨0 - r.x0, 0 - r.x1, 0 - r.d0, 0 - r.d1, r.y0, r.y1⟩

/-- The representation of the point of the segment from `u` to `w` at the height of `v`
(sheared): denominator `dy + ε dx` normalised to have a positive lowest coefficient, the
abscissa `u.1` itself when the segment is degenerate (`dx = dy = 0`). -/
noncomputable def edgeRep (u w v : Point) : Rep :=
  if w.2 - u.2 < 0 then
    Rep.neg ⟨u.1 * ztpj + ztgv * ztor,
      u.1 * ztor + ztmu * ztor, w.2 - u.2, w.1 - u.1, v.2, v.1⟩
  else if 0 < w.2 - u.2 then
    ⟨u.1 * ztpj + ztgv * ztor,
      u.1 * ztor + ztmu * ztor, w.2 - u.2, w.1 - u.1, v.2, v.1⟩
  else if w.1 - u.1 < 0 then
    Rep.neg ⟨u.1 * ztpj + ztgv * ztor,
      u.1 * ztor + ztmu * ztor, w.2 - u.2, w.1 - u.1, v.2, v.1⟩
  else if 0 < w.1 - u.1 then
    ⟨u.1 * ztpj + ztgv * ztor,
      u.1 * ztor + ztmu * ztor, w.2 - u.2, w.1 - u.1, v.2, v.1⟩
  else ⟨u.1, 0, 1, 0, v.2, v.1⟩

/-- The representation of a symbolic point of `shear ε P`, computed from `P`. -/
noncomputable def symRep (P : Polygon) : SymPt → Rep
  | .vtx i => ⟨(P.vtx i).1, 0, 1, 0, (P.vtx i).2, (P.vtx i).1⟩
  | .onEdge e h => edgeRep zthrv ztbane ztmce

/-- The representation is correct at `ε`. -/
def RepOK (r : Rep) (p : Point) (ε : ℝ) : Prop :=
  0 < r.d0 + ε * r.d1 ∧ r.x0 + ε * r.x1 = p.1 * (r.d0 + ε * r.d1) ∧ p.2 = r.y0 + ε * r.y1

/-- The abscissa of the sheared segment point, multiplied by the denominator. -/
theorem edge_x_mul (u w v : Point) (ε : ℝ) (hne : ztpj + ε * ztor ≠ 0) :
    (u.1 + ztbaaw *
        ztytd) *
      (ztpj + ε * ztor) =
    u.1 * ztpj + ztgv * ztor +
      ε * ztysa := by
  grind

/-- **Correctness of `edgeRep`**: for all small `ε > 0` it represents the point of the
sheared segment at the sheared height of `v`. -/
theorem edgeRep_spec (u w v : Point) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), RepOK (edgeRep u w v)
      (u.1 + ztbaaw *
        ztytd, v.2 + ε * v.1) ε := by
  have hcont : Continuous fun ε : ℝ => ztpj + ε * ztor := by fun_prop
  unfold edgeRep
  by_cases h1 : w.2 - u.2 < 0
  · zuckq
    have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), ztpj + ε * ztor < 0 :=
      hcont.continuousAt.eventually_lt continuous_const.continuousAt by_simp_all
    zucfv
    have := edge_x_mul u w v ε hε.ne
    zuiff

  zuckq
  by_cases h2 : 0 < w.2 - u.2
  · zuipi
    have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), (0 : ℝ) < ztpj + ε * ztor :=
      continuous_const.continuousAt.eventually_lt hcont.continuousAt by_simp_all
    zucfv
    have := edge_x_mul u w v ε hε.ne'
    tauto
  zuipi
  have h0 : w.2 - u.2 = 0 := by_grind
  by_cases h3 : w.1 - u.1 < 0
  · zuipj
    zuepd
    have hlt : ztpj + ε * ztor < 0 := by
      rw [h0, zero_add]; exact mul_neg_of_pos_of_neg hε h3
    have := edge_x_mul u w v ε hlt.ne
    zuiff

  zuipj
  by_cases h4 : 0 < w.1 - u.1
  · zuipk
    zuepd
    have hlt : 0 < ztpj + ε * ztor := by_simp_all
    have := edge_x_mul u w v ε hlt.ne'
    tauto
  zuipk
  have h5 : w.1 - u.1 = 0 := by_grind
  refine Eventually.of_forall fun ε => ⟨by_norm_num, ?_, rfl⟩
  simp_all

/-- **Correctness of `symRep`**: for all small `ε > 0`, `symRep P s` represents the symbolic
point `s` of `shear ε P`. -/
theorem symRep_spec (P : Polygon) (s : SymPt) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), RepOK ztubm (s.eval ztsl) ε := by
  cases s with
  | vtx i =>
    refine Eventually.of_forall fun ε => ⟨by simp [symRep], ?_, ?_⟩ <;>
      simp [symRep, SymPt.eval, shear_vtx, shearPt]
  | onEdge e h =>
    have := edgeRep_spec zthrv ztbane ztmce
    refine this.mono fun ε hε => ?_
    have hev : SymPt.eval ztsl ztspt =
        ((P.vtx e).1 + (((P.vtx h).2 + ε * (P.vtx h).1) - ztiex) *
          (ztbajq /
            (((P.vtx ztwmy).2 + ε * (P.vtx ztwmy).1) -
              ztiex)), (P.vtx h).2 + ε * (P.vtx h).1) := by
      simp only [SymPt.eval, edgeXAt, Visibility.edgeX, Visibility.xAt, shear_vtx, shear_n,
        shearPt]
    rw [hev]
    exact hε

/-! ## The coefficient lists of the tests -/

/-- Abscissa order `a.1 < b.1`: `x_b d_a - x_a d_b` (padded to five coefficients). -/
def xPoly (a b : Rep) : List ℝ :=
  [b.x0 * a.d0 - a.x0 * b.d0, b.x0 * a.d1 + b.x1 * a.d0 - a.x0 * b.d1 - a.x1 * b.d0,
    b.x1 * a.d1 - a.x1 * b.d1, 0, 0]

/-- Ordinate order `a.2 < b.2`: `y_b - y_a`. -/
def yPoly (a b : Rep) : List ℝ := [b.y0 - a.y0, b.y1 - a.y1, 0, 0, 0]

/-- The orientation determinant times `d_a d_b d_c`:
`(x_b d_a - x_a d_b) d_c (y_c - y_a) - (x_c d_a - x_a d_c) d_b (y_b - y_a)`, coefficients
of the product of `A = x_b d_a - x_a d_b`, `B = d_c (y_c - y_a)`, `C = x_c d_a - x_a d_c`,
`E = d_b (y_b - y_a)`. -/
def dPoly (a b c : Rep) : List ℝ :=
  let A0 := b.x0 * a.d0 - a.x0 * b.d0
  let A1 := b.x0 * a.d1 + b.x1 * a.d0 - a.x0 * b.d1 - a.x1 * b.d0
  let A2 := b.x1 * a.d1 - a.x1 * b.d1
  let C0 := c.x0 * a.d0 - a.x0 * c.d0
  let C1 := c.x0 * a.d1 + c.x1 * a.d0 - a.x0 * c.d1 - a.x1 * c.d0
  let C2 := c.x1 * a.d1 - a.x1 * c.d1
  let B0 := c.d0 * ztthq
  let B1 := c.d0 * ztthr + c.d1 * ztthq
  let B2 := c.d1 * ztthr
  let E0 := b.d0 * zttft
  let E1 := b.d0 * zttfu + b.d1 * zttft
  let E2 := b.d1 * zttfu
  [A0 * B0 - C0 * E0,
    A0 * B1 + A1 * B0 - C0 * E1 - C1 * E0,
    A0 * B2 + A1 * B1 + A2 * B0 - C0 * E2 - C1 * E1 - C2 * E0,
    A1 * B2 + A2 * B1 - C1 * E2 - C2 * E1,
    A2 * B2 - C2 * E2]

/-- The coefficient list of test `op`. -/
def testPoly (op : ℕ) (a b c : Rep) : List ℝ :=
  match op with
  | 0 => xPoly a b
  | 1 => yPoly a b
  | _ => dPoly a b c

/-- The value of `pe` on a five-coefficient list. -/
theorem pe_five (c0 c1 c2 c3 c4 ε : ℝ) :
    pe [c0, c1, c2, c3, c4] ε = c0 + ε * c1 + ε ^ 2 * c2 + ε ^ 3 * c3 + ε ^ 4 * c4 := by
  simp only [pe]
  ring

/-- Where the representations are correct, `xPoly` is `(x_b - x_a) d_a d_b`. -/
theorem pe_xPoly {ε : ℝ} (ha : RepOK a p ε) (hb : RepOK b q ε) :
    pe ztuek ε = zttxa * (zteov * ztepd) := by
  have e : pe ztuek ε =
      ztqdt * zteov - ztjny * ztepd := by
    rw [xPoly, pe_five]; ring
  rw [e, ha.2.1, hb.2.1]
  ring

/-- Where the representations are correct, `yPoly` is `y_b - y_a`. -/
theorem pe_yPoly {ε : ℝ} (ha : RepOK a p ε) (hb : RepOK b q ε) :
    pe (yPoly a b) ε = q.2 - p.2 := by
  rw [yPoly, pe_five, ha.2.2, hb.2.2]
  ring

/-- Where the representations are correct, `dPoly` is `det · d_a d_b d_c`. -/
theorem pe_dPoly {a b c : Rep} {p q r : Point} {ε : ℝ} (ha : RepOK a p ε) (hb : RepOK b q ε)
    (hc : RepOK c r ε) :
    pe ztron ε =
      det p q r * (zteov * ztepd * ztjro) := by
  have e : pe ztron ε =
      (ztqdt * zteov - ztjny * ztepd) *
          (ztjro * ((c.y0 + ε * c.y1) - ztqdn)) -
        ((c.x0 + ε * c.x1) * zteov - ztjny * ztjro) *
          (ztepd * ((b.y0 + ε * b.y1) - ztqdn)) := by
    rw [dPoly, pe_five]; ring
  rw [e, ha.2.1, hb.2.1, hc.2.1, ← ha.2.2, ← hb.2.2, ← hc.2.2]
  zuorv
  ring

/-! ## From the eventual value to the value at `epsOf P` -/

/-- A test has the same truth value on two triples with the same sign facts. -/
theorem signTest_congr {a b d a' b' d' : Point} (h : SignFacts a b d = SignFacts a' b' d')
    (op : ℕ) : SignTest op a b d ↔ SignTest op a' b' d' := by
  simp only [SignFacts, Prod.mk.injEq] at h
  zucdw
  match op with
  | 0 => exact Iff.of_eq h1
  | 1 => exact Iff.of_eq h2
  | 2 => exact Iff.of_eq h3
  | _ + 3 => exact Iff.of_eq h4

/-- Positivity of `pe (testPoly op …)` at a point where the representations are correct is the
test `op` for `op < 3`, and vanishing is test `3`. -/
theorem signTest_iff_pe {a b c : Rep} {p q r : Point} {ε : ℝ} (ha : RepOK a p ε)
    (hb : RepOK b q ε) (hc : RepOK c r ε) (op : ℕ) :
    (op < 3 → (SignTest op p q r ↔ 0 < pe ztqxh ε)) ∧
      (op = 3 → (SignTest op p q r ↔ pe ztqxh ε = 0)) := by
  have hab := mul_pos ha.1 hb.1
  have habc := mul_pos hab hc.1
  refine ztlvx
  · match op, hop with
    | 0, _ =>
      zudcc
      rw [pe_xPoly ha hb, mul_pos_iff_of_pos_right hab, sub_pos]
    | 1, _ =>
      zudcc
      rw [pe_yPoly ha hb, sub_pos]
    | 2, _ =>
      zudcc
      rw [pe_dPoly ha hb hc, mul_pos_iff_of_pos_right habc]
  · subst hop
    zudcc
    rw [pe_dPoly ha hb hc, mul_eq_zero, or_iff_left habc.ne']

/-- **The sign tests in `Qof P` are lexicographic sign conditions** on coefficient lists
computed from `P` (tests `0, 1, 2`: positivity). -/
theorem signTest_iff_lex (P : Polygon) (hG : ∃ ε, GoodShear P ε) (s₁ s₂ s₃ : SymPt)
    (h₁ : s₁.Lt P.n) (h₂ : s₂.Lt P.n) (h₃ : s₃.Lt P.n) (op : ℕ) :
    (op < 3 → (SignTest op ztykc ztyke ztykg ↔
      lexPos ztgmo)) ∧
    (op = 3 → (SignTest op ztykc ztyke ztykg ↔
      allZero ztgmo)) := by
  obtain ⟨hε0, -, -, hstab⟩ := goodShear_epsOf hG
  set L := testPoly op _ _ _
  have hev := ((symRep_spec P s₁).and (symRep_spec P s₂)).and ((symRep_spec P s₃).and (lex_ev L))
  zufzj
  zucmu
  set ε' := min ztbfe ztbhs
  have hε'0 : 0 < ε' := by_grind
  have hε'δ : ε' < δ := by_grind
  obtain ⟨⟨r1, r2⟩, r3, hl⟩ := hsub (show ε' ∈ Ioo 0 δ from ⟨hε'0, hε'δ⟩)
  have hSF := hstab ε' hε'0 by_grind s₁ s₂ s₃ h₁ h₂ h₃
  have hT := signTest_congr hSF op
  have hP := signTest_iff_pe r1 r2 r3 op
  refine ztlvx
  · exact (hT.trans (hP.1 hop)).trans (pos_iff_lexPos hl)
  · exact (hT.trans (hP.2 hop)).trans (zero_iff_allZero hl)
open Machine Machine.Stmt Programs
def wrOK (B : ℕ → Bool) : Instr → Bool
  | .inputSize r | .constN r _ | .copyN r _ | .addN r _ _ | .subN r _ _ | .loadN r _ => B r
  | .constR r _ | .copyR r _ | .addR r _ _ | .subR r _ _ | .mulR r _ _ | .divR r _ _ => B r
  | .loadR r _ | .readX r _ | .readY r _ => B r
  | _ => false

/-- Every instruction of the statement satisfies `wrOK B`. -/
def wr (B : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrOK B i
  | .seq s t => wr B s && wr B t
  | .ifLtN _ _ t e => wr B t && wr B e
  | .ifLtR _ _ t e => wr B t && wr B e
  | .whileLtN _ _ b => wr B b
  | .whileLtR _ _ b => wr B b

/-- Registers outside `B`, both memories and the output agree. -/
def FrameB (B : ℕ → Bool) (c c' : Config) : Prop :=
  ztcjh ∧ ztbge ∧
    c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output
theorem FrameB.refl (B : ℕ → Bool) (c : Config) : FrameB B c c :=
  ⟨by_omega, by_simp_all, rfl, rfl, rfl⟩
theorem FrameB.trans {B : ℕ → Bool} {c₁ c₂ c₃ : Config} (h₁ : FrameB B c₁ c₂)
    (h₂ : FrameB B c₂ c₃) : FrameB B c₁ c₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans zthhr, fun r hr => (h₂.2.1 r hr).trans ztfsm,
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩
variable {P : Polygon} {W : ℕ}
/-- **Frame of a register-writing statement**: an execution of a statement all of whose
instructions write registers accepted by `B` changes no other register, no memory cell and
not the output. -/
theorem exec_frameB {B : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wr B s = true) : FrameB B c c' := by
  induction h with
  | skip _ => exact FrameB.refl B _
  | @instr ins c c' _ he _ _ =>
    zvnhu at hs
    cases ins <;> simp only [wrOK, Bool.false_eq_true] at hs <;>
      zvncw at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      refine ⟨fun j hj => ?_, fun j hj => ?_, rfl, rfl, rfl⟩ <;>
      first
      | rfl
      | (zvmwf; split_ifs with hh
         · simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    simp only [wr, Bool.and_eq_true] at hs
    zueot
  | ifLtN_true _ _ ih =>
    zufce
  | ifLtN_false _ _ ih =>
    zufcf
  | ifLtR_true _ _ ih =>
    zufce
  | ifLtR_false _ _ ih =>
    zufcf
  | whileLtN_false _ _ => exact FrameB.refl B _
  | whileLtN_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans zthyj
  | whileLtR_false _ _ => exact FrameB.refl B _
  | whileLtR_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans zthyj

/-! ## The lexicographic sign of a list of real registers -/

/-- The lexicographic sign of the real registers `rs` (`Z` holds `0`): `nreg Pb := 1` iff the
lowest nonzero entry is positive, `nreg Zb := 1` iff all entries vanish. -/
def lexStmt (Z Pb Zb : ℕ) : List ℕ → Stmt
  | [] => block [.constN Pb 0, .constN Zb 1]
  | r :: rs => .ifLtR Z r (block [.constN Pb 1, .constN Zb 0])
      (.ifLtR r Z (block [.constN Pb 0, .constN Zb 0]) ztqta)

/-- **Spec of `lexStmt`**: cost `≤ 4 · |rs| + 2`; the two bits are `≤ 1` and decide
`lexPos` and `allZero` of the register values. -/
theorem lexStmt_spec (Z Pb Zb : ℕ) (hne : Pb ≠ Zb) (hW : 1 ≤ W) :
    ∀ (rs : List ℕ) (c : Config), WordsBounded W c → c.rreg Z = 0 →
    ∃ c' k, Exec P W ztqta c c' k ∧ k ≤ 4 * rs.length + 2 ∧
      c'.nreg Pb ≤ 1 ∧ c'.nreg Zb ≤ 1 ∧ (c'.nreg Pb = 1 ↔ lexPos ztwcv) ∧
      (c'.nreg Zb = 1 ↔ allZero ztwcv) := by
  intro rs
  induction rs with
  | nil =>
    zuhgg

    exec_block
    · omega
    · omega
    · simp [hne, lexPos, allZero]
  | cons r rs ih =>
    zuhgg

    by_cases h1 : c.rreg Z < c.rreg r
    · refine spec_ifLtR_true h1 ?_
      have hp : 0 < c.rreg r := by_simp_all
      exec_block
      · omega
      · omega
      · zuevy
        simp [hne, lexPos, allZero, hp, hp.ne']
    · by_cases h2 : c.rreg r < c.rreg Z
      · refine spec_ifLtR_false h1 (spec_ifLtR_true h2 ?_)
        have hn : c.rreg r < 0 := by_simp_all
        exec_block
        · omega
        · omega
        · zuevy
          simp [hne, lexPos, allZero, hn.ne, not_lt.2 hn.le]
      · refine spec_ifLtR_false h1 (spec_ifLtR_false h2 ?_)
        have h0 : c.rreg r = 0 := by
          grind
        obtain ⟨c', k, ex, hk, a, b, e1, e2⟩ := ih c hc hZ
        refine ⟨c', k, ex, by_grind, a, b, ?_, ?_⟩
        · simp [lexPos, h0, e1]
        · simp [allZero, h0, e2]

/-! ## Loading a symbolic point -/

/-- `nreg 10040 := (nreg a + 1) % n` (with `nreg 10020 = n`, `nreg 10021 = 1`). -/
def succIdx (a : ℕ) : Stmt :=
  .seq (block [.addN 10040 a 10021]) (.ifLtN 10040 10020 .skip (block [.constN 10040 0]))

/-- **Spec of `succIdx`**: cost `≤ 4`, the successor index modulo `n`, only natural register
`10040` written. -/
theorem succIdx_spec (a : ℕ) (c : Config) (hc : WordsBounded W c)
    (ha : c.nreg a < P.n) (h1 : c.nreg 10021 = 1) (hn : c.nreg 10020 = P.n) (hW : P.n ≤ W) :
    ∃ c' k, Exec P W (succIdx a) c c' k ∧ k ≤ 4 ∧ c'.nreg 10040 = ztlli % P.n ∧
      c'.rreg = c.rreg ∧ (∀ r, r ≠ 10040 → c'.nreg r = c.nreg r) := by
  unfold succIdx
  refine spec_seq ?_
  exec_block
  · omega
  · by_cases hlt : c.nreg a + 1 < P.n
    · zuek
      zurc
      refine ⟨by_omega, by config_simp; rw [h1, Nat.mod_eq_of_lt hlt], rfl,
        by simp_all⟩
    · zudx
      have he : c.nreg a + 1 = P.n := by_omega
      exec_block
      · omega
      simp_all

/-- A representation held in the six real registers from `ob` on. -/
def RepAt (c : Config) (ob : ℕ) (r : Rep) : Prop :=
  c.rreg ob = r.x0 ∧ c.rreg zteuf = r.x1 ∧ c.rreg zteug = r.d0 ∧ c.rreg zteuh = r.d1 ∧
    c.rreg zthiw = r.y0 ∧ c.rreg zthix = r.y1

/-- The sign normalisation of an edge representation (`edgeRep` in terms of its inputs). -/
noncomputable def normRep (u1 dx dy x0 x1 y0 y1 : ℝ) : Rep :=
  if dy < 0 then Rep.neg ztcbz
  else if 0 < dy then ztcbz
  else if dx < 0 then Rep.neg ztcbz
  else if 0 < dx then ztcbz
  else ⟨u1, 0, 1, 0, y0, y1⟩
theorem edgeRep_eq (u w v : Point) :
    edgeRep u w v = normRep u.1 ztor ztpj
      (u.1 * ztpj + ztgv * ztor)
      ztysa v.2 v.1 := rfl

/-- Negate the numerator and the denominator at `ob`. -/
def negR (ob : ℕ) : Stmt :=
  block [.subR ob 10020 ob, .subR zteuf 10020 zteuf, .subR zteug 10020 zteug,
    .subR zteuh 10020 zteuh]

/-- The degenerate edge: abscissa `u.1`, denominator `1`. -/
def degR (ob : ℕ) : Stmt :=
  block [.copyR ob 10041, .constR zteuf 0, .constR zteug 1, .constR zteuh 0]

/-- The sign normalisation (`dy` in `rreg 10046`, `dx` in `rreg 10045`, `u.1` in `10041`). -/
def normR (ob : ℕ) : Stmt :=
  .ifLtR 10046 10020 ztvzs (.ifLtR 10020 10046 .skip
    (.ifLtR 10045 10020 ztvzs (.ifLtR 10020 10045 .skip (degR ob))))

/-- **Spec of `normR`**: cost `≤ 12`, the normalised representation. -/
theorem normR_spec (ob : ℕ) (hob : ob = 10100 ∨ ob = 10110 ∨ ob = 10120)
    {u1 dx dy x0 x1 y0 y1 : ℝ} (c : Config) (hc : WordsBounded W c) (hZ : c.rreg 10020 = 0)
    (hdx : c.rreg 10045 = dx) (hdy : c.rreg 10046 = dy) (hu : c.rreg 10041 = u1)
    (hr : RepAt c ob ztcbz) :
    ∃ c' k, Exec P W ztwaa c c' k ∧ k ≤ 12 ∧
      RepAt c' ob (normRep u1 dx dy x0 x1 y0 y1) := by
  rcases hob with rfl | rfl | rfl <;>
  · obtain ⟨r0, r1, r2, r3, r4, r5⟩ := hr
    zvmxv at r0 r1 r2 r3 r4 r5
    simp only [normR, negR, degR, Nat.reduceAdd]
    by_cases h1 : dy < 0
    · zucix
      exec_block
      zubsc
      simp only [normRep, h1, ↓reduceIte, RepAt, Rep.neg, Nat.reduceAdd]
      simp_all
    by_cases h2 : 0 < dy
    · zupb
      zucix
      zumkb
      simp only [normRep, h1, h2, ↓reduceIte, RepAt, Nat.reduceAdd]
      simp_all
    have h0 : dy = 0 := by_grind
    by_cases h3 : dx < 0
    · zupb
      zupb
      zucix
      exec_block
      zubsc
      simp only [normRep, h1, h2, h3, ↓reduceIte, RepAt, Rep.neg, Nat.reduceAdd]
      simp_all
    by_cases h4 : 0 < dx
    · zupb
      zupb
      zupb
      zucix
      zumkb
      zucrb

    · zupb
      zupb
      zupb
      zupb
      exec_block
      zubsc
      zucrb

/-- Load a vertex: `x0 = x`, `x1 = 0`, `d = 1`, `y0 = y`, `y1 = x`. -/
def loadVtx (nb ob : ℕ) : Stmt :=
  block [.readX ob ztftj, .constR zteuf 0, .constR zteug 1, .constR zteuh 0,
    .readY zthiw ztftj, .readX zthix ztftj]

/-- Load an edge point (`u` = start of the edge, `w` = its end, index in `nreg 10040`, `v` =
the height vertex): the unnormalised representation `x0 = u.1 dy + (v.2 - u.2) dx`,
`x1 = u.1 dx + (v.1 - u.1) dx`, `d = (dy, dx)`, `y = (v.2, v.1)`. -/
def loadEdge (nb ob : ℕ) : Stmt :=
  block [.readX 10041 ztftj, .readY 10042 ztftj, .readX 10043 10040, .readY 10044 10040,
    .readX zthix ztttz, .readY zthiw ztttz, .subR 10045 10043 10041,
    .subR 10046 10044 10042, .subR 10047 zthiw 10042, .subR 10048 zthix 10041,
    .mulR 10049 10041 10046, .mulR 10050 10047 10045, .addR ob 10049 10050,
    .mulR 10049 10041 10045, .mulR 10050 10048 10045, .addR zteuf 10049 10050,
    .copyR zteug 10046, .copyR zteuh 10045]

/-- Load the symbolic point held in `nreg nb … nb + 2` as a representation at `rreg ob … ob + 5`. -/
def loadPt (nb ob : ℕ) : Stmt :=
  .ifLtN nb 10021 (loadVtx nb ob) (.seq (succIdx ztftj) (.seq (loadEdge nb ob) ztwaa))

/-- **Spec of `loadPt`** (for the three slots used by the kernel): cost `≤ 40`, the registers
from `ob` on hold `symRep P s`. -/
theorem loadPt_spec (nb ob : ℕ)
    (hj : (nb = 10000 ∧ ob = 10100) ∨ (nb = 10003 ∧ ob = 10110) ∨ (nb = 10006 ∧ ob = 10120))
    (c : Config) (hc : WordsBounded W c) (hn : c.nreg 10020 = P.n) (h1 : c.nreg 10021 = 1)
    (hZ : c.rreg 10020 = 0) (hW : P.n ≤ W) (s : SymPt) (hs : s.Lt P.n) (hin : SymPtIn c nb s) :
    ∃ c' k, Exec P W (loadPt nb ob) c c' k ∧ k ≤ 40 ∧ RepAt c' ob ztubm := by
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · cases s with
    | vtx i =>
      obtain ⟨hk, hi⟩ := hin
      zvmxv at hi
      simp only [loadPt, loadVtx, Nat.reduceAdd]
      zudd
      exec_block
      zubsc
      simp only [RepAt, symRep, Nat.reduceAdd]
      config_simp
      simp only [hi, Int.cast_zero, Int.cast_one, and_self]
    | onEdge e h =>
      obtain ⟨hk, he, hh⟩ := hin
      zvmxv at he hh
      simp only [loadPt, loadEdge, Nat.reduceAdd]
      zubv
      zujl
      refine spec_use (succIdx_spec _ c hc (by zvmxm; exact hs.1) h1 hn hW) ?_
      rintro c1 k1 hk1 hw1 ⟨hidx, hrr, hnr⟩
      have e1 : c1.nreg _ = e := (hnr _ by_norm_num).trans he
      have e2 : c1.nreg _ = h := (hnr _ by_norm_num).trans hh
      zvmxm at hidx
      refine spec_seq ?_
      exec_block
      refine spec_use (normR_spec _ by_norm_num _ ‹_› (dx := (P.vtx ztwmy).1 - (P.vtx e).1)
        (dy := (P.vtx ztwmy).2 - (P.vtx e).2)
        (x0 := (P.vtx e).1 * ((P.vtx ztwmy).2 - (P.vtx e).2) +
          ((P.vtx h).2 - (P.vtx e).2) * ztbajq)
        (x1 := (P.vtx e).1 * ztbajq +
          ((P.vtx h).1 - (P.vtx e).1) * ztbajq)
        (y0 := (P.vtx h).2) (y1 := (P.vtx h).1)
        (by config_simp; grind) (by config_simp; grind)
        (by config_simp; grind) (by config_simp; rw [e1])
        (by simp only [RepAt, Nat.reduceAdd]; config_simp; grind))
        ?_
      intro c' k2 hk2 _ hrep
      zubsc
      rw [symRep, edgeRep_eq]
      exact hrep

/-! ## The prelude, the coefficient lists, the selection and the final bit -/

/-- Constants: `nreg 10020 := n`, `nreg 10021 := 1`, `nreg 10022 := 2`, `nreg 10023 := 3`,
`rreg 10020 := 0`. -/
def prelude : Stmt :=
  block [.inputSize 10020, .constN 10021 1, .constN 10022 2, .constN 10023 3, .constR 10020 0]

/-- **Spec of `prelude`**: cost `5`. -/
theorem prelude_spec (c : Config) (hc : WordsBounded W c) (hW : P.n + 3 ≤ W) :
    ∃ c' k, Exec P W prelude c c' k ∧ k ≤ 5 ∧ c'.nreg 10020 = P.n ∧ c'.nreg 10021 = 1 ∧
      c'.nreg 10022 = 2 ∧ c'.nreg 10023 = 3 ∧ c'.rreg 10020 = 0 := by
  unfold prelude
  exec_block
  · omega
  · omega
  · omega
  · omega
  simp

/-- The coefficient lists of all tests, from the representations at `10100`, `10110`, `10120`:
`A = x_b d_a - x_a d_b` at `10200`, `C = x_c d_a - x_a d_c` at `10203`, `y_b - y_a` at `10206`,
`y_c - y_a` at `10208`, `B = d_c (y_c - y_a)` at `10210`, `E = d_b (y_b - y_a)` at `10213`,
`A B - C E` at `10216 … 10220`; scratch `10300, 10301`.  Exactly `71` instructions. -/
def polyStmt : Stmt :=
  block [.mulR 10300 10110 10102, .mulR 10301 10100 10112, .subR 10200 10300 10301,
    .mulR 10300 10110 10103, .mulR 10301 10111 10102, .addR 10300 10300 10301,
    .mulR 10301 10100 10113, .subR 10300 10300 10301, .mulR 10301 10101 10112,
    .subR 10201 10300 10301, .mulR 10300 10111 10103, .mulR 10301 10101 10113,
    .subR 10202 10300 10301, .mulR 10300 10120 10102, .mulR 10301 10100 10122,
    .subR 10203 10300 10301, .mulR 10300 10120 10103, .mulR 10301 10121 10102,
    .addR 10300 10300 10301, .mulR 10301 10100 10123, .subR 10300 10300 10301,
    .mulR 10301 10101 10122, .subR 10204 10300 10301, .mulR 10300 10121 10103,
    .mulR 10301 10101 10123, .subR 10205 10300 10301, .subR 10206 10114 10104,
    .subR 10207 10115 10105, .subR 10208 10124 10104, .subR 10209 10125 10105,
    .mulR 10210 10122 10208, .mulR 10300 10122 10209, .mulR 10301 10123 10208,
    .addR 10211 10300 10301, .mulR 10212 10123 10209, .mulR 10213 10112 10206,
    .mulR 10300 10112 10207, .mulR 10301 10113 10206, .addR 10214 10300 10301,
    .mulR 10215 10113 10207, .mulR 10300 10200 10210, .mulR 10301 10203 10213,
    .subR 10216 10300 10301, .mulR 10300 10200 10211, .mulR 10301 10201 10210,
    .addR 10300 10300 10301, .mulR 10301 10203 10214, .subR 10300 10300 10301,
    .mulR 10301 10204 10213, .subR 10217 10300 10301, .mulR 10300 10200 10212,
    .mulR 10301 10201 10211, .addR 10300 10300 10301, .mulR 10301 10202 10210,
    .addR 10300 10300 10301, .mulR 10301 10203 10215, .subR 10300 10300 10301,
    .mulR 10301 10204 10214, .subR 10300 10300 10301, .mulR 10301 10205 10213,
    .subR 10218 10300 10301, .mulR 10300 10201 10212, .mulR 10301 10202 10211,
    .addR 10300 10300 10301, .mulR 10301 10204 10215, .subR 10300 10300 10301,
    .mulR 10301 10205 10214, .subR 10219 10300 10301, .mulR 10300 10202 10212,
    .mulR 10301 10205 10215, .subR 10220 10300 10301]

/-- **Spec of `polyStmt`**: cost `≤ 71`; the registers hold `xPoly`, `yPoly` and `dPoly` of the
three representations. -/
theorem polyStmt_spec (c : Config) (hc : WordsBounded W c) {ra rb rc : Rep}
    (ha : RepAt c 10100 ra) (hb : RepAt c 10110 rb) (hcc : RepAt c 10120 rc) :
    ∃ c' k, Exec P W polyStmt c c' k ∧ k ≤ 71 ∧
      [c'.rreg 10200, c'.rreg 10201, c'.rreg 10202, 0, 0] = xPoly ra rb ∧
      [c'.rreg 10206, c'.rreg 10207, 0, 0, 0] = yPoly ra rb ∧
      [c'.rreg 10216, c'.rreg 10217, c'.rreg 10218, c'.rreg 10219, c'.rreg 10220] =
        dPoly ra rb rc := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := ha
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hb
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := hcc
  zvmxv at a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 c1 c2 c3 c4 c5
  unfold polyStmt
  exec_block
  refine ztcbn <;>
    simp only [xPoly, yPoly, dPoly, List.cons.injEq, and_true] <;> config_simp <;>
    simp only [a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4, c5, and_self]

/-- Select the coefficient list of test `nreg 10009` into `rreg 10400 … 10404`. -/
def selStmt : Stmt :=
  .ifLtN 10009 10021
    (block [.copyR 10400 10200, .copyR 10401 10201, .copyR 10402 10202, .constR 10403 0,
      .constR 10404 0])
    (.ifLtN 10009 10022
      (block [.copyR 10400 10206, .copyR 10401 10207, .constR 10402 0, .constR 10403 0,
        .constR 10404 0])
      (block [.copyR 10400 10216, .copyR 10401 10217, .copyR 10402 10218, .copyR 10403 10219,
        .copyR 10404 10220]))
theorem testPoly_of_two_le {op : ℕ} (h : 2 ≤ op) (a b c : Rep) : testPoly op a b c = dPoly a b c := by
  match op, h with
  | n + 2, _ => rfl

/-- **Spec of `selStmt`**: cost `≤ 9`; the selected registers hold `testPoly op`. -/
theorem selStmt_spec (c : Config) (hc : WordsBounded W c) {ra rb rc : Rep}
    (h1 : c.nreg 10021 = 1) (h2 : c.nreg 10022 = 2)
    (hx : [c.rreg 10200, c.rreg 10201, c.rreg 10202, 0, 0] = xPoly ra rb)
    (hy : [c.rreg 10206, c.rreg 10207, 0, 0, 0] = yPoly ra rb)
    (hd : [c.rreg 10216, c.rreg 10217, c.rreg 10218, c.rreg 10219, c.rreg 10220] =
      dPoly ra rb rc) :
    ∃ c' k, Exec P W selStmt c c' k ∧ k ≤ 9 ∧
      [10400, 10401, 10402, 10403, 10404].map c'.rreg = testPoly ztqhi ra rb rc := by
  unfold selStmt
  by_cases hA : c.nreg 10009 < 1
  · zudd
    have hop : c.nreg 10009 = 0 := by_omega
    exec_block
    zubsc
    rw [hop, testPoly, ← hx]
    simp
  · zubv
    by_cases hB : c.nreg 10009 < 2
    · zudd
      have hop : c.nreg 10009 = 1 := by_omega
      exec_block
      zubsc
      rw [hop, testPoly, ← hy]
      simp
    · zubv
      exec_block
      zubsc
      rw [testPoly_of_two_le by_omega, ← hd]
      simp

/-- The output bit: the positivity bit for tests `0, 1, 2`, the zero bit for test `3`. -/
def finStmt : Stmt :=
  .ifLtN 10009 10023 (.instr (.copyN 10010 10410)) (.instr (.copyN 10010 10411))

/-- **Spec of `finStmt`**: cost `≤ 3`. -/
theorem finStmt_spec (c : Config) (hc : WordsBounded W c)
    (h3 : c.nreg 10023 = 3) :
    ∃ c' k, Exec P W finStmt c c' k ∧ k ≤ 3 ∧
      (c.nreg 10009 < 3 → c'.nreg 10010 = c.nreg 10410) ∧
      (¬ c.nreg 10009 < 3 → c'.nreg 10010 = c.nreg 10411) := by
  unfold finStmt
  by_cases h : c.nreg 10009 < 3
  · zudd
    zumjy
  · zubv
    zumjy
def Bpre (r : ℕ) : Bool := decide (10020 ≤ r ∧ r < 10024)
/-- Registers written by `loadPt _ ob`. -/
def Bload (ob r : ℕ) : Bool := decide (10040 ≤ r ∧ r < 10051) || decide (ob ≤ r ∧ r < ob + 6)
/-- Registers written by `polyStmt`. -/
def Bpoly (r : ℕ) : Bool := decide (10200 ≤ r ∧ r < 10302)
/-- Registers written by `selStmt`. -/
def Bsel (r : ℕ) : Bool := decide (10400 ≤ r ∧ r < 10405)
/-- Registers written by `lexStmt`. -/
def Blex (r : ℕ) : Bool := decide (10410 ≤ r ∧ r < 10412)

/-- **The sign kernel.** -/
def signProg : Stmt :=
  .seq prelude (.seq (loadPt 10000 10100) (.seq (loadPt 10003 10110) (.seq (loadPt 10006 10120)
    (.seq polyStmt (.seq selStmt
      (.seq (lexStmt 10020 10410 10411 [10400, 10401, 10402, 10403, 10404]) finStmt))))))

/-- A symbolic point is determined by its registers. -/
theorem symPtIn_unique {c : Config} {r : ℕ} {s s' : SymPt} (h : SymPtIn c r s)
    (h' : SymPtIn c r s') : s = s' := by
  cases s with
  | vtx i =>
    cases s' with
    | vtx i' => simp only [SymPtIn] at h h'; rw [← h.2, ← h'.2]
    | onEdge e' h'' => simp only [SymPtIn] at h h'; omega
  | onEdge e hh =>
    cases s' with
    | vtx i' => simp only [SymPtIn] at h h'; omega
    | onEdge e' h'' => simp only [SymPtIn] at h h'; rw [← h.2.1, ← h'.2.1, ← h.2.2, ← h'.2.2]
variable {c c' : Config}
/-- A symbolic point in registers survives when its three registers do. -/
theorem symPtIn_of_eq {r : ℕ} {s : SymPt} (h : SymPtIn c r s)
    (he : ∀ j, r ≤ j → j < r + 3 → c'.nreg j = c.nreg j) : SymPtIn c' r s := by
  cases s with
  | vtx i =>
    exact ⟨(he r le_rfl by_omega).trans h.1, (he ztgu by_omega by_omega).trans h.2⟩
  | onEdge e hh =>
    exact ⟨(he r le_rfl by_omega).trans h.1, (he ztgu by_omega by_omega).trans h.2.1,
      (he ztbcu by_omega by_omega).trans h.2.2⟩

/-- A representation in registers survives when its six registers do. -/
theorem repAt_of_eq {ob : ℕ} {r : Rep} (h : RepAt c ob r)
    (he : ∀ j, ob ≤ j → j < ob + 6 → c'.rreg j = c.rreg j) : RepAt c' ob r :=
  ⟨(he ob le_rfl by_omega).trans h.1, (he zteuf by_omega by_omega).trans h.2.1,
    (he zteug by_omega by_omega).trans h.2.2.1,
    (he zteuh by_omega by_omega).trans h.2.2.2.1,
    (he zthiw by_omega by_omega).trans h.2.2.2.2.1,
    (he zthix by_omega by_omega).trans h.2.2.2.2.2⟩
end
end SignK
namespace SweepPrim
open Machine Machine.Stmt Programs SignK
@[expose] public section
variable {B B' : ℕ → Bool}
/-- Monotonicity of the write check in the accepted set. -/
theorem wr_mono {s : Stmt} (h : wr B s = true)
    (hB : ∀ r, B r = true → B' r = true) : wr B' s = true := by
  induction s with
  | skip => rfl
  | instr i =>
    zvnhu at h ⊢
    cases i <;> simp only [wrOK] at h ⊢ <;> first | exact hB _ h | exact h
  | seq s t ihs iht =>
    simp only [wr, Bool.and_eq_true] at h ⊢; exact ⟨ihs h.1, iht h.2⟩
  | ifLtN a b t e iht ihe =>
    zufcd
  | ifLtR a b t e iht ihe =>
    zufcd
  | whileLtN a b body ih => zvnhu at h ⊢; exact ih h
  | whileLtR a b body ih => zvnhu at h ⊢; exact ih h

/-- A register frame for fewer registers is one for more. -/
theorem frameB_mono {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r by_grind, fun r hr => h.2.1 r (by
    grind), h.2.2⟩

/-! ## Formulas -/

/-- **A Boolean formula** over bit registers. -/
inductive BF where
  /-- The bit held in register `r` (true iff it is `1`). -/
  | var (r : ℕ)
  /-- A constant. -/
  | const (b : Bool)
  /-- Negation. -/
  | not (f : BF)
  /-- Conjunction. -/
  | and (f g : BF)
  /-- Disjunction. -/
  | or (f g : BF)
namespace BF

/-- The value of a formula under an assignment of the variables. -/
def eval (v : ℕ → Bool) : BF → Bool
  | var r => v r
  | const b => b
  | not f => !(f.eval v)
  | and f g => f.eval v && g.eval v
  | or f g => f.eval v || g.eval v

/-- The number of nodes. -/
def size : BF → ℕ
  | var _ => 1
  | const _ => 1
  | not f => f.size + 1
  | and f g => f.size + g.size + 1
  | or f g => f.size + g.size + 1
theorem one_le_size (f : BF) : 1 ≤ f.size := by
  cases f <;> zunlj <;> omega

/-- Every variable register satisfies `p`. -/
def VarsOK (p : ℕ → Prop) : BF → Prop
  | var r => p r
  | const _ => True
  | not f => f.VarsOK p
  | and f g => f.VarsOK p ∧ g.VarsOK p
  | or f g => f.VarsOK p ∧ g.VarsOK p
theorem VarsOK.mono {p q : ℕ → Prop} (hpq : ∀ r, p r → q r) :
    ∀ {f : BF}, f.VarsOK p → f.VarsOK q
  | var r, h => hpq r h
  | const _, _ => trivial
  | not f, h => VarsOK.mono hpq (f := f) h
  | and f g, h => ⟨VarsOK.mono hpq (f := f) h.1, VarsOK.mono hpq (f := g) h.2⟩
  | or f g, h => ⟨VarsOK.mono hpq (f := f) h.1, VarsOK.mono hpq (f := g) h.2⟩

/-- **The branch-free compiler**: the value of `f` into `d`, scratch `d + 1 …`. -/
def compile : BF → ℕ → Stmt
  | var r, d => .instr (.copyN d r)
  | const b, d => .instr (.constN d b.toNat)
  | not f, d => .seq ztjvb ztxwb
  | and f g, d => .seq ztjvb (.seq ztbahw
      (block [.addN d d ztet, .constN ztet 1, .subN d d ztet]))
  | or f g, d => .seq ztjvb (.seq ztbahw
      (block [.addN d d ztet, .constN ztet 1, .subN ztet d ztet,
        .subN d d ztet]))

/-- The registers the compiled block may write. -/
def wset (f : BF) (d : ℕ) (r : ℕ) : Bool := decide (d ≤ r ∧ r ≤ d + f.size)
theorem wr_compile : ∀ (f : BF) (d : ℕ), wr ztqmw ztjvb = true
  | var r, d => by zunuj
  | const b, d => by zunuj
  | not f, d => by
    have h := wr_mono ztojw (B' := (not f).wset d) (fun r hr => by
      zufy
      grind)
    have h1 := one_le_size f
    simp only [compile, wr]
    zuzx
    simp only [block, wr, wrOK, wset, size, Bool.true_and, Bool.and_true, Bool.and_eq_true]
    simp
  | and f g, d => by
    have hf := wr_mono ztojw (B' := (and f g).wset d) (fun r hr => by
      zufy
      grind)
    have hg := wr_mono ztzym (B' := (and f g).wset d) (fun r hr => by
      zufy
      grind)
    zusr

  | or f g, d => by
    have hf := wr_mono ztojw (B' := (or f g).wset d) (fun r hr => by
      zufy
      grind)
    have hg := wr_mono ztzym (B' := (or f g).wset d) (fun r hr => by
      zufy
      grind)
    zusr

/-- **The compiled formula computes its value.**  If every variable is a register below `d`
holding a bit, the block writes `(f.eval …).toNat` into `d` (at most `4 · size f` steps) and
changes only the registers `d … d + size f`. -/
theorem compile_exec {P : Polygon} {W : ℕ} (hW : 2 ≤ W) :
    ∀ (f : BF) (d : ℕ) (c : Config), WordsBounded W c →
      f.VarsOK (fun r => r < d ∧ c.nreg r ≤ 1) →
      ∃ c' k, Exec P W ztjvb c c' k ∧ k ≤ 4 * f.size ∧
        c'.nreg d = (f.eval fun r => decide ztdmw).toNat ∧ FrameB ztqmw c c'
  | var r, d, c, hw, hv => by
    obtain ⟨hr, hb⟩ := hv
    refine ⟨_, 1, Exec.copyN (P := P) hw d r, by_tauto, ?_,
      exec_frameB (Exec.copyN (P := P) hw d r) (wr_compile (var r) d)⟩
    zufbl
    config_simp
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h <;> zumxk
  | const b, d, c, hw, _ => by
    have hb : b.toNat ≤ W := by cases b <;> simp; omega
    refine ⟨_, 1, Exec.constN (P := P) hw d _ hb, by_tauto, by simp [eval],
      exec_frameB (Exec.constN (P := P) hw d _ hb) (wr_compile (const b) d)⟩
  | not f, d, c, hw, hv => by
    obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := compile_exec (P := P) hW f d c hw hv
    zuka
    have e₂ : ∃ c₂ k₂, Exec P W ztxwb c₁ c₂ k₂ ∧
        k₂ = 2 ∧ c₂.nreg d = 1 - c₁.nreg d := by
      exec_block
      · omega
      simp
    obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ := e₂
    have ex : Exec P W ((not f).compile d) c c₂ ztbct := .seq e₁ e₂
    refine ⟨c₂, _, ex, by zunlj; omega, ?_, exec_frameB ex (wr_compile (not f) d)⟩
    rw [v₂, v₁]
    zufbl
    cases f.eval _ <;> rfl
  | and f g, d, c, hw, hv => by
    obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := compile_exec (P := P) hW f d c hw (VarsOK.mono (by
      omega) hv.1)
    zuka
    have keep : ztkop := fun r hr =>
      f₁.1 r ztkva
    obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := compile_exec (P := P) hW g ztet c₁ hw₁ (VarsOK.mono (by
      grind) hv.2)
    zuja
    zubal

    have e₃ : ∃ c₃ k₃, Exec P W (block [.addN d d ztet, .constN ztet 1,
        .subN d d ztet]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
        c₃.nreg d = c₂.nreg d + c₂.nreg ztet - 1 := by
      exec_block
      · omega
      · omega
      simp
    zueih
    have ex : Exec P W ((and f g).compile d) c c₃ ztxee := .seq e₁ ztcr
    refine ⟨c₃, _, ex, by zunlj; omega, ?_, exec_frameB ex (wr_compile (and f g) d)⟩
    zugxj
    have hg : ztjxa = g.eval fun r => decide ztdmw :=
      eval_congr (p := fun r => r < d ∧ c.nreg r ≤ 1) ztcvp hv.2
    zuguv
    zufbl
    cases f.eval _ <;> cases g.eval _ <;> rfl
  | or f g, d, c, hw, hv => by
    obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := compile_exec (P := P) hW f d c hw (VarsOK.mono (by
      omega) hv.1)
    zuka
    have keep : ztkop := fun r hr =>
      f₁.1 r ztkva
    obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := compile_exec (P := P) hW g ztet c₁ hw₁ (VarsOK.mono (by
      grind) hv.2)
    zuja
    zubal

    have e₃ : ∃ c₃ k₃, Exec P W (block [.addN d d ztet, .constN ztet 1,
        .subN ztet d ztet, .subN d d ztet]) c₂ c₃ k₃ ∧ k₃ = 4 ∧
        c₃.nreg d = (c₂.nreg d + c₂.nreg ztet) - (c₂.nreg d + c₂.nreg ztet - 1) := by
      exec_block
      · omega
      · omega
      simp
    zueih
    have ex : Exec P W ((or f g).compile d) c c₃ ztxee := .seq e₁ ztcr
    refine ⟨c₃, _, ex, by zunlj; omega, ?_, exec_frameB ex (wr_compile (or f g) d)⟩
    zugxj
    have hg : ztjxa = g.eval fun r => decide ztdmw :=
      eval_congr (p := fun r => r < d ∧ c.nreg r ≤ 1) ztcvp hv.2
    zuguv
    zufbl
    cases f.eval _ <;> cases g.eval _ <;> rfl
where
  /-- The value depends only on the variables. -/
  eval_congr {v v' : ℕ → Bool} {p : ℕ → Prop} {f : BF} (h : ∀ r, p r → v r = v' r)
      (hf : f.VarsOK p) : f.eval v = f.eval v' := by
    induction f with
    | var r => exact h r hf
    | const b => rfl
    | not f ih => simp only [eval, ih hf]
    | and f g ihf ihg => zunqv
    | or f g ihf ihg => zunqv
end BF
end
end SweepPrim
namespace BuildRam
open Machine Machine.Stmt
@[expose] public section
def Instr.ren (f : ℕ → ℕ) : Instr → Instr
  | .halt => .halt
  | .inputSize r => .inputSize ztyi
  | .constN r k => .constN ztyi k
  | .copyN r a => .copyN ztyi ztbaa
  | .addN r a b => .addN ztyi ztbaa ztcpx
  | .subN r a b => .subN ztyi ztbaa ztcpx
  | .loadN r a => .loadN ztyi ztbaa
  | .storeN a r => .storeN ztbaa ztyi
  | .constR r z => .constR ztyi z
  | .copyR r a => .copyR ztyi ztbaa
  | .addR r a b => .addR ztyi ztbaa ztcpx
  | .subR r a b => .subR ztyi ztbaa ztcpx
  | .mulR r a b => .mulR ztyi ztbaa ztcpx
  | .divR r a b => .divR ztyi ztbaa ztcpx
  | .loadR r a => .loadR ztyi ztbaa
  | .storeR a r => .storeR ztbaa ztyi
  | .readX r a => .readX ztyi ztbaa
  | .readY r a => .readY ztyi ztbaa
  | .jump l => .jump l
  | .brLtN a b l => .brLtN ztbaa ztcpx l
  | .brLtR a b l => .brLtR ztbaa ztcpx l
  | .emit a b d => .emit ztbaa ztcpx ztvqe

/-- Rename the registers of a statement. -/
def Stmt.ren (f : ℕ → ℕ) : Stmt → Stmt
  | .skip => .skip
  | .instr i => .instr ztsyh
  | .seq s t => .seq ztfor ztnpm
  | .ifLtN a b t e => .ifLtN ztbaa ztcpx ztnpm zttdd
  | .ifLtR a b t e => .ifLtR ztbaa ztcpx ztnpm zttdd
  | .whileLtN a b s => .whileLtN ztbaa ztcpx ztfor
  | .whileLtR a b s => .whileLtR ztbaa ztcpx ztfor

/-- The configuration seen through the renaming: register `f r` holds what `c` holds in `r`
(for an involution `f`). -/
def cfgRen (f : ℕ → ℕ) (c : Config) : Config :=
  { c with nreg := fun r => c.nreg (f r), rreg := fun r => c.rreg (f r) }
variable {f : ℕ → ℕ}
theorem upd_ren {α : Type} (hf : ∀ r, f ztyi = r) (g : ℕ → α) (i : ℕ) (v : α) :
    (fun r => upd g i v ztyi) = upd (fun r => g ztyi) ztmjd v := by
  funext r
  zudlr
  grind
theorem cfgRen_cfgRen (hf : ∀ r, f ztyi = r) (c : Config) : cfgRen f ztjst = c := by
  cases c; simp [cfgRen, hf]
theorem wordsBounded_ren (hf : ∀ r, f ztyi = r) (c : Config) {W : ℕ} :
    WordsBounded W ztjst ↔ WordsBounded W c := by
  constructor
  · zubf
    refine ztpfj
    have := h1 ztyi; simp only [cfgRen, hf] at this; omega
  · rintro ⟨h1, h2⟩; tauto
theorem isStraight_ren {ins : Instr} (h : ins.IsStraight) : (Instr.ren f ins).IsStraight := by
  cases ins <;> simp_all [Instr.ren]
theorem effect_ren (hf : ∀ r, f ztyi = r) {P : Polygon} {ins : Instr} {c c' : Config}
    (h : ins.effect P c = some c') :
    (Instr.ren f ins).effect P ztjst = some ztnwx := by
  cases ins <;> simp only [Instr.effect, Instr.ren, Option.some.injEq, reduceCtorEq] at h ⊢ <;>
    (try split at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    (try subst h) <;> simp_all [cfgRen, upd_ren hf]

/-- **Renaming registers preserves executions.** -/
theorem Exec.ren (hf : ∀ r, f ztyi = r) {P : Polygon} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) : Exec P W ztfor ztjst ztnwx k := by
  induction h with
  | skip hw => exact .skip ztejj
  | instr hs he hw hw' =>
    exact .instr (isStraight_ren hs) (effect_ren hf he) ztejj
      ((wordsBounded_ren hf _).2 hw')
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true ztbfy ih
  | ifLtN_false ht _ ih => exact .ifLtN_false ztbfy ih
  | ifLtR_true ht _ ih => exact .ifLtR_true ztbfy ih
  | ifLtR_false ht _ ih => exact .ifLtR_false ztbfy ih
  | whileLtN_false ht hw =>
    exact .whileLtN_false ztbfy ztejj
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ztbfy ih₁ ih₂
  | whileLtR_false ht hw =>
    exact .whileLtR_false ztbfy ztejj
  | whileLtR_true ht _ _ ih₁ ih₂ => exact .whileLtR_true ztbfy ih₁ ih₂

/-- **Running a renamed statement**: an execution of `s` from the renamed view of `d` gives an
execution of `s.ren f` from `d`. -/
theorem exec_of_ren (hf : ∀ r, f ztyi = r) {P : Polygon} {W : ℕ} {s : Stmt} {d c' : Config}
    {k : ℕ} (h : Exec P W s (cfgRen f d) c' k) :
    Exec P W ztfor d ztnwx k := by
  have := Exec.ren hf h
  rwa [cfgRen_cfgRen hf] at this

/-! ## Write sets -/
open SignK (wr wrOK)
variable {B B' : ℕ → Bool}
theorem wrOK_mono (hB : ∀ r, B r = true → B' r = true) {i : Instr}
    (h : wrOK B i = true) : wrOK B' i = true := by
  cases i <;> simp_all [wrOK]

/-- A larger write set. -/
theorem wr_mono (hB : ∀ r, B r = true → B' r = true) {s : Stmt}
    (h : wr B s = true) : wr B' s = true := by
  induction s <;> simp_all [wr, wrOK_mono hB]
theorem wrOK_ren {f : ℕ → ℕ} (_hf : ∀ r, f ztyi = r) (B : ℕ → Bool) (i : Instr) :
    wrOK B ztsyh = wrOK ztzfi i := by
  cases i <;> simp [wrOK, Instr.ren]
theorem wr_ren {f : ℕ → ℕ} (hf : ∀ r, f ztyi = r) (B : ℕ → Bool) (s : Stmt) :
    wr B ztfor = wr ztzfi s := by
  induction s <;> simp_all [wr, Stmt.ren, wrOK_ren hf]

/-! ## The swap of bands used by `BuildNF` -/

/-- The involution: `40000 … 40999 ↔ 50000 … 50999`, `41000 … 41999 ↔ 90000 … 90999`. -/
def σ (r : ℕ) : ℕ :=
  if 40000 ≤ r ∧ r < 41000 then r + 10000
  else if 50000 ≤ r ∧ r < 51000 then r - 10000
  else if 41000 ≤ r ∧ r < 42000 then r + 49000
  else if 90000 ≤ r ∧ r < 91000 then r - 49000
  else r
theorem σ_σ (r : ℕ) : σ ztewy = r := by
  zumvp

/-- The renamed view: register `r` of the view holds register `σ r`. -/
theorem cfgRen_nreg (c : Config) (r : ℕ) : (cfgRen σ c).nreg r = c.nreg ztewy := rfl
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core.Cluster
open Chazelle.Separator
@[expose] public section
variable {V' F' D' : Type*}

/-- The rotation system `G` encodes the map `M'`. -/
structure EnvEnc (G : Env) (M' : CombMap V' F' D') (eV : V' → ℕ) (eD : D' → ℕ) : Prop where
  eV_lt : ∀ v, eV v < G.nv
  eV_inj : Function.Injective eV
  eV_surj : ∀ u, u < G.nv → ∃ v, eV v = u
  eD_lt : ∀ d, eD d < G.N
  eD_inj : Function.Injective eD
  eD_surj : ∀ e, e < G.N → ∃ d, eD d = e
  opp : ∀ d, G.opp ztgim = eD (M'.opp d)
  rot : ∀ d, G.rot ztgim = eD (M'.rot d)
  vert : ∀ d, G.vert ztgim = eV (M'.vert d)
  first : ∀ v, ∃ d, G.first (eV v) = eD d ∧ M'.vert d = v
namespace EnvEnc
variable {G : Env} {M' : CombMap V' F' D'} {eV : V' → ℕ} {eD : D' → ℕ}
theorem iterate_rot (h : EnvEnc G M' eV eD) (n : ℕ) (d : D') :
    G.rot^[n] ztgim = eD ((M'.rot ^ n) d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, h.rot, ih, pow_succ, Equiv.Perm.mul_apply]

/-- **The encoded rotation system is well formed.** -/
theorem ok [Finite D'] (h : EnvEnc G M' eV eD) : G.OK := by
  refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_, fun e he e' he' hee => ?_,
    fun e he => ?_, fun e he e' he' hee => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨d, rfl⟩ := h.eD_surj e he; rw [h.opp]; exact h.eD_lt _
  · obtain ⟨d, rfl⟩ := h.eD_surj e he; rw [h.rot]; exact h.eD_lt _
  · obtain ⟨d, rfl⟩ := h.eD_surj e he; rw [h.vert]; exact h.eV_lt _
  · zubox
    zugoy
    rw [h.rot, h.rot] at hee
    rw [M'.rot.injective (h.eD_inj hee)]
  · obtain ⟨d, rfl⟩ := h.eD_surj e he; rw [h.rot, h.vert, h.vert, M'.vert_rot]
  · zubox
    zugoy
    rw [h.vert, h.vert] at hee
    obtain ⟨n, hn⟩ := (M'.sameCycle_of_vert d d' (h.eV_inj hee)).exists_nat_pow_eq
    exact ⟨n, by rw [h.iterate_rot, hn]⟩
  · zugqu
    obtain ⟨d, hd, -⟩ := h.first v
    zvnej; exact h.eD_lt _
  · zugqu
    obtain ⟨d, hd, hvd⟩ := h.first v
    rw [hd, h.vert, hvd]
theorem head (h : EnvEnc G M' eV eD) (d : D') : G.head ztgim = eV (M'.head d) := by
  unfold Env.head CombMap.head
  rw [h.opp, h.vert]

/-- **Steps between encoded vertices.** -/
theorem step_iff (h : EnvEnc G M' eV eD) (u w : V') :
    G.Step ztjuq ztmiy ↔ ∃ d, G.db ztgim ≠ 1 ∧ M'.vert d = u ∧ M'.head d = w ∧
      G.vb ztjuq ≠ 1 ∧ G.vb ztmiy ≠ 1 := by
  constructor
  · rintro ⟨e, he, hdb, hve, hhe, hu, hw⟩
    zubox
    zukrn
    zukrk
    exact ⟨d, hdb, h.eV_inj hve, h.eV_inj hhe, hu, hw⟩
  · rintro ⟨d, hdb, rfl, rfl, hu, hw⟩
    exact ⟨eD d, h.eD_lt d, hdb, h.vert d, h.head d, hu, hw⟩

/-- The typed step relation read through the encodings. -/
def TStep (G : Env) (M' : CombMap V' F' D') (eV : V' → ℕ) (eD : D' → ℕ) (u w : V') : Prop :=
  ∃ d, G.db ztgim ≠ 1 ∧ M'.vert d = u ∧ M'.head d = w ∧ G.vb ztjuq ≠ 1 ∧ G.vb ztmiy ≠ 1

/-- **Reachability** in `G` from an encoded vertex is typed reachability. -/
theorem reach_iff (h : EnvEnc G M' eV eD) (u w : V') :
    G.Reach ztjuq ztmiy ↔ Relation.ReflTransGen ztqdb u w := by
  constructor
  · zuibu
    -- every vertex reached is encoded
    have key : ∀ x, G.Reach ztjuq x → ∃ w', x = eV w' ∧
        Relation.ReflTransGen ztqdb u w' := by
      zuh
      induction hx with
      | refl => exact ⟨u, rfl, Relation.ReflTransGen.refl⟩
      | tail _ hs ih =>
        obtain ⟨w', rfl, hw'⟩ := ih
        obtain ⟨e, he, hdb, hve, hhe, hu, hw⟩ := hs
        zubox
        zukrk
        subst hhe
        zukrn
        refine ⟨M'.head d, rfl, Relation.ReflTransGen.tail hw' ⟨d, hdb, h.eV_inj hve, rfl,
          by omega, hw⟩⟩
    obtain ⟨w', hw', hr'⟩ := key _ hr
    rw [h.eV_inj hw']; omega
  · zuibu
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact Relation.ReflTransGen.tail ih ((h.step_iff _ _).mpr hs)
