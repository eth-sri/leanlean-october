module

public import Chazelle.MacT
public import Chazelle.Core.OracleQueryExec
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.SpecNF
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.NFDecompBfs

namespace Chazelle.Core.L41
open Machine Chazelle Chazelle.Merge
@[expose] public section
def NodeOK (P : Polygon) (m : ℕ → ℕ) (A hp d f : ℕ) (C : Chain) (γ : ℕ) : Prop :=
  ChainDescAt m d zta ztqg C ∧ C.P = Qof P ∧ m d = hp ∧ d + 5 ≤ A ∧
    hp + 7 ≤ A ∧ C.s + C.m + 1 ≤ P.n ∧
    ∃ N, NFWithin m f A N ∧ IsCanonicalNF ztc zta N γ 4
variable {m m' : ℕ → ℕ} {P : Polygon}
theorem hostAt_agree {hp A : ℕ} {H : Host} (h : HostAt m hp H) (hl : H.length = 1)
    (hA : hp + 4 ≤ A) (he : ∀ a, a < A → m' a = m a) : HostAt m' hp H := by
  zueas
  refine ztexr
  zukco
  zufpy
  grind
theorem chainDescAt_agree {d hp A : ℕ} {Q : Polygon} {n : ℕ} {C : Chain}
    (h : ChainDescAt m d Q ztjja C) (hd : d + 5 ≤ A) (hh : m d = hp) (hA : hp + 7 ≤ A)
    (he : ∀ a, a < A → m' a = m a) : ChainDescAt m' d Q ztjja C := by
  zubhb
  refine ⟨?_, h1, by_grind, by_grind,
    by grind, by_grind⟩
  zuktz
  exact hostAt_agree h0 rfl by_omega he

/-- Nodes survive writes at or above `A`. -/
theorem NodeOK.agree {m m' : ℕ → ℕ} {A hp d f : ℕ} {C : Chain} {γ : ℕ}
    (h : NodeOK P m A hp d f C γ) (he : ∀ a, a < A → m' a = m a) : NodeOK P m' A hp d f C γ := by
  zuchw
  refine ⟨chainDescAt_agree h1 h4 h3 h5 he, h2, by_grind, h4, h5, h6,
    N, ?_, hc⟩
  intro m'' hm''
  exact hN m'' (fun a ha => (hm'' a ha).trans (he a ha))

/-- Nodes stay nodes for a larger bound. -/
theorem NodeOK.mono {m : ℕ → ℕ} {A A' hp d f : ℕ} {C : Chain} {γ : ℕ}
    (h : NodeOK P m A hp d f C γ) (hA : A ≤ A') : NodeOK P m A' hp d f C γ := by
  zuchw
  exact ⟨h1, h2, h3, by_omega, by_omega, h6, N, fun m' hm' => hN m' (fun a ha => hm' a by_omega),
    hc⟩

/-- **Junctions of consecutive chains of `Q` are generic.** -/
theorem sharedGeneric_q (hG : GoodEnv P) {J : Junction} (hJ : J.P = Qof P)
    (hn : J.s + J.m₁ + J.m₂ + 1 ≤ P.n) : SharedGeneric J := by
  zuyq
  zuc
  have h1 := J.one_le_m₁; have h2 := J.one_le_m₂
  have ev : ∀ k, J.s + k < P.n → J.whole.vertex k = (Qof P).vtx ztsyn := fun k hk => by
    zugil
    show J.P.vtx (ztsyn % J.P.n) = _
    rw [hJ, hQn, Nat.mod_eq_of_lt hk]
  unfold SharedGeneric sharedU sharedV sharedW
  rw [ev _ by_omega, ev _ by_omega, ev _ by_omega]
  refine ⟨hDH _ _ by_omega by_omega by_omega, hDH _ _ by_omega by_omega by_omega,
    hDH _ _ by_omega by_omega by_omega⟩

/-- A host description in memory is determined by the memory. -/
theorem hostAt_unique {m : ℕ → ℕ} {B : ℕ} {H H' : Host} (h : HostAt m B H) (h' : HostAt m B H') :
    H = H' := by
  obtain ⟨l, hi⟩ := h
  obtain ⟨l', hi'⟩ := h'
  apply List.ext_getElem by_omega
  grind

/-- **The precondition of a merge** from two consecutive nodes and the union's descriptor. -/
theorem mergePre_of {W : ℕ} {c : Config} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hX : X.holds P c.nmem ztdab ztm)
    (hcap : rd c bMerge 5 + fuseLoss ≤ X.cap P c.nmem ztdab)
    (h7 : rd c bMerge 7 = 4) (h56 : rd c bMerge 5 + fuseLoss ≤ rd c bMerge 6)
    {hp d1 f1 d2 f2 TD : ℕ} {C1 C2 : Chain} {γ1 γ2 : ℕ}
    (hn1 : NodeOK P c.nmem ztm hp d1 f1 C1 γ1)
    (hn2 : NodeOK P c.nmem ztm hp d2 f2 C2 γ2)
    (hγ1 : γ1 ≤ rd c bMerge 5) (hγ2 : γ2 ≤ rd c bMerge 5)
    (hcons : C2.s = C1.s + C1.m) (hlen : C1.m + C2.m + 1 ≤ C1.P.n)
    (r0 : rd c bMerge 0 = d1) (r1 : rd c bMerge 1 = d2) (r2 : rd c bMerge 2 = TD)
    (r3 : rd c bMerge 3 = f1) (r4 : rd c bMerge 4 = f2)
    (hTD : ChainDescAt c.nmem TD zta ztqg (jOf C1 C2 hlen).whole)
    (hTDm : c.nmem TD = hp) (hTDA : TD + 5 ≤ c.nreg ALLOC)
    (hOk : ∀ C : Chain, C.P = Qof P → Ok P ztc) : MergePre X Ok P W c := by
  zusi

  zuc
  zufvv
  zucm
  zuyq
  zuhoc
  zucgq

  have hwP : J.whole.P = Qof P := by_tauto
  have hpoly : ztyks := by
    have := poly_whole zta by_omega; simp_all
  have hHA : ztbabx := by have := d1a.1; simp_all
  -- well-formed descriptors
  have wf : ∀ d, d + 5 ≤ c.nreg ALLOC → c.nmem d = hp → c.nmem ztet < P.n →
      ChainWF P ztm c.nmem d := by
    intro d hd hdh hds
    refine ⟨hd, fun H C hC => ?_⟩
    have hH : ztpkf := hostAt_unique hC.1 by_simp_all
    zulsw
    refine ⟨by zvohn, hostWF_whole hn1, ?_, ?_⟩
    · zuoyp; tauto
    · rw [hC.2.1, hpoly, hQn, ← hC.2.2.1]; omega
  have s1 : c.nmem (d1 + 1) < P.n := by rw [d1a.2.2.1]; omega
  have s2 : c.nmem (d2 + 1) < P.n := by rw [d2a.2.2.1]; omega
  have sT : c.nmem ztjni < P.n := by rw [hTD.2.2.1, jOf_whole_s]; omega
  refine ⟨hG, hWh, hX, hcap, by zuofh, h56, ⟨?_, ?_, ?_, fun H hH => ?_⟩,
    Host.whole P.n, J, N1, N2, ztcg, by rw [show J.P = Qof P from hwP]; exact hQ,
    sharedGeneric_q hG hwP (by show C1.s + C1.m + C2.m + 1 ≤ P.n; omega),
    by simp_all, by_simp_all, hOk _ hwP,
    by zuofh; exact (fullDegSpec P hG.1 hG.2).1 _ hwP, by_simp_all,
    by simp_all, ztrfc,
    ⟨γ2, hγ2, by_simp_all⟩⟩
  · simp_all
  · simp_all
  · simp_all
  · rw [r2, hTDm] at hH
    rw [hostAt_unique hH hHA]; exact hostRegular_whole hn1
  · simp_all
  · simp_all
  simp_all
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs
@[expose] public section
def l0Body : Stmt := block [.storeN 160072 160071, .addN 160073 160071 160081,
  .loadN 160073 160073, .addN 160072 160072 160024, .storeN 160072 160073,
  .addN 160072 160072 160024, .addN 160071 160071 160082, .addN 9999 9999 160087,
  .addN 160070 160070 160024]

/-- **The level array of the leaves.** -/
def l0S : Stmt := .seq zthsj
  (.whileLtN 160070 160014 l0Body)

/-- The registers written by `l0S` (besides the allocator). -/
def L0RG (r : ℕ) : Prop := 160070 ≤ r ∧ r ≤ 160073
section proofs
variable {P : Polygon} {W : ℕ}

/-- The loop rule with a potential and a growth bound `ψ c' ≤ ψ c + k`. -/
theorem whileLtN_potential_lb' {a b : ℕ} {body : Stmt}
    (I : Config → Prop) (Φ ψ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c ∧ ψ c' ≤ ψ c + k)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ c + 2 ∧ ψ c' ≤ ψ c + k := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · zubu

    · exact ⟨c, 2, .whileLtN_false ht ztoai, hc, ht, by_omega, by_omega⟩
variable {c : Config}
set_option maxHeartbeats 8000000 in
theorem l0Body_exec (hw : WordsBounded W c) {i p q Al : ℕ}
    (h70 : c.nreg 160070 = i) (h71 : c.nreg 160071 = p) (h72 : c.nreg 160072 = q)
    (hA : c.nreg ALLOC = Al) (h24 : c.nreg 160024 = 1) (h81 : c.nreg 160081 = 5)
    (h82 : c.nreg 160082 = 6) (h87 : c.nreg 160087 = 8)
    (hW : q + 2 ≤ W) (hWp : p + 6 ≤ W) (hWA : Al + 8 ≤ W) (hWi : i + 1 ≤ W) (hpq : p + 5 < q) :
    ∃ c' k, Exec P W l0Body c c' k ∧ k = 9 ∧ WordsBounded W c' ∧
      c'.nreg 160070 = i + 1 ∧ c'.nreg 160071 = p + 6 ∧ c'.nreg 160072 = q + 2 ∧
      c'.nreg ALLOC = Al + 8 ∧ c'.nmem q = p ∧ c'.nmem ztfo = c.nmem ztkbt ∧
      (∀ a, a ≠ q → a ≠ q + 1 → c'.nmem a = c.nmem a) ∧
      ztdbf ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold l0Body
  exec_block
  all_goals try (config_simp; (try simp only [h70, h71, h72, hA, h24, h81, h82, h87]); omega)
  refine ztcra
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · config_simp; simp only [h71, h72, h24, h81, Machine.upd_apply]
    grind
  · simp_all
  · unfold L0RG at h1
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
set_option maxHeartbeats 8000000 in
/-- **The level array of the leaves.** -/
theorem l0S_exec (hw : WordsBounded W c) {R0 j : ℕ}
    (hA : c.nreg ALLOC = R0) (h15 : c.nreg 160015 = R0 + 6 * j) (h14 : c.nreg 160014 = j)
    (h24 : c.nreg 160024 = 1) (h81 : c.nreg 160081 = 5) (h82 : c.nreg 160082 = 6)
    (h87 : c.nreg 160087 = 8) (hW : R0 + 8 * j + 8 ≤ W) :
    ∃ c' k, Exec P W l0S c c' k ∧ k ≤ 11 * j + 5 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = R0 + 8 * j ∧ c'.nreg ALLOC ≤ R0 + k ∧
      (∀ k, k < j → c'.nmem (R0 + 6 * j + 2 * k) = R0 + 6 * k ∧
        c'.nmem (R0 + 6 * j + 2 * k + 1) = c.nmem ztnok) ∧
      (∀ a, (a < R0 + 6 * j ∨ R0 + 8 * j ≤ a) → c'.nmem a = c.nmem a) ∧
      ztdbf ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  set B0 := R0 + 6 * j with hB0
  obtain ⟨c1, k1, e1, hk1, hw1, h70, h71, h72, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      zthsj c c1 k1 ∧ k1 = 3 ∧
      WordsBounded W c1 ∧ c1.nreg 160070 = 0 ∧ c1.nreg 160071 = R0 ∧ c1.nreg 160072 = B0 ∧
      (∀ r, ¬ L0RG r → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧
      c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, by config_simp, by_simp_all, by_simp_all,
      fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    unfold L0RG at hr
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  have r1 : ∀ r, ¬ L0RG r → c1.nreg r = c.nreg r := fr1
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 160070 = i ∧
    c'.nreg ALLOC = R0 + 8 * i ∧ c'.nreg 160071 = R0 + 6 * i ∧ c'.nreg 160072 = B0 + 2 * i ∧
    (∀ k, k < i → c'.nmem (B0 + 2 * k) = R0 + 6 * k ∧
      c'.nmem (B0 + 2 * k + 1) = c.nmem ztnok) ∧
    (∀ a, (a < B0 ∨ B0 + 2 * i ≤ a) → c'.nmem a = c.nmem a) ∧
    ztdbf ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, e, ⟨i, ⟨hw', h70', hA', h71', h72', hent, hout, fr', hrr', hrm', ho'⟩, hij⟩,
      htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 160070) (b := 160014) (body := l0Body)
      (fun c' => ∃ i, I i c' ∧ i ≤ j) (fun c' => 11 * (j - c'.nreg 160070))
      ztcht (fun c' ⟨i, h, _⟩ => h.1)
      (fun c2 ⟨i, ⟨hw2, h70, hA2, h71, h72, hent, hout, fr2, hrr2, hrm2, ho2⟩, hij⟩ htest => by
        have g : ∀ r, ¬ L0RG r → r ≠ ALLOC → c2.nreg r = c.nreg r := fr2
        have c14 : c2.nreg 160014 = j := by
          rw [g _ ztbsj by_omega]; omega
        rw [h70, c14] at htest
        obtain ⟨c3, k3, e3, hk3, hw3, q70, q71, q72, qA, qm0, qm1, qm, fr3, hrr3, hrm3, ho3⟩ :=
          l0Body_exec (P := P) hw2 h70 h71 h72 hA2
            ztwsv
            ztwsv
            ztwsv
            ztwsv
            by_omega by_omega by_omega by_omega by_omega
        have hrec : c2.nmem ztnoj = c.nmem ztnoj :=
          hout _ ztec
        refine ⟨c3, k3, e3, ⟨i + 1, ⟨hw3, q70, by_omega, by_omega,
          by omega, fun k hk => ?_, fun a ha => ?_, fun r h1 h2 => ?_,
          by grind, by_grind, by_grind⟩, by_omega⟩, ?_, ?_⟩
        · rcases Nat.lt_or_ge k i with hki | hki
          · zunmh; grind
          grind
        · zuhnh
        · grind
        · omega
        grind)
      ⟨0, ⟨hw1, h70, by rw [r1 _ ztbsj, hA]; ring,
        by omega, by_omega, fun k hk => by_omega, fun a _ => by zvmxz,
        fun r h1 _ => r1 r h1, hrr1, hrm1, ho1⟩, Nat.zero_le _⟩
  have c14 : c'.nreg 160014 = j := by
    rw [fr' _ ztbsj by_omega]; omega
  have hij' : i = j := by_omega
  subst hij'
  have hk' : k ≤ 11 * i + 2 := by
    omega
  zufwy
  have hA1 : c1.nreg ALLOC = R0 := by rw [r1 _ ztbsj]; exact hA
  exact ⟨c', k1 + k, .seq e1 e, by_omega, hw', hA', by_omega, hent,
    fun a ha => hout a by_omega, fr', hrr', hrm', ho'⟩
end proofs
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs
@[expose] public section
def preB : Stmt := block [.loadN 160035 160065,
  .addN 160093 160065 160024, .loadN 160090 160093,
  .addN 160093 160093 160024, .loadN 160036 160093,
  .addN 160093 160093 160024, .loadN 160091 160093,
  .copyN 160037 9999, .addN 9999 9999 160081]

/-- The merge registers. -/
def setupB : Stmt := block [.copyN 100000 160035, .copyN 100001 160036, .copyN 100002 160037,
  .copyN 100003 160090, .copyN 100004 160091, .copyN 100005 160033, .copyN 100006 160034,
  .copyN 100007 160084, .copyN 100009 160000]

/-- The new cell `[TD, NF, prev]` and the advance. -/
def postB : Stmt := block [.copyN 160092 9999, .storeN 160092 160037,
  .addN 160093 160092 160024, .storeN 160093 100008,
  .addN 160093 160093 160024, .storeN 160093 160063,
  .copyN 160063 160092, .addN 9999 9999 160083,
  .addN 160065 160065 160084, .addN 160062 160062 160080, .addN 160064 160064 160024]
theorem rd_merge (c : Config) (i : ℕ) : rd c bMerge i = c.nreg (100000 + i) := rfl
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 8000000 in
theorem preB_exec (hw : WordsBounded W c) {ptr A : ℕ}
    (h65 : c.nreg 160065 = ptr) (h24 : c.nreg 160024 = 1) (h81 : c.nreg 160081 = 5)
    (hA : c.nreg ALLOC = A) (hW : ptr + 3 ≤ W) (hWA : A + 5 ≤ W) :
    ∃ c' k, Exec P W preB c c' k ∧ k = 9 ∧ WordsBounded W c' ∧
      c'.nreg 160035 = c.nmem ptr ∧ c'.nreg 160090 = c.nmem zthji ∧
      c'.nreg 160036 = c.nmem ztkco ∧ c'.nreg 160091 = c.nmem ztoeq ∧
      c'.nreg 160037 = A ∧ c'.nreg ALLOC = A + 5 ∧
      (∀ r, r ≠ 160035 → r ≠ 160036 → r ≠ 160037 → r ≠ 160090 → r ≠ 160091 → r ≠ 160093 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold preB
  exec_block
  all_goals try (config_simp; (try simp only [h65, h24, h81, hA]); omega)
  simp_all
set_option maxHeartbeats 8000000 in
theorem setupB_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W setupB c c' k ∧ k = 9 ∧ WordsBounded W c' ∧
      rd c' bMerge 0 = c.nreg 160035 ∧ rd c' bMerge 1 = c.nreg 160036 ∧
      rd c' bMerge 2 = c.nreg 160037 ∧ rd c' bMerge 3 = c.nreg 160090 ∧
      rd c' bMerge 4 = c.nreg 160091 ∧ rd c' bMerge 5 = c.nreg 160033 ∧
      rd c' bMerge 6 = c.nreg 160034 ∧ rd c' bMerge 7 = c.nreg 160084 ∧
      rd c' bMerge 9 = c.nreg 160000 ∧
      (∀ r, (r < 100000 ∨ 100009 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold setupB
  simp only [rd_merge, Nat.reduceAdd]
  exec_block
  refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp, by config_simp,
    by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  zubi
  repeat (rw [Machine.upd_other _ _ _ by_omega])
set_option maxHeartbeats 8000000 in
theorem postB_exec (hw : WordsBounded W c) {E TD f prev ptr i j : ℕ}
    (hA : c.nreg ALLOC = E) (h37 : c.nreg 160037 = TD) (h8 : c.nreg 100008 = f)
    (h63 : c.nreg 160063 = prev) (h65 : c.nreg 160065 = ptr) (h62 : c.nreg 160062 = i)
    (h64 : c.nreg 160064 = j)
    (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2) (h83 : c.nreg 160083 = 3)
    (h84 : c.nreg 160084 = 4) (hW : E + 3 ≤ W) (hWp : ptr + 4 ≤ W) (hWi : i + 2 ≤ W)
    (hWj : j + 1 ≤ W) :
    ∃ c' k, Exec P W postB c c' k ∧ k = 11 ∧ WordsBounded W c' ∧
      c'.nmem E = TD ∧ c'.nmem ztemk = f ∧ c'.nmem ztnkp = prev ∧
      ztfjd ∧
      c'.nreg ALLOC = E + 3 ∧ c'.nreg 160063 = E ∧ c'.nreg 160065 = ptr + 4 ∧
      c'.nreg 160062 = i + 2 ∧ c'.nreg 160064 = j + 1 ∧
      (∀ r, r ≠ 160092 → r ≠ 160093 → r ≠ 160063 → r ≠ 160065 → r ≠ 160062 → r ≠ 160064 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold postB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h65, h62, h64, h24, h80, h83, h84]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_,
    fun r a1 a2 a3 a4 a5 a6 a7 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [hA, h37, h24, Machine.upd_apply]; grind
  · simp_all
  · simp_all
  · config_simp; simp only [hA, h24, Machine.upd_apply]; grind
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  simp_all
end proofs
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs SweepPrim SignK WalkKey Chazelle.Merge
@[expose] public section
def pairS (sM : Stmt) : Stmt := .seq preB (.seq descS (.seq setupB (.seq sM postB)))

/-- The registers of band `bL41` written by a merge step. -/
def PairRG (r : ℕ) : Prop :=
  DescRG r ∨ r = 160035 ∨ r = 160036 ∨ r = 160037 ∨ r = 160090 ∨ r = 160091 ∨ r = 160092 ∨
    r = 160093 ∨ r = 160062 ∨ r = 160063 ∨ r = 160064 ∨ r = 160065

/-- The cost of one merge, in terms of the chord counts `x, y`, the granularity `γ` of the parts
and the length `M` of the union. -/
def mergeCostV (κ F G H : ℕ → ℕ) (x y γ M : ℕ) : ℕ :=
  κ 4 * ztcwy * F ztcbh * G ztcbh *
    ztxgb
theorem band_l41_notin : bL41 ∉ mergeBands ∪ oracleBands := by_decide
theorem band_merge_in : bMerge ∈ mergeBands ∪ oracleBands := by_decide
theorem band_sign_in : bSign ∈ mergeBands ∪ oracleBands := by_decide
variable {r : ℕ}
theorem bandOf_l41 (h1 : 160000 ≤ r) (h2 : r < 170000) : bandOf r = bL41 := by
  zulud
theorem bk_false_of (h : bandOf r ∉ mergeBands ∪ oracleBands) : Bk r = false := by
  unfold Bk
  zukr
  simp only [decide_eq_false_iff_not, not_not] at hc
  zucvk
  zuimr
theorem not_mergeReg_of (h : bandOf r ∉ mergeBands ∪ oracleBands) :
    r < 100000 ∨ 100009 < r := by
  zukr
  zugkq
  zuimr
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
/-- **One merge step on the RAM.** -/
theorem pairS_exec (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hWn : P.n + 3 ≤ W)
    {sM : Stmt} {κ F G H : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hMM : MergeMeets sM κ F G H X Ok) (hXc : X.CapLocal)
    (hOk : ∀ C : Chain, C.P = Qof P → Ok P ztc)
    {c : Config} (hw : WordsBounded W c)
    {A ptr prev i j hX γ₀ tgt hp d1 f1 d2 f2 γ1 γ2 : ℕ} {C1 C2 : Chain}
    (hA : c.nreg ALLOC = A) (h65 : c.nreg 160065 = ptr) (h63 : c.nreg 160063 = prev)
    (h62 : c.nreg 160062 = i) (h64 : c.nreg 160064 = j) (h33 : c.nreg 160033 = γ₀)
    (h34 : c.nreg 160034 = tgt) (h00 : c.nreg 160000 = hX)
    (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2) (h81 : c.nreg 160081 = 5)
    (h83 : c.nreg 160083 = 3) (h84 : c.nreg 160084 = 4)
    (m1 : c.nmem ptr = d1) (m2 : c.nmem zthji = f1) (m3 : c.nmem ztkco = d2)
    (m4 : c.nmem ztoeq = f2)
    (hn1 : NodeOK P c.nmem A hp d1 f1 C1 γ1) (hn2 : NodeOK P c.nmem A hp d2 f2 C2 γ2)
    (hγ1 : γ1 ≤ γ₀) (hγ2 : γ2 ≤ γ₀) (hcons : C2.s = C1.s + C1.m)
    (hXh : X.holds P c.nmem hX A) (hcap : γ₀ + fuseLoss ≤ X.cap P c.nmem hX)
    (htg : γ₀ + fuseLoss ≤ tgt)
    (hptr : ptr + 4 ≤ W) (hi : i + 2 ≤ W) (hj : j + 1 ≤ W)
    (hbud : A + 5 + mergeCostV κ F G H ztjrq ztjrr γ₀ ztdsx + 3 ≤ W) :
    ∃ c' k, Exec P W ztwbm c c' k ∧
      k ≤ mergeCostV κ F G H ztjrq ztjrr γ₀ ztdsx + 329 ∧
      WordsBounded W c' ∧ c'.nreg ALLOC ≤ A + k ∧
      ∃ E TD f C, A + 5 ≤ E ∧ E ≤ A + 5 + mergeCostV κ F G H ztjrq ztjrr γ₀
          ztdsx ∧
        c'.nreg ALLOC = E + 3 ∧ c'.nmem E = TD ∧ c'.nmem ztemk = f ∧ c'.nmem ztnkp = prev ∧
        C.s = C1.s ∧ C.m = C1.m + C2.m ∧ NodeOK P c'.nmem ztswu hp TD f C tgt ∧
        c'.nreg 160063 = E ∧ c'.nreg 160065 = ptr + 4 ∧ c'.nreg 160062 = i + 2 ∧
        c'.nreg 160064 = j + 1 ∧
        zttp ∧ ztbuk ∧
        c'.output = c.output ∧
        X.holds P c'.nmem hX ztswu ∧ X.cap P c'.nmem hX = X.cap P c.nmem hX ∧
        (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ PairRG r → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ PairRG r → c'.rreg r = c.rreg r) := by
  zuk
  zuc
  zusi

  have hlen : ztpiz := by_grind
  have hAW : A + 5 ≤ W := by_omega
  -- 1. the loads
  obtain ⟨c1, k1, e1, hk1, hw1, l35, l90, l36, l91, l37, lA, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    preB_exec (P := P) hw h65 h24 h81 hA by_omega hAW
  zvnmf at l35; rw [m2] at l90; rw [m3] at l36; rw [m4] at l91
  have c1r : ∀ r, 160000 ≤ r → r < 160035 → c1.nreg r = c.nreg r := by_grind
  -- 2. the descriptor of the union
  have hd1c : ChainDescAt c1.nmem d1 zta ztqg C1 := by_grind
  have hd2c : ChainDescAt c1.nmem d2 zta ztqg C2 := by_grind
  obtain ⟨c2, k2, e2, hk2, hw2, -, t0, t1, t2, t3, t4, hm2, fr2, frr2, hrm2, ho2⟩ :=
    descS_exec hG hWn hw1 l35 l36 l37 by_grind
      hd1c hd2c d1P d2P hcons by_omega by_omega by_omega hAW
  have c21 : ∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ PairRG r → c2.nreg r = c1.nreg r :=
    fun r h1 h2 => fr2 r ztzey ztvfa
  have c2r : ∀ r, 160000 ≤ r → r < 160035 → c2.nreg r = c.nreg r := fun r a b => by
    rw [fr2 r ztzc ztggj]; grind
  have c2A : c2.nreg ALLOC = A + 5 := by
    zuofi; exact lA
  have c2_37 : c2.nreg 160037 = A := by
    zubej
  have c2_35 : c2.nreg 160035 = d1 := by
    zubej
  have c2_36 : c2.nreg 160036 = d2 := by
    zubej
  have c2_90 : c2.nreg 160090 = f1 := by
    zubej
  have c2_91 : c2.nreg 160091 = f2 := by
    zubej
  have c2_84 : c2.nreg 160084 = 4 := by
    zuofj
    grind
  have mem2 : ztfai := fun a ha => by
    grind
  -- the descriptor of the union at `A`
  have hTD : ChainDescAt c2.nmem A zta ztqg (jOf C1 C2 hlen).whole := by
    have g1 := chainDescAt_agree d1a d1A d1h hpA mem2
    have g2 := chainDescAt_agree d2a d2A d2h hpA mem2
    refine descWhole hlen by_grind hcons g1 g2 ?_ t1 t2 t3 ?_
    · grind
    · rw [t4, hm1, mem2 _ by_omega, mem2 _ by_omega]
  have hTDm : c2.nmem A = hp := by_grind
  -- 3. the merge registers
  obtain ⟨c3, k3, e3, hk3, hw3, r0, r1, r2, r3, r4, r5, r6, r7, r9, fr3, hm3, hrr3, hrm3, ho3⟩ :=
    setupB_exec (P := P) hw2
  rw [c2_35] at r0; rw [c2_36] at r1; rw [c2_37] at r2; rw [c2_90] at r3; rw [c2_91] at r4
  rw [c2r _ by_omega by_omega, h33] at r5; rw [c2r _ by_omega by_omega, h34] at r6
  rw [c2_84] at r7; rw [c2r _ by_omega by_omega, h00] at r9
  have c3A : c3.nreg ALLOC = A + 5 := by rw [fr3 _ by_omega]; omega
  have mem3 : ztknu := fun a ha => by rw [hm3]; exact mem2 a ha
  have mem3' := fun a ha => (mem3 a ha).symm
  -- the context at `c3`
  have hX3 : X.holds P c3.nmem (rd c3 bMerge 9) ztqjl := by
    rw [r9, c3A]; exact X.mono _ _ _ _ _ by_omega (X.local_ _ _ _ _ _ mem3' hXh)
  have hcap3 := hXc _ _ _ _ _ mem3 hXh
  -- the nodes at `c3`
  have hn1' : NodeOK P c3.nmem ztqjl hp d1 f1 C1 γ1 := by
    rw [c3A]; exact (NodeOK.agree ⟨d1a, d1P, d1h, d1A, hpA, d1n, N1, hN1, hc1⟩ mem3).mono
      by_omega
  have hn2' : NodeOK P c3.nmem ztqjl hp d2 f2 C2 γ2 := by
    rw [c3A]; exact (NodeOK.agree ⟨d2a, d2P, d2h, d2A, by_omega, d2n, N2, hN2, hc2⟩ mem3).mono
      by_omega
  have hTD3 : ChainDescAt c3.nmem A zta ztqg (jOf C1 C2 hlen).whole := by
    grind
  have hpre :=
    mergePre_of hG hWh hX3 by_grind r7 by_omega
      hn1' hn2' by_omega by_omega hcons hlen r0 r1 r2 r3 r4 hTD3
      by_grind (by rw [c3A])
      hOk
  -- the chord counts
  have hf1 : c3.nmem f1 = c.nmem f1 := by
    rw [(hN1.transport mem3).holds.1, hN1.holds.1]
  have hf2 : c3.nmem f2 = c.nmem f2 := by
    rw [(hN2.transport mem3).holds.1, hN2.holds.1]
  have hcost : mergeCost κ F G H c3 =
      mergeCostV κ F G H ztjrq ztjrr γ₀ ztdsx := by
    unfold mergeCost mergeCostV
    rw [r7, r3, r4, r5, r2, hf1, hf2, hm3, t2]
  -- 4. the merge
  obtain ⟨c4, k4, e4, hk4, hpost, fr4⟩ := hMM P W c3 hw3 hpre by_grind
  replace hk4 : k4 ≤ mergeCost κ F G H c3 := hk4
  rw [hcost] at hk4
  obtain ⟨fr4r, fr4rr, fr4m, fr4rm, fr4o, fr4a, fr4b⟩ := fr4
  have hJ : JunctionAt c3.nmem (rd c3 bMerge 0) (rd c3 bMerge 1) (rd c3 bMerge 2) zta
      ztqg ztfsv := by
    zuime
    refine ⟨?_, ?_, hTD3⟩
    · rw [jOf_left]; exact hn1'.1
    · rw [jOf_right hlen by_grind hcons]; exact hn2'.1
  obtain ⟨N, -, hNW, hNc⟩ := hpost _ _ N1 N2 hJ (by rw [r3]; exact (hN1.transport mem3).holds)
    (by rw [r4]; exact (hN2.transport mem3).holds)
  rw [r6, r7] at hNc
  set E := c4.nreg ALLOC with hE
  have hE5 : A + 5 ≤ E := by_omega
  have hE6 : E ≤ A + 5 + mergeCostV κ F G H ztjrq ztjrr γ₀ ztdsx := by
    omega
  have c43 : ∀ r, bandOf r ∉ mergeBands ∪ oracleBands → r ≠ ALLOC → c4.nreg r = c3.nreg r :=
    by omega
  have c4c : ∀ r, 160000 ≤ r → r < 160035 → c4.nreg r = c.nreg r := fun r a b => by
    rw [c43 r (by rw [bandOf_l41 a by_omega]; decide) by_omega,
      fr3 r by_omega]; exact c2r r a b
  have c4_37 : c4.nreg 160037 = A := by
    rw [c43 _ by_decide
      by_omega, fr3 _ by_omega]; omega
  have c4_84 : c4.nreg 160084 = 4 := by
    rw [c43 _ by_decide
      by_omega, fr3 _ by_omega]; omega
  have c4k : ∀ r, 160065 ≤ r → r < 160090 → c4.nreg r = c.nreg r := fun r a b => by
    rw [c43 r ztlgw
      by_omega, fr3 r by_omega,
      fr2 r ztzc ztggj]
    exact fr1 r by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega
  have c4k' : ∀ r, 160057 ≤ r → r < 160065 → c4.nreg r = c.nreg r := fun r a b => by
    rw [c43 r ztlgw
      by_omega, fr3 r by_omega,
      fr2 r ztzc ztggj]
    exact fr1 r by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega
  -- 5. the cell and the advance
  obtain ⟨c5, k5, e5, hk5, hw5, w0, w1, w2, hm5, a5, q63, q65, q62, q64, fr5, hrr5, hrm5, ho5⟩ :=
    postB_exec (P := P) e4.wb_right hE.symm c4_37 rfl (by rw [c4k' _ by_omega by_omega, h63])
      (by rw [c4k _ by_omega by_omega, h65]) (by rw [c4k' _ by_omega by_omega, h62])
      (by rw [c4k' _ by_omega by_omega, h64]) (by rw [c4c _ by_omega by_omega, h24])
      (by rw [c4k _ by_omega by_omega, h80]) (by rw [c4k _ by_omega by_omega, h83])
      c4_84 by_omega hptr hi hj
  -- memory
  have mem54 := fun a ha => hm5 a ztbbu
  have mem53 : ∀ a, a < A + 5 → c5.nmem a = c3.nmem a := fun a ha => by
    rw [mem54 a by_omega, fr4m a (by rw [c3A]; exact ha)]
  have mem5 : ztknv := fun a ha => by
    rw [mem53 a by_omega]; exact mem3 a ha
  have mem5' := by_omega
  refine ⟨c5, k1 + ztvs, .seq e1 ztbxo,
    by omega, hw5, by rw [a5]; have := fr4b; rw [c3A] at this; omega, E, A, c4.nreg 100008, (jOf C1 C2 hlen).whole, hE5, hE6, a5, w0, w1, w2,
    rfl, rfl, ⟨?_, ?_, ?_, by_omega, by_omega, ?_, N, ?_, hNc⟩, q63, q65, q62, q64, mem5,
    fun a ha => ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, fun r h1 h2 => ?_⟩
  · exact chainDescAt_agree hTD3 by_omega (by rw [hm3]; try exact hTDm) by_omega mem53
  · rw [jOf_whole_P]; omega
  · rw [mem53 _ by_omega, hm3]; omega
  · show C1.s + ztdsx + 1 ≤ P.n; omega
  · exact (hNW.transport mem54).mono by_omega
  · rw [hrm5, fr4rm a by_grind, hrm3, hrm2, hrm1]
  · grind
  · refine X.mono _ _ _ _ _ by_grind (X.local_ _ _ _ _ _ ?_ hXh)
    intro a ha; exact (mem5 a ha).symm
  · exact hXc _ _ _ _ _ mem5 hXh
  · have e1' : ¬ (r = 160092 ∨ r = 160093 ∨ r = 160063 ∨ r = 160065 ∨ r = 160062 ∨
        r = 160064) := fun h => h2 (by unfold PairRG; omega)
    rw [fr5 r by_omega by_omega by_omega by_omega by_omega by_omega h3,
      c43 r h1 h3, fr3 r (not_mergeReg_of h1), c21 r h1 h2]
    exact fr1 r ztbqa ztbqa
      ztbqa ztbqa
      ztbqa by_grind h3
  · rw [hrr5, fr4rr r h1, hrr3, frr2 r ztvfa
      (by intro h; exact h2 (Or.inl (by unfold DescRG; omega))), hrr1]
end proofs
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs Chazelle.Merge Finset
@[expose] public section
abbrev Shp := ℕ × ℕ × ℕ

/-- The node `k` of a level (in shape). -/
def nd (ns : List Shp) (k : ℕ) : Shp := ns.getD k ztt

/-- The chord bound of a node from Lemma 2.3. -/
def kb (x : Shp) : ℕ := 60 * ztelb / x.2.2

/-- **A level in memory**: entry `k` of the array at `B` is a node of shape `nd ns k`. -/
def LevelAt (P : Polygon) (m : ℕ → ℕ) (A B hp : ℕ) (ns : List Shp) : Prop :=
  ∀ k, k < ns.length → ∃ C : Chain, C.s = (nd ns k).1 ∧ C.m = (nd ns k).2.1 ∧
    NodeOK P m A hp (m ztgda) (m ztelt) C (nd ns k).2.2

/-- Consecutive shapes. -/
def Consec (ns : List Shp) : Prop :=
  ∀ k, k + 1 < ns.length → (nd ns zts).1 = (nd ns k).1 + (nd ns k).2.1

/-- The chord family of a normal form has one chord per record. -/
theorem nf_chords_ncard {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF ztc Q N) :
    (N.F ztc Q).ncard = N.chords.length := by
  zufru

  have hFn : N.F ztc Q = ztxbm ''
      Set.Iio N.chords.length := by
    zuitz
    · zuoc
      zuep
      zuifc
      show (N.chord i).toSet _ _ = _
      zuub
    · zuin
      refine ztfju
      zuub
  rw [hFn, Set.InjOn.ncard_image (s := Set.Iio N.chords.length) ztdul,
    ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

/-- **Lemma 2.3 for a node**: `K γ ≤ 60 (2 m + 7)`. -/
theorem NodeOK.chords_le {P : Polygon} {m : ℕ → ℕ} {A hp d f : ℕ} {C : Chain} {γ : ℕ}
    (hG : GoodEnv P) (h : NodeOK P m A hp d f C γ) : m f * γ ≤ 60 * ztz := by
  obtain ⟨-, hCP, -, -, -, -, N, hN, hc⟩ := h
  zurr
  have hGM : ztebh := Or.inl ⟨C, by_simp_all, rfl⟩
  zubm
  have hF := hc.1.1
  have := hM.lemma23_walk hF.2.1 hF.1 hc.2.1 hc.2.2.1
  zuiyn
  rw [nf_chords_ncard hc.1, hn] at this
  rw [hN.holds.1]; omega
theorem NodeOK.chords_kb {P : Polygon} {m : ℕ → ℕ} {A hp d f : ℕ} {C : Chain} {x : Shp}
    (hG : GoodEnv P) (h : NodeOK P m A hp d f C x.2.2) (hm : C.m = x.2.1) (hγ : 1 ≤ x.2.2) :
    m f ≤ kb x := by
  have := h.chords_le hG
  zvmwi at this
  unfold kb
  exact (Nat.le_div_iff_mul_le hγ).mpr this
theorem mergeCostV_mono (κ F G H : ℕ → ℕ) {x x' y y' : ℕ} (γ M : ℕ) (hx : x ≤ x') (hy : y ≤ y') :
    mergeCostV κ F G H x y γ M ≤ mergeCostV κ F G H x' y' γ M := by
  unfold mergeCostV
  gcongr
section proofs
variable {P : Polygon} {W : ℕ}

/-- **A loop over pairs** (`ri` counts by `2`, up to `N`) with per-iteration costs `b p`. -/
theorem forStep2 {ri rn : ℕ} {body : Stmt} (I : ℕ → Config → Prop) (N : ℕ) (b : ℕ → ℕ)
    (hI : ∀ p c, I p c → WordsBounded W c ∧ c.nreg ri = 2 * p ∧ c.nreg rn = N)
    (hbody : ∀ p c, 2 * p < N → I p c → ∃ c' k, Exec P W body c c' k ∧ k ≤ b p ∧ I ztr c' ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k)
    {c : Config} (hc : I 0 c) :
    ∃ c' k, Exec P W zthqm c c' k ∧
      k ≤ (∑ q ∈ range ztytf, ztrks) + 2 ∧ I ztytf c' ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨c', k, e, ⟨p', hIp, hp'⟩, htest, hk, hψ⟩ := whileLtN_potential_lb' (P := P) (W := W)
    (a := ri) (b := rn) (body := body) (fun c => ∃ p, I p c ∧ p ≤ zttg / 2)
    (fun c => ∑ q ∈ Ico (c.nreg ri / 2) ztytf, ztrks) ztesf
    (fun c ⟨p, h, _⟩ => (hI p c h).1)
    (fun c ⟨p, h, hpn⟩ htest => by
      obtain ⟨-, hri, hrn⟩ := hI p c h
      rw [hri, hrn] at htest
      obtain ⟨c', k, e, hk, h', hA'⟩ := hbody p c htest h
      obtain ⟨-, hri', -⟩ := hI ztr c' h'
      refine ⟨c', k, e, by_grind, ?_, hA'⟩
      rw [hri, hri', show 2 * ztr / 2 = p + 1 by omega, show 2 * p / 2 = p by omega,
        Finset.sum_eq_sum_Ico_succ_bot (show p < zttg / 2 by omega)]
      omega) ⟨0, hc, Nat.zero_le _⟩
  obtain ⟨-, hri, hrn⟩ := hI p' c' hIp
  have hpn : p' = zttg / 2 := by_omega
  subst hpn
  refine ⟨c', k, e, ?_, hIp, hψ⟩
  obtain ⟨-, hri0, -⟩ := hI 0 c hc
  simp_all
end proofs

/-- The per-pair cost bound of a level. -/
def pairCost (κ F G H : ℕ → ℕ) (ns : List Shp) (γ₀ q : ℕ) : ℕ :=
  mergeCostV κ F G H (kb (nd ns ztbtl)) (kb (nd ns ztbhl)) γ₀
    ((nd ns ztbtl).2.1 + (nd ns ztbhl).2.1)

/-- The pair loop. -/
def pairL (sM : Stmt) : Stmt := .whileLtN 160062 160067 ztwbm

/-- **The state of the pair loop** after `p` merges. -/
def PairSt (P : Polygon) (W : ℕ) (X : MemCtx) (c0 : Config) (A0 B hp hX tgt : ℕ) (ns : List Shp)
    (pcs : ℕ → ℕ) (p : ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 160062 = 2 * p ∧ c.nreg 160065 = B + 4 * p ∧ c.nreg 160064 = p ∧
    A0 ≤ c.nreg ALLOC ∧ c.nreg ALLOC ≤ A0 + ∑ q ∈ range p, ztlrr ∧
    (∀ a, a < A0 → c.nmem a = c0.nmem a) ∧ (∀ a, a < A0 → c.rmem a = c0.rmem a) ∧
    c.output = c0.output ∧
    (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ PairRG r → r ≠ ALLOC → c.nreg r = c0.nreg r) ∧
    (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ PairRG r → c.rreg r = c0.rreg r) ∧
    X.holds P c.nmem hX ztm ∧ X.cap P c.nmem hX = X.cap P c0.nmem hX ∧
    ∃ e : ℕ → ℕ, (∀ q, q < p → A0 ≤ e q ∧ e q + 3 ≤ c.nreg ALLOC ∧
      (1 ≤ q → c.nmem ztlne = e ztcfe) ∧
      ∃ C : Chain, C.s = (nd ns ztbtl).1 ∧
        C.m = (nd ns ztbtl).2.1 + (nd ns ztbhl).2.1 ∧
        NodeOK P c.nmem ztm hp (c.nmem ztvpk) (c.nmem ztrow) C tgt) ∧
      (1 ≤ p → c.nreg 160063 = e ztoq)
section proofs
variable {P : Polygon} {W : ℕ}
variable {r : ℕ}
theorem not_pairRG (h : r < 160035 ∨ ztneo ∨ (160065 < r ∧ r < 160090)
    ∨ 160093 < r) : ¬ PairRG r := by
  unfold PairRG DescRG; omega
theorem bandOK_l41 (h1 : 160000 ≤ r) (h2 : r < 170000) :
    bandOf r ∉ mergeBands ∪ oracleBands := by
  rw [bandOf_l41 h1 h2]; decide
set_option maxHeartbeats 16000000 in
/-- **The pair loop of a level.** -/
theorem pairL_exec (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hWn : P.n + 3 ≤ W)
    {sM : Stmt} {κ F G H : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hMM : MergeMeets sM κ F G H X Ok) (hXc : X.CapLocal)
    (hOk : ∀ C : Chain, C.P = Qof P → Ok P ztc)
    {c0 : Config} (hw : WordsBounded W c0) {A0 B hp hX γ₀ tgt : ℕ} {ns : List Shp}
    (hj : 1 ≤ ns.length)
    (hA : c0.nreg ALLOC = A0) (h62 : c0.nreg 160062 = 0) (h65 : c0.nreg 160065 = B)
    (h64 : c0.nreg 160064 = 0) (h67 : c0.nreg 160067 = ns.length - 1)
    (h33 : c0.nreg 160033 = γ₀) (h34 : c0.nreg 160034 = tgt) (h00 : c0.nreg 160000 = hX)
    (h24 : c0.nreg 160024 = 1) (h80 : c0.nreg 160080 = 2) (h81 : c0.nreg 160081 = 5)
    (h83 : c0.nreg 160083 = 3) (h84 : c0.nreg 160084 = 4)
    (hL : LevelAt P c0.nmem A0 B hp ns) (hc : Consec ns) (hB : B + 2 * ns.length ≤ A0)
    (hγ : ∀ k, k < ns.length → (nd ns k).2.2 ≤ γ₀)
    (hγ1 : ∀ k, k < ns.length → 1 ≤ (nd ns k).2.2)
    (hXh : X.holds P c0.nmem hX A0) (hcap : γ₀ + fuseLoss ≤ X.cap P c0.nmem hX)
    (htg : γ₀ + fuseLoss ≤ tgt)
    (hbud : A0 + ∑ q ∈ range ztcwb, ztcfb ≤ W) :
    ∃ c' k, Exec P W ztwbk c0 c' k ∧
      k ≤ ztytj + 2 ∧
      c'.nreg ALLOC ≤ A0 + k ∧ PairSt P W X c0 A0 B hp hX tgt ns (pairCost κ F G H ns γ₀) ztcwb c' := by
  zuk
  zukzo
  set pcs := pairCost κ F G H ns γ₀ with hpcs
  have hnp : ztjzb / 2 = j / 2 := by_omega
  have hsum_mono : ∀ p, p ≤ j / 2 → ∑ q ∈ range p, ztlrr ≤
      ∑ q ∈ range _, ztlrr := fun p hp =>
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hp)
  obtain ⟨c', k, e, hk, hI, hψ⟩ := forStep2 (P := P) (W := W) (ri := 160062) (rn := 160067)
    (body := pairS sM) (PairSt P W X c0 A0 B hp hX tgt ns pcs) zthv (fun q => pcs q + 329)
    (fun p c h => ⟨h.1, h.2.1, by
      rw [h.2.2.2.2.2.2.2.2.2.1 _ ztdtu ztddf
        by_omega]; omega⟩)
    (fun p c hp h => by
      obtain ⟨hwc, c62, c65, c64, cA0, cA1, cm, crm, co, cr, crr, cX, ccap, ee, hee, hprev⟩ := h
      have cr' : ∀ r, 160000 ≤ r → r < 160035 → c.nreg r = c0.nreg r := fun r a b =>
        cr r (bandOK_l41 a by_omega) ztddf by_omega
      have cr'' : ∀ r, 160065 < r → r < 160090 → c.nreg r = c0.nreg r := fun r a b =>
        cr r ztdtu ztddf by_omega
      zujmj
      have hp1 : 2 * p + 1 < j := by_omega
      obtain ⟨C1, s1, m1', n1⟩ := hL ztdsl by_omega
      obtain ⟨C2, s2, m2', n2⟩ := hL ztgci hp1
      have cmA := cm
      have n1c := (n1.agree cmA).mono cA0
      have n2c := (n2.agree cmA).mono cA0
      have hcons : ztsba := by rw [s1, s2, m1', hc _ hp1]
      have kb1 : ztsen :=
        n1c.chords_kb hG m1' by_grind
      have kb2 : ztsen :=
        n2c.chords_kb hG m2' by_grind
      have hmc : mergeCostV κ F G H (c.nmem (c0.nmem ztyom))
          (c.nmem (c0.nmem ztyon)) γ₀ ztdsx ≤ pcs p := by
        have := mergeCostV_mono κ F G H γ₀ ztdsx kb1 kb2
        rw [m1', m2'] at this ⊢; tauto
      have hbp : A + 5 + pcs p + 3 ≤ W := by
        have := hsum_mono ztr by_omega
        rw [Finset.sum_range_succ] at this
        omega
      obtain ⟨c'', k'', e'', hk'', hw'', hAk'', E, TD, f, C, hE1, hE2, hA'', w0, w1, w2, hCs, hCm,
          hN,
          q63, q65, q62, q64, mem'', rmem'', out'', hX'', cap'', fr'', frr''⟩ :=
        pairS_exec hG hWh hWn hMM hXc hOk hwc (A := A) (ptr := B + 4 * p)
          (d1 := c0.nmem (B + 2 * ztdsl)) (f1 := c0.nmem ztyom)
          (d2 := c0.nmem (B + 2 * ztgci)) (f2 := c0.nmem ztyon)
          (prev := c.nreg 160063) (i := 2 * p) (j := p) (hX := hX) (γ₀ := γ₀) (tgt := tgt)
          rfl c65 rfl c62 c64 ztdce
          ztdce
          ztdce
          ztdce
          ztdcf
          ztdcf
          ztdcf
          ztdcf
          ztdls
          ztdls
          ztdls
          ztdls
          n1c n2c by_grind (hγ _ hp1) hcons cX
          by_omega htg by_omega by_omega by_omega by_omega
      refine ⟨c'', k'', e'', by_omega, ?_, hAk''⟩
      refine ⟨hw'', by_omega, by_omega, q64, by_omega, ?_,
        fun a ha => by rw [mem'' a by_omega]; exact cm a ha,
        fun a ha => by rw [rmem'' a by_omega]; exact crm a ha, by_grind,
        fun r h1 h2 h3 => by rw [fr'' r h1 h2 h3]; exact cr r h1 h2 h3,
        fun r h1 h2 => by rw [frr'' r h1 h2]; exact crr r h1 h2,
        by grind, by_omega,
        fun q => if q = p then E else ee q, fun q hq => ?_, by_grind⟩
      · rw [hA'', Finset.sum_range_succ]; omega
      · rcases Nat.lt_or_ge q p with hqp | hqp
        · obtain ⟨a1, a2, a3, C', b1, b2, b3⟩ := hee q hqp
          simp only [show q ≠ p by omega, ite_false]
          refine ⟨a1, by_omega, fun hq1 => ?_, C', b1, b2, ?_⟩
          · simp only [show q - 1 ≠ p by omega, ite_false]
            rw [mem'' _ by_omega]; omega
          · rw [mem'' _ by_omega, mem'' _ by_omega, hA'']
            exact (b3.agree mem'').mono by_omega
        · have hqe : q = p := by_omega
          subst hqe
          zuwa
          refine ⟨by_omega, by_omega, fun hq1 => ?_, C, ?_, ?_, ?_⟩
          · simp only [show q - 1 ≠ q by omega, ite_false]
            omega
          · omega
          · omega
          grind)
    (⟨hw, by rw [h62], by_omega, h64, by_omega, by_omega,
      fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
      by grind, rfl, fun _ => 0, fun q hq => by_omega, fun h => by_omega⟩)
  rw [hnp] at hk hI
  refine ⟨c', k, e, ?_, by_omega, hI⟩
  omega
end proofs
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs Chazelle.Merge Finset
@[expose] public section
def pairUp : List Shp → ℕ → List Shp
  | a :: b :: rest, t => ztnqw :: pairUp rest t
  | l, _ => l
theorem pairUp_length : ∀ (l : List Shp) (t : ℕ), (pairUp l t).length = (l.length + 1) / 2
  | [], _ => by_rfl
  | [_], _ => by zuoyq
  | a :: b :: rest, t => by
    simp only [pairUp, List.length_cons, pairUp_length rest t]; omega
variable (a : Shp) (l : List Shp)
theorem nd_cons_succ (k : ℕ) : nd (a :: l) zts = nd l k := by
  rfl
theorem nd_cons_zero : nd (a :: l) 0 = a := by_rfl
theorem nd_pairUp_merge : ∀ (l : List Shp) (t q : ℕ), q < l.length / 2 →
    nd zteum q = ((nd l ztbtl).1, (nd l ztbtl).2.1 + (nd l ztbhl).2.1, t)
  | [], _, q, h => by_simp_all
  | [_], _, q, h => by_simp_all
  | a :: b :: rest, t, 0, _ => by
    rfl
  | a :: b :: rest, t, q + 1, h => by
    have ih := nd_pairUp_merge rest t q by_grind
    tauto
theorem nd_pairUp_carry : ∀ (l : List Shp) (t : ℕ), l.length % 2 = 1 →
    nd zteum ztjzw = nd l ztetw
  | [], _, h => by_rfl
  | [_], _, _ => by zuoyq
  | a :: b :: rest, t, h => by
    simp only [List.length_cons] at h ⊢
    have ih := nd_pairUp_carry rest t by_omega
    have h1 : 1 ≤ rest.length := by_omega
    simp only [pairUp]
    rw [show (rest.length + 1 + 1) / 2 = rest.length / 2 + 1 by omega, nd_cons_succ,
      show rest.length + 1 + 1 - 1 = rest.length - 1 + 1 + 1 by omega, nd_cons_succ,
      nd_cons_succ]
    exact ih
theorem nd_pairUp_zero (t : ℕ) (h : 1 ≤ l.length) :
    (nd zteum 0).1 = (nd l 0).1 := by
  rcases Nat.lt_or_ge 1 l.length with h2 | h2
  · rw [nd_pairUp_merge l t 0 by_omega]
  · have : l.length = 1 := by_omega
    have := nd_pairUp_carry l t by_omega
    simp_all

/-- **The next level is consecutive.** -/
theorem consec_pairUp {l : List Shp} (t : ℕ) (h : Consec l) : Consec zteum := by
  zuco
  rw [pairUp_length] at hq
  have hq0 : q < l.length / 2 := by_omega
  rw [nd_pairUp_merge l t q hq0]
  have e1 : (nd zteum ztfo).1 = (nd l (2 * q + 2)).1 := by
    rcases Nat.lt_or_ge ztfo ztjzw with h1 | h1
    · rw [nd_pairUp_merge l t _ h1]; rfl
    · zufwa
      have := nd_pairUp_carry l t hodd
      grind
  rw [e1, h _ by_omega, h _ by_omega]
  grind
theorem pairUp_sum : ∀ (l : List Shp) (t : ℕ),
    ((pairUp l t).map fun x => x.2.1).sum = (l.map fun x => x.2.1).sum
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, t => by
    simp only [pairUp, List.map_cons, List.sum_cons, pairUp_sum rest t]; ring

/-- The granularities of the next level are at most the target. -/
theorem pairUp_gran {l : List Shp} {t γ₀ : ℕ} (hγ : ∀ k, k < l.length → (nd l k).2.2 ≤ γ₀)
    (ht : γ₀ ≤ t) : ∀ k, k < (pairUp l t).length → (nd zteum k).2.2 ≤ t := by
  zugf
  zuemn

  · zunzc
  · zufwa
    have := nd_pairUp_carry l t hodd
    grind
theorem pairUp_gran_pos {l : List Shp} {t : ℕ} (hγ : ∀ k, k < l.length → 1 ≤ (nd l k).2.2)
    (ht : 1 ≤ t) : ∀ k, k < (pairUp l t).length → 1 ≤ (nd zteum k).2.2 := by
  zugf
  zuemn

  · zunzc; exact ht
  · zufwa
    have := nd_pairUp_carry l t hodd
    grind

/-- **The nodes of the next level as back-linked cells** `[descriptor, NF, prev]`. -/
def CellSt (P : Polygon) (m : ℕ → ℕ) (A hp : ℕ) (ns : List Shp) (e : ℕ → ℕ) : Prop :=
  ∀ q, q < ns.length → e q + 3 ≤ A ∧ (1 ≤ q → m ztlne = e ztcfe) ∧
    ∃ C : Chain, C.s = (nd ns q).1 ∧ C.m = (nd ns q).2.1 ∧
      NodeOK P m A hp (m ztvpk) (m ztrow) C (nd ns q).2.2

/-- The cell of a carried node. -/
def carryB : Stmt := block [.loadN 160035 160065, .addN 160093 160065 160024,
  .loadN 160090 160093, .copyN 160092 9999, .storeN 160092 160035, .addN 160093 160092 160024,
  .storeN 160093 160090, .addN 160093 160093 160024, .storeN 160093 160063, .copyN 160063 160092,
  .addN 9999 9999 160083, .addN 160064 160064 160024]

/-- **The carry** of an odd last node. -/
def carryS : Stmt := .ifLtN 160062 160014 carryB .skip
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 8000000 in
theorem carryB_exec {c : Config} (hw : WordsBounded W c) {E ptr prev j : ℕ}
    (hA : c.nreg ALLOC = E) (h65 : c.nreg 160065 = ptr) (h63 : c.nreg 160063 = prev)
    (h64 : c.nreg 160064 = j) (h24 : c.nreg 160024 = 1) (h83 : c.nreg 160083 = 3)
    (hW : E + 3 ≤ W) (hWp : ptr + 1 ≤ W) (hWj : j + 1 ≤ W) :
    ∃ c' k, Exec P W carryB c c' k ∧ k = 12 ∧ WordsBounded W c' ∧
      c'.nmem E = c.nmem ptr ∧ c'.nmem ztemk = c.nmem zthji ∧ c'.nmem ztnkp = prev ∧
      ztfjd ∧
      c'.nreg ALLOC = E + 3 ∧ c'.nreg 160063 = E ∧ c'.nreg 160064 = j + 1 ∧
      (∀ r, r ≠ 160035 → r ≠ 160090 → r ≠ 160092 → r ≠ 160093 → r ≠ 160063 → r ≠ 160064 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold carryB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h65, h64, h24, h83]); omega)
  refine ⟨rfl, by_omega, ?_, ?_, ?_, fun a ha => ?_, ?_, ?_, ?_,
    fun r a1 a2 a3 a4 a5 a6 a7 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [hA, h65, h24, Machine.upd_apply]; grind
  · simp_all
  · simp_all
  · config_simp; simp only [hA, h24, Machine.upd_apply]; grind
  · simp_all
  · simp_all
  · simp_all
  simp_all
set_option maxHeartbeats 16000000 in
/-- **The carry.** -/
theorem carryS_exec {X : MemCtx} {c0 c : Config} {A0 B hp hX tgt : ℕ} {ns : List Shp}
    {pcs : ℕ → ℕ} (hj : 1 ≤ ns.length)
    (hst : PairSt P W X c0 A0 B hp hX tgt ns pcs ztcwb c)
    (h14 : c0.nreg 160014 = ns.length) (h24 : c0.nreg 160024 = 1) (h83 : c0.nreg 160083 = 3)
    (hL : LevelAt P c0.nmem A0 B hp ns) (hB : B + 2 * ns.length ≤ A0)
    (hW : c.nreg ALLOC + 3 ≤ W) :
    ∃ c' k, Exec P W carryS c c' k ∧ k ≤ 14 ∧ WordsBounded W c' ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + 3 ∧
      zth ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.rreg = c.rreg ∧
      (∀ r, ¬ PairRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nreg 160064 = (pairUp ns tgt).length ∧
      ∃ e : ℕ → ℕ, CellSt P c'.nmem ztdo hp ztkce e ∧
        c'.nreg 160063 = e ((pairUp ns tgt).length - 1) ∧
        (∀ q, q < (pairUp ns tgt).length → A0 ≤ e q) := by
  zuk
  obtain ⟨hwc, c62, c65, c64, cA0, -, cm, -, -, cr, -, -, -, ee, hee, hprev⟩ := hst
  zukzo
  set np := j / 2 with hnp
  have hlen' : (pairUp ns tgt).length = ztl / 2 := pairUp_length ns tgt
  have c14 : c.nreg 160014 = j := by
    zudju

  have c24 : ztplx := by
    zudju

  have c83 : ztunp := by
    zudju

  -- the merged nodes as cells
  have merged : ∀ (m : ℕ → ℕ) (A : ℕ), c.nreg ALLOC ≤ A →
      (∀ a, a < c.nreg ALLOC → m a = c.nmem a) → ∀ q, q < np →
      ee q + 3 ≤ A ∧ (1 ≤ q → m (ee q + 2) = ee ztcfe) ∧
      ∃ C : Chain, C.s = (nd ztkce q).1 ∧ C.m = (nd ztkce q).2.1 ∧
        NodeOK P m A hp (m (ee q)) (m (ee q + 1)) C (nd ztkce q).2.2 := by
    intro m A hA he q hq
    obtain ⟨a1, a2, a3, C, b1, b2, b3⟩ := hee q hq
    rw [nd_pairUp_merge ns tgt q hq]
    refine ⟨by_omega, fun h => by_grind, C, b1, b2, ?_⟩
    zundt
    exact (b3.agree he).mono hA
  by_cases hodd : 2 * np < j
  · -- the carry
    have hj1 : j - 1 = 2 * np := by_omega
    obtain ⟨C, s1, m1, n1⟩ := hL zthv by_omega
    obtain ⟨c', k, e, hk, hw', w0, w1, w2, hm', hA', q63, q64, fr', hrr', hrm', ho'⟩ :=
      carryB_exec hwc rfl c65 rfl c64 c24 c83 hW by_omega by_omega
    have hptr : B + 4 * np = B + 2 * zthv := by_omega
    refine ⟨c', k + 1, .ifLtN_true by_omega e, by_omega, hw',
      by omega, by_omega, by_omega, fun a ha => hm' a ztbbu, hrm', ho', hrr',
      fun r h1 h2 => fr' r ztcmm ztcmm
        ztcmm ztcmm
        ztcmm ztcmm h2,
      by omega, fun q => if q = np then c.nreg ALLOC else ee q,
      fun q hq => ?_, ?_, fun q hq => ?_⟩
    · zuemb

      · zunmi
        obtain ⟨a1, a2, C', b1, b2, b3⟩ := merged c'.nmem ztdo by_omega
          (fun a ha => hm' a ztbbu) q hq1
        exact ⟨a1, fun h => by rw [a2 h]; simp [show q - 1 ≠ np by omega], C', b1, b2, b3⟩
      · have hq2 : q = np := by_omega
        subst hq2
        zuwa
        have hcarry := nd_pairUp_carry ns tgt by_omega
        rw [← hnp] at hcarry
        refine ⟨by_omega, fun h => ?_, C, ?_, ?_, ?_⟩
        · simp only [show np - 1 ≠ np by omega, ite_false]
          grind
        · grind
        · grind
        · rw [hcarry, w0, w1, hA', hptr, cm _ by_omega, cm _ by_omega]
          have n1c := (n1.agree cm).mono cA0
          exact (n1c.agree fun a ha => hm' a ztbbu).mono by_omega
    · rw [q63, hlen']; simp [show ztl / 2 - 1 = np by omega]
    · zuemb

      · zunmi; exact (hee q hq1).1
      · simp only [show q = np by omega, ite_true]; omega
  · -- nothing to carry
    have heven : 2 * np = j := by_omega
    refine ⟨c, 2, .ifLtN_false by_omega (.skip hwc), by_omega, hwc,
      le_rfl, by_omega, by_omega, by_omega, rfl, rfl, rfl, by_omega,
      by omega, ee, fun q hq => ?_, ?_, fun q hq => ?_⟩
    · rw [hlen'] at hq
      exact merged c.nmem _ le_rfl by_omega q by_omega
    · rw [hprev by_omega, hlen']; congr 1; omega
    grind
end proofs
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs Chazelle.Merge Finset
@[expose] public section
def rbInit : Stmt := block [.copyN 160094 9999, .addN 160095 9999 160064,
  .addN 160095 160095 160064, .copyN 160096 160063, .constN 160097 0]

/-- One entry, from the end. -/
def rbBody : Stmt := block [.subN 160095 160095 160080, .loadN 160098 160096,
  .storeN 160095 160098, .addN 160099 160096 160024, .loadN 160098 160099,
  .addN 160099 160095 160024, .storeN 160099 160098, .addN 160099 160096 160080,
  .loadN 160096 160099, .addN 160097 160097 160024, .addN 9999 9999 160080]

/-- **The rebuild of the level array.** -/
def rbS : Stmt := .seq rbInit (.whileLtN 160097 160064 rbBody)

/-- The registers written by `rbS` (besides the allocator). -/
def RbRG (r : ℕ) : Prop := 160094 ≤ r ∧ r ≤ 160099

/-- The registers written by `rbBody` (besides the allocator). -/
def RbBRG (r : ℕ) : Prop := 160095 ≤ r ∧ r ≤ 160099
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 8000000 in
theorem rbBody_exec (hw : WordsBounded W c) {p0 e0 t Al : ℕ}
    (h95 : c.nreg 160095 = p0) (h96 : c.nreg 160096 = e0) (h97 : c.nreg 160097 = t)
    (hA : c.nreg ALLOC = Al) (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2)
    (hp : 2 ≤ p0) (he : e0 + 3 ≤ p0 - 2) (hWp : p0 ≤ W) (hWt : t + 1 ≤ W) (hWA : Al + 2 ≤ W) :
    ∃ c' k, Exec P W rbBody c c' k ∧ k = 11 ∧ WordsBounded W c' ∧
      c'.nreg 160095 = p0 - 2 ∧ c'.nreg 160096 = c.nmem (e0 + 2) ∧ c'.nreg 160097 = t + 1 ∧
      c'.nreg ALLOC = Al + 2 ∧ c'.nmem (p0 - 2) = c.nmem e0 ∧
      c'.nmem (p0 - 2 + 1) = c.nmem (e0 + 1) ∧
      (∀ a, a ≠ p0 - 2 → a ≠ p0 - 2 + 1 → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RbBRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold rbBody
  exec_block
  all_goals try (config_simp; (try simp only [h95, h96, h97, hA, h24, h80]); omega)
  refine ztcra
  · config_simp; omega
  · config_simp; simp only [h95, h96, h80, h24, Machine.upd_apply]; grind
  · config_simp; omega
  · config_simp; omega
  · config_simp; simp only [h95, h96, h80, h24, Machine.upd_apply]; simp
  · config_simp; simp only [h95, h96, h80, h24, Machine.upd_apply]; grind
  · config_simp; simp only [h95, h96, h80, h24, Machine.upd_apply]; grind
  · unfold RbBRG at h1
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
set_option maxHeartbeats 8000000 in
theorem rbInit_exec (hw : WordsBounded W c) {B J : ℕ}
    (hA : c.nreg ALLOC = B) (h64 : c.nreg 160064 = J) (hW : B + 2 * J ≤ W) :
    ∃ c' k, Exec P W rbInit c c' k ∧ k = 5 ∧ WordsBounded W c' ∧
      c'.nreg 160094 = B ∧ c'.nreg 160095 = B + 2 * J ∧ c'.nreg 160096 = c.nreg 160063 ∧
      c'.nreg 160097 = 0 ∧ (∀ r, ¬ RbRG r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zuksg
  unfold rbInit
  exec_block
  all_goals try (config_simp; (try simp only [hA, h64]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  · simp_all
  · config_simp; omega
  · config_simp
  · config_simp
  · unfold RbRG at h1
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])

/-- The invariant of the rebuild after `t` entries. -/
def RbInv (W : ℕ) (c0 : Config) (B J : ℕ) (e : ℕ → ℕ) (t : ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 160097 = t ∧ c.nreg 160064 = J ∧ c.nreg 160095 = B + 2 * zthav ∧
    c.nreg ALLOC = B + 2 * t ∧ (t < J → c.nreg 160096 = e ztjjb) ∧
    (∀ k, J - t ≤ k → k < J → c.nmem ztgda = c0.nmem ztqmf ∧
      c.nmem ztelt = c0.nmem ztlnd) ∧
    (∀ a, (a < B + 2 * zthav ∨ B + 2 * J ≤ a) → c.nmem a = c0.nmem a) ∧
    (∀ r, ¬ RbBRG r → r ≠ ALLOC → c.nreg r = c0.nreg r) ∧
    c.rreg = c0.rreg ∧ c.rmem = c0.rmem ∧ c.output = c0.output
set_option maxHeartbeats 16000000 in
/-- **The rebuild.** -/
theorem rbS_exec (hw : WordsBounded W c) {B J : ℕ} {e : ℕ → ℕ}
    (hA : c.nreg ALLOC = B) (h64 : c.nreg 160064 = J) (h24 : c.nreg 160024 = 1)
    (h80 : c.nreg 160080 = 2) (h63 : 1 ≤ J → c.nreg 160063 = e (J - 1))
    (hcell : ∀ q, q < J → e q + 3 ≤ B) (hlink : ∀ q, q < J → 1 ≤ q → c.nmem ztlne = e ztcfe)
    (hW : B + 2 * J + 1 ≤ W) :
    ∃ c' k, Exec P W rbS c c' k ∧ k ≤ 13 * J + 7 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = B + 2 * J ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧ c'.nreg 160094 = B ∧
      (∀ k, k < J → c'.nmem ztgda = c.nmem ztqmf ∧
        c'.nmem ztelt = c.nmem ztlnd) ∧
      (∀ a, (a < B ∨ B + 2 * J ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RbRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  obtain ⟨c1, k1, e1, hk1, hw1, i94, i95, i96, i97, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    rbInit_exec (P := P) hw hA h64 by_omega
  have r1 : ∀ r, ¬ RbRG r → c1.nreg r = c.nreg r := fr1
  obtain ⟨c', k, e', ⟨t, ⟨hw', h97', h64', h95', hA', h96', hent, hout, fr', hrr', hrm', ho'⟩, htJ⟩,
      htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 160097) (b := 160064) (body := rbBody)
      (fun c => ∃ t, RbInv W c1 B J e t c ∧ t ≤ J) (fun c => 13 * (J - c.nreg 160097))
      ztesf (fun c ⟨t, h, _⟩ => h.1)
      (fun c2 ⟨t, ⟨hw2, h97, h64c, h95, hA2, h96, hent, hout, fr2, hrr2, hrm2, ho2⟩, htJ⟩ htest => by
        rw [h97, h64c] at htest
        have r24 : ztizc := by
          zufmw

        have r80 : c2.nreg 160080 = 2 := by
          zufmw

        set kk := J - 1 - t with hkk
        have hek := hcell kk by_omega
        obtain ⟨c3, k3, e3, hk3, hw3, q95, q96, q97, qA, qm0, qm1, qm, fr3, hrr3, hrm3, ho3⟩ :=
          rbBody_exec (P := P) hw2 h95 (h96 htest) h97 hA2 r24 r80 by_omega by_omega
            by_omega by_omega by_omega
        have q64 : c3.nreg 160064 = J := by
          rw [fr3 _ ztggn by_omega]; omega
        refine ⟨c3, k3, e3, ⟨t + 1, ⟨hw3, q97, q64, by rw [q95]; omega, by_omega,
          fun ht1 => ?_, fun k a1 a2 => ?_, fun a ha => ?_, fun r h1 h2 => ?_,
          by grind, by_grind, by_grind⟩, by_omega⟩, ?_, by_omega⟩
        · rw [q96, hout _ ztec, hm1, hlink kk by_omega by_omega]
          rfl
        · rcases Nat.lt_or_ge k zthav with hk | hk
          · have hkq : k = kk := by_omega
            subst hkq
            zujx
            · rw [show B + 2 * ztjjb = B + 2 * zthav - 2 by omega, qm0,
                hout _ ztec, hm1]
            · rw [show B + 2 * ztjjb + 1 = B + 2 * zthav - 2 + 1 by omega, qm1,
                hout _ ztec, hm1]
          · obtain ⟨b1, b2⟩ := hent k hk a2
            zunmh
            omega
        · zuhnh
        · grind
        omega)
      ⟨0, ⟨hw1, i97, by zuolj; omega, by_omega,
        by rw [r1 _ ztcuo, hA]; simp,
        fun h => by_grind, fun k a1 a2 => by_omega,
        fun a _ => rfl, fun r _ _ => rfl, rfl, rfl, rfl⟩, Nat.zero_le _⟩
  have htJ' : t = J := by_omega
  have hk' : k ≤ 13 * J + 2 := by
    omega
  zufwy
  have hA1 : c1.nreg ALLOC = B := by zuolj; exact hA
  refine ⟨c', k1 + k, .seq e1 e', by_omega, hw', by_omega, by_omega,
    by rw [fr' _ ztggn by_omega]; omega,
    fun k hk => ?_, fun a ha => ?_, fun r h1 h2 => ?_, by_grind, by_grind,
    by grind⟩
  · rw [← hm1]; exact hent k by_omega hk
  · grind
  · rw [fr' r (by unfold RbBRG; unfold RbRG at h1; omega) h2]; grind
end proofs

/-- **The new array holds the next level.** -/
theorem levelAt_of_cells {P : Polygon} {m m' : ℕ → ℕ} {B hp : ℕ} {ns : List Shp} {e : ℕ → ℕ}
    (hc : CellSt P m B hp ns e)
    (hent : ∀ k, k < ns.length → m' ztgda = m ztqmf ∧ m' ztelt = m ztlnd)
    (hout : ∀ a, a < B → m' a = m a) : LevelAt P m' (B + 2 * ns.length) B hp ns := by
  zugf
  obtain ⟨-, -, C, h1, h2, h3⟩ := hc k hk
  refine ⟨C, h1, h2, ?_⟩
  rw [(hent k hk).1, (hent k hk).2]
  exact (h3.agree hout).mono by_omega
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs Chazelle.Merge Finset
@[expose] public section
def lvInit : Stmt := block [.constN 160062 0, .constN 160064 0, .copyN 160065 160066,
  .subN 160067 160014 160024, .addN 160034 160033 160024]

/-- The target: the final granularity when at most two nodes are left. -/
def tgtS : Stmt := .ifLtN 160014 160083 ztoyl .skip

/-- The end of a level. -/
def lvFin : Stmt := block [.copyN 160066 160094, .copyN 160014 160064, .copyN 160033 160034]

/-- **One level of the merge tree.** -/
def levelS (sM : Stmt) : Stmt :=
  .seq lvInit (.seq tgtS (.seq ztwbk (.seq carryS (.seq rbS lvFin))))

/-- The target of a level of `j` nodes. -/
def lvTgt (Gl j γ₀ : ℕ) : ℕ := if j < 3 then Gl else γ₀ + 1

/-- The cost bound of a level. -/
def lvCost (κ F G H : ℕ → ℕ) (ns : List Shp) (γ₀ : ℕ) : ℕ :=
  ztytj +
    13 * ztzzv + 40

/-- The registers of band `bL41` written by a level. -/
def LvRG (r : ℕ) : Prop :=
  PairRG r ∨ RbRG r ∨ r = 160066 ∨ r = 160014 ∨ r = 160033 ∨ r = 160034 ∨ r = 160067
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 8000000 in
theorem lvInit_exec (hw : WordsBounded W c) {B j γ₀ : ℕ}
    (h66 : c.nreg 160066 = B) (h14 : c.nreg 160014 = j) (h33 : c.nreg 160033 = γ₀)
    (h24 : c.nreg 160024 = 1) (hW : γ₀ + 1 ≤ W) :
    ∃ c' k, Exec P W lvInit c c' k ∧ k = 5 ∧ WordsBounded W c' ∧
      c'.nreg 160062 = 0 ∧ c'.nreg 160064 = 0 ∧ c'.nreg 160065 = B ∧ c'.nreg 160067 = j - 1 ∧
      c'.nreg 160034 = γ₀ + 1 ∧
      (∀ r, r ≠ 160062 → r ≠ 160064 → r ≠ 160065 → r ≠ 160067 → r ≠ 160034 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lvInit
  exec_block
  all_goals try (config_simp; (try simp only [h66, h14, h33, h24]); omega)
  simp_all
set_option maxHeartbeats 8000000 in
theorem tgtS_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W tgtS c c' k ∧ k ≤ 2 ∧ WordsBounded W c' ∧
      c'.nreg 160034 = (if c.nreg 160014 < c.nreg 160083 then c.nreg 160032 else c.nreg 160034) ∧
      ztivb ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  by_cases h : c.nreg 160014 < c.nreg 160083
  · obtain ⟨c', k, e, hk, hw', h34, fr, hm, hrr, hrm, ho⟩ : ∃ c' k, Exec P W
        ztoyl c c' k ∧ k = 1 ∧ WordsBounded W c' ∧
        c'.nreg 160034 = c.nreg 160032 ∧ ztivb ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
      exec_block
      simp_all
    exact ⟨c', k + 1, .ifLtN_true h e, by_omega, hw', by_simp_all, fr, hm, hrr,
      hrm, ho⟩
  · exact ⟨c, 2, .ifLtN_false h ztjd, le_rfl, hw, by_simp_all, by_omega, rfl,
      rfl, rfl, rfl⟩
set_option maxHeartbeats 8000000 in
theorem lvFin_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W lvFin c c' k ∧ k = 3 ∧ WordsBounded W c' ∧
      c'.nreg 160066 = c.nreg 160094 ∧ c'.nreg 160014 = c.nreg 160064 ∧
      c'.nreg 160033 = c.nreg 160034 ∧
      (∀ r, r ≠ 160066 → r ≠ 160014 → r ≠ 160033 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lvFin
  exec_block
  simp_all
set_option maxHeartbeats 16000000 in
/-- **One level of the merge tree on the RAM.** -/
theorem level_exec (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hWn : P.n + 3 ≤ W)
    {sM : Stmt} {κ F G H : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hMM : MergeMeets sM κ F G H X Ok) (hXc : X.CapLocal)
    (hOk : ∀ C : Chain, C.P = Qof P → Ok P ztc)
    {c : Config} (hw : WordsBounded W c) {A0 B hp hX γ₀ Gl : ℕ} {ns : List Shp}
    (hj : 2 ≤ ns.length)
    (hA : c.nreg ALLOC = A0) (h66 : c.nreg 160066 = B) (h14 : c.nreg 160014 = ns.length)
    (h33 : c.nreg 160033 = γ₀) (h32 : c.nreg 160032 = Gl) (h00 : c.nreg 160000 = hX)
    (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2) (h81 : c.nreg 160081 = 5)
    (h83 : c.nreg 160083 = 3) (h84 : c.nreg 160084 = 4)
    (hL : LevelAt P c.nmem A0 B hp ns) (hc : Consec ns) (hB : B + 2 * ns.length ≤ A0)
    (hγ : ∀ k, k < ns.length → (nd ns k).2.2 ≤ γ₀)
    (hγ1 : ∀ k, k < ns.length → 1 ≤ (nd ns k).2.2)
    (hXh : X.holds P c.nmem hX A0) (hcap : γ₀ + fuseLoss ≤ X.cap P c.nmem hX)
    (htg : γ₀ + fuseLoss ≤ lvTgt Gl ns.length γ₀) (hγW : γ₀ + 1 ≤ W)
    (hbud : A0 + lvCost κ F G H ns γ₀ ≤ W) :
    ∃ c' k, Exec P W ztvye c c' k ∧ k ≤ lvCost κ F G H ns γ₀ ∧ WordsBounded W c' ∧
      A0 ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A0 + k ∧
      c'.nreg 160014 = (pairUp ns ztftd).length ∧
      c'.nreg 160033 = lvTgt Gl ns.length γ₀ ∧
      (∃ B', c'.nreg 160066 = B' ∧
        B' + 2 * (pairUp ns ztftd).length ≤ c'.nreg ALLOC ∧
        LevelAt P c'.nmem ztdo B' hp ztzxo) ∧
      ztiub ∧ ztiuc ∧
      c'.output = c.output ∧
      (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ LvRG r → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ LvRG r → c'.rreg r = c.rreg r) ∧
      X.holds P c'.nmem hX ztdo ∧ X.cap P c'.nmem hX = X.cap P c.nmem hX := by
  zuk
  simp only [lvCost] at hbud ⊢
  set t := lvTgt Gl ns.length γ₀ with htdef
  have hlen' := pairUp_length ns t
  -- 1. init
  obtain ⟨c1, k1, e1, hk1, hw1, i62, i64, i65, i67, i34, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    lvInit_exec (P := P) hw h66 h14 h33 h24 hγW
  have r1 : ∀ r, 160000 ≤ r → r < 160034 → c1.nreg r = c.nreg r := by_grind
  have r1' : ∀ r, 160067 < r → c1.nreg r = c.nreg r := fun r a =>
    fr1 r by_omega by_omega by_omega by_omega by_omega
  -- 2. the target
  obtain ⟨c2, k2, e2, hk2, hw2, t34, fr2, hm2, hrr2, hrm2, ho2⟩ := tgtS_exec (P := P) hw1
  have t34' : c2.nreg 160034 = t := by
    rw [t34, r1 _ by_omega by_omega, r1' _ by_omega, r1 _ by_omega by_omega, i34, h14,
      h83, h32, htdef]
    rfl
  have r2 : ∀ r, r ≠ 160034 → r ≠ 160062 → r ≠ 160064 → r ≠ 160065 → r ≠ 160067 →
      c2.nreg r = c.nreg r := by_grind
  have m2 : ztsfg := by_grind
  have hA2 : c2.nreg ALLOC = A0 := by
    rw [r2 _ by_omega by_omega by_omega
      by_omega by_omega]; exact hA
  -- 3. the pair loop
  have hbud' : A0 + ∑ q ∈ range ztcwb, ztcfb ≤ W := by
    have : ∑ q ∈ range _, ztcfb ≤
        ∑ q ∈ range ztcwb, ztbrl :=
      Finset.sum_le_sum by_grind
    omega
  obtain ⟨c3, k3, e3, hk3, hψ3, hst⟩ := pairL_exec hG hWh hWn hMM hXc hOk hw2 (A0 := A0) (B := B)
    (hp := hp) (hX := hX) (γ₀ := γ₀) (tgt := t) (ns := ns) by_omega hA2
    ((fr2 _ by_omega).trans i62) ((fr2 _ by_omega).trans i65)
    ((fr2 _ by_omega).trans i64) ((fr2 _ by_omega).trans i67)
    by_grind t34'
    by_grind
    by_grind
    by_grind
    by_grind
    by_grind
    by_grind
    by_grind hc hB hγ hγ1 by_grind by_grind htg
    hbud'
  zuizh
  obtain ⟨-, -, -, -, s3A0, s3A1, s3m, s3rm, s3o, s3r, s3rr, s3X, s3cap, -⟩ := hst'
  -- 4. the carry
  obtain ⟨c4, k4, e4, hk4, hw4, a41, a42, a43, m43, rm43, o43, rr43, fr43, c64, ee, hcell, h63,
      hee0⟩ :=
    carryS_exec (hj := by_omega) hst
      by_grind
      by_grind
      by_grind
      by_grind hB (by
        omega)
  -- 5. the rebuild
  set B' := c4.nreg ALLOC with hB'
  have c4_24 : c4.nreg 160024 = 1 := by
    rw [fr43 _ ztddf by_omega,
      s3r _ ztdtu ztddf by_omega,
      r2 _ by_omega by_omega by_omega by_omega by_omega]; omega
  have c4_80 : c4.nreg 160080 = 2 := by
    rw [fr43 _ ztddf by_omega,
      s3r _ ztdtu ztddf by_omega,
      r2 _ by_omega by_omega by_omega by_omega by_omega]; omega
  have hsum8 : ∑ q ∈ range ztcwb, ztcfb + 13 * (pairUp ns t).length ≤
      ∑ q ∈ range ztcwb, ztbrl + 13 * ztzzv := by
    have : ∑ q ∈ range _, ztcfb ≤
        ∑ q ∈ range ztcwb, ztbrl :=
      Finset.sum_le_sum by_grind
    omega
  obtain ⟨c5, k5, e5, hk5, hw5, a5, a5k, b94, hent, hout, fr54, hrr54, hrm54, ho54⟩ :=
    rbS_exec (P := P) hw4 (J := (pairUp ns t).length) (e := ee) rfl c64 c4_24 c4_80
      (fun h => h63) (fun q hq => (hcell q hq).1) (fun q hq h1 => (hcell q hq).2.1 h1)
      by_omega
  have hLv : LevelAt P c5.nmem _ B' hp _ :=
    levelAt_of_cells hcell hent (fun a ha => hout a ztbbu)
  -- 6. the end
  obtain ⟨c6, k6, e6, hk6, hw6, f66, f14, f33, fr65, hm65, hrr65, hrm65, ho65⟩ :=
    lvFin_exec (P := P) hw5
  have hA6 : c6.nreg ALLOC = B' + 2 * (pairUp ns t).length := by
    rw [fr65 _ by_omega by_omega by_omega]; exact a5
  have mem64 : ∀ a, a < B' → c6.nmem a = c4.nmem a := fun a ha => by
    rw [hm65]; exact hout a ztbbu
  have hA3 := s3A0
  have f33' : c6.nreg 160033 = t := by
    rw [f33, fr54 _ ztcuo by_omega,
      fr43 _ ztddf by_omega,
      s3r _ ztdtu ztddf by_omega]
    omega
  refine ⟨c6, k1 + ztrd,
    .seq e1 ztvb, ?_, hw6, by_omega, by_omega,
    by rw [f14, fr54 _ ztcuo by_omega, c64],
    f33',
    by grind,
    fun a ha => ?_, fun a ha => ?_, by_grind,
    fun r h1 h2 h3 => ?_, fun r h1 h2 => ?_, ?_, ?_⟩
  · omega
  · rw [mem64 a by_omega, m43 a by_omega, s3m a ha, m2]
  · rw [hrm65, hrm54, rm43, s3rm a ha, hrm2, hrm1]
  · zumre
    rw [fr65 r by_omega by_omega by_omega, fr54 r ztbapk h3,
      fr43 r by_tauto h3, s3r r h1 by_tauto h3]
    exact r2 r by_omega ztbqa ztbqa
      ztbqa by_omega
  · zumre
    rw [hrr65, hrr54, rr43, s3rr r h1 by_tauto, hrr2, hrr1]
  · zumml
    refine X.mono _ _ _ _ _ by_grind
      (X.local_ _ _ _ _ _ ?_ s3X)
    intro a ha; rw [mem64 a by_omega, m43 a ha]
  · rw [hXc _ _ _ _ _ (fun a ha => by rw [mem64 a by_omega, m43 a ha]) s3X, s3cap, m2]
end proofs
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs Chazelle.Merge Finset
@[expose] public section
def treeS (sM : Stmt) : Stmt := .whileLtN 160024 160014 ztvye

/-- The cost bound of the merge tree (with `f` levels of fuel). -/
def totCost (κ F G H : ℕ → ℕ) (Gl : ℕ) : ℕ → List Shp → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, ns, γ₀ => if ns.length ≤ 1 then 0 else
      lvCost κ F G H ns γ₀ + 2 + totCost κ F G H Gl f ztzxo
        ztftd

/-- **The state of the merge tree** at a level `ns` with granularity bound `γ₀`. -/
def TreeSt (P : Polygon) (W : ℕ) (X : MemCtx) (cs : Config) (As hp hX Gl a L : ℕ)
    (ns : List Shp) (γ₀ : ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 160014 = ns.length ∧ c.nreg 160033 = γ₀ ∧
    (∃ B, c.nreg 160066 = B ∧ B + 2 * ns.length ≤ c.nreg ALLOC ∧
      LevelAt P c.nmem ztm B hp ns) ∧
    Consec ns ∧ 1 ≤ ns.length ∧ (nd ns 0).1 = a ∧ (ns.map fun x => x.2.1).sum = L ∧
    (∀ k, k < ns.length → (nd ns k).2.2 ≤ γ₀) ∧ (∀ k, k < ns.length → 1 ≤ (nd ns k).2.2) ∧
    (ns.length = 1 → (nd ns 0).2.2 = Gl) ∧ γ₀ + Nat.clog 2 ns.length ≤ Gl ∧
    As ≤ c.nreg ALLOC ∧ (∀ a, a < As → c.nmem a = cs.nmem a) ∧
    (∀ a, a < As → c.rmem a = cs.rmem a) ∧ c.output = cs.output ∧
    (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ LvRG r → r ≠ ALLOC → c.nreg r = cs.nreg r) ∧
    (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ LvRG r → c.rreg r = cs.rreg r) ∧
    X.holds P c.nmem hX ztm ∧ X.cap P c.nmem hX = X.cap P cs.nmem hX
theorem clog_half {j : ℕ} (hj : 2 ≤ j) : Nat.clog 2 j = Nat.clog 2 (ztl / 2) + 1 := by
  rw [Nat.clog_of_two_le by_norm_num hj, show j + 2 - 1 = j + 1 by omega]
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
/-- **The merge tree on the RAM.** -/
theorem tree_exec (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hWn : P.n + 3 ≤ W)
    {sM : Stmt} {κ F G H : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hMM : MergeMeets sM κ F G H X Ok) (hXc : X.CapLocal)
    (hOk : ∀ C : Chain, C.P = Qof P → Ok P ztc)
    {cs : Config} {As hp hX Gl a L : ℕ}
    (s32 : cs.nreg 160032 = Gl) (s00 : cs.nreg 160000 = hX)
    (s24 : cs.nreg 160024 = 1) (s80 : cs.nreg 160080 = 2) (s81 : cs.nreg 160081 = 5)
    (s83 : cs.nreg 160083 = 3) (s84 : cs.nreg 160084 = 4)
    (hGcap : Gl ≤ X.cap P cs.nmem hX) (hGW : Gl ≤ W) :
    ∀ (f : ℕ) (ns : List Shp) (γ₀ : ℕ) (c : Config), ns.length ≤ f →
      TreeSt P W X cs As hp hX Gl a L ns γ₀ c →
      c.nreg ALLOC + totCost κ F G H Gl f ns γ₀ ≤ W →
      ∃ c' k ns' γ', Exec P W ztwgw c c' k ∧ k ≤ totCost κ F G H Gl f ns γ₀ + 2 ∧
        c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧ ns'.length = 1 ∧
        TreeSt P W X cs As hp hX Gl a L ns' γ' c' := by
  zuk
  intro f
  induction f with
  | zero =>
    intro ns γ₀ c hf hst _
    have := hst.2.2.2.2.2.1; omega
  | succ f ih =>
    intro ns γ₀ c hf hst hbud
    obtain ⟨hw, h14, h33, ⟨B, h66, hB, hL⟩, hc, hj1, ha, hsum, hγ, hγ1, hone, hclog, hAs, hm,
      hrm, ho, hr, hrr, hX', hcap'⟩ := hst
    have cr : ∀ r, 160000 ≤ r → r < 170000 → ¬ LvRG r → c.nreg r = cs.nreg r := fun r a b h =>
      hr r (bandOK_l41 a b) h by_omega
    have nl : ∀ r, (r < 160035 ∨ ztneo ∨ ztnep) →
        r ≠ 160014 → r ≠ 160033 → r ≠ 160034 → ¬ LvRG r := by
      zuetf
      unfold LvRG PairRG DescRG RbRG at h5; omega
    zujtp
    · -- the loop ends
      have h1 : ns.length = 1 := by_omega
      refine ⟨c, 2, ns, γ₀, .whileLtN_false ?_ hw, by_omega, by_omega, h1,
        ⟨hw, h14, h33, ⟨B, h66, hB, hL⟩, hc, hj1, ha, hsum, hγ, hγ1, hone, hclog, hAs, hm, hrm,
          ho, hr, hrr, hX', hcap'⟩⟩
      grind
    · -- one level
      zudhr

      have hcl := clog_half hj2
      have hcl1 : 1 ≤ Nat.clog 2 ns.length := by_omega
      zudom
      have htg : γ₀ + fuseLoss ≤ t := by
        zvnup; unfold lvTgt; split_ifs <;> omega
      have hbud' : c.nreg ALLOC + lvCost κ F G H ns γ₀ ≤ W := by
        have : totCost κ F G H Gl ztbax ns γ₀ = lvCost κ F G H ns γ₀ + 2 +
            totCost κ F G H Gl f ztdvp t := by
          zudkq
        omega
      have cv : ∀ r, (r < 160035 ∨ ztnep) → 160000 ≤ r →
          r ≠ 160014 → r ≠ 160033 → r ≠ 160034 → c.nreg r = cs.nreg r :=
        fun r h1 h2 h3 h4 h5 => cr r h2 by_omega (nl r by_omega h3 h4 h5)
      have c32 : c.nreg 160032 = Gl := by
        grind
      have c00 : c.nreg 160000 = hX := by
        grind
      have c24 : ztplx := by
        grind
      have c80 : c.nreg 160080 = 2 := by
        grind
      have c81 : c.nreg 160081 = 5 := by
        grind
      have c83 : ztunp := by
        grind
      have c84 : c.nreg 160084 = 4 := by
        grind
      obtain ⟨c1, k1, e1, hk1, hw1, hA1, hA1', l14, l33, ⟨B', l66, hB', hL'⟩, lm, lrm, lo, lr, lrr,
          lX, lcap⟩ :=
        level_exec hG hWh hWn hMM hXc hOk hw (A0 := c.nreg ALLOC) (B := B) (hp := hp) (hX := hX)
          (γ₀ := γ₀) (Gl := Gl) (ns := ns) hj2 rfl h66 h14 h33 c32 c00 c24 c80 c81 c83 c84
          hL hc hB hγ hγ1 hX' by_omega htg by_omega hbud'
      zuhzf
      have hγt : γ₀ ≤ t := by_omega
      have hst1 : TreeSt P W X cs As hp hX Gl a L ztdvp t c1 := by
        refine ⟨hw1, l14, l33, ⟨B', l66, hB', hL'⟩, consec_pairUp t hc, by_omega,
          by rw [nd_pairUp_zero ns t by_omega]; exact ha, by zuoym; omega,
          pairUp_gran hγ hγt, pairUp_gran_pos hγ1 by_omega, fun h => ?_, ?_, by_omega,
          fun x hx => by rw [lm x by_omega]; grind,
          fun x hx => by rw [lrm x by_omega]; grind, by_grind,
          fun r h1 h2 h3 => by rw [lr r h1 h2 h3]; grind,
          fun r h1 h2 => by rw [lrr r h1 h2]; exact hrr r h1 h2, lX, by_omega⟩
        · rw [nd_pairUp_merge ns t 0 by_omega]
          simp only [ht]; unfold lvTgt; zunab
        · rw [hlen']
          zvnup; unfold lvTgt; split_ifs with h3
          · have : ztftn / 2 = 1 := by_omega
            rw [this, Nat.clog_one_right]; omega
          · omega
      have hbud1 : c1.nreg ALLOC + totCost κ F G H Gl f ztdvp t ≤ W := by
        have : totCost κ F G H Gl ztbax ns γ₀ = lvCost κ F G H ns γ₀ + 2 +
            totCost κ F G H Gl f ztdvp t := by
          zudkq
        omega
      obtain ⟨c', k, ns', γ', e', hk', hA', h1', hst'⟩ :=
        ih ztdvp t c1 by_omega hst1 hbud1
      refine ⟨c', k1 + 2 + k, ns', γ', .whileLtN_true ?_ e1 e', ?_, by_omega, h1', hst'⟩
      · omega
      · have : totCost κ F G H Gl ztbax ns γ₀ = lvCost κ F G H ns γ₀ + 2 +
            totCost κ F G H Gl f ztdvp t := by
          zudkq
        omega
end proofs
def leafP (G0 : ℕ) (x : Shp) : Bool := decide (x.2.2 ≤ G0)

/-- The cost factor of one merge. -/
def phiL (κ F G H : ℕ → ℕ) (Gl L : ℕ) : ℕ :=
  κ 4 * F Gl * G Gl * (H Gl + Nat.clog 2 ztgt + 1)

/-- The cost bound of one level. -/
def lvBound (κ F G H : ℕ → ℕ) (Gl G0 J L LS0 : ℕ) : ℕ :=
  phiL κ F G H Gl L * ztyox + 344 * J + 40
theorem sum_range_nd (f : Shp → ℕ) : ∀ ns : List Shp,
    ∑ k ∈ range ns.length, f zthit = (ns.map f).sum
  | [] => by_simp
  | a :: l => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [nd_cons_succ, nd_cons_zero]
    rw [sum_range_nd f l]; ring
theorem sum_pairs (g : ℕ → ℕ) : ∀ p : ℕ,
    ∑ q ∈ range p, (g ztbtl + g ztbhl) = ∑ k ∈ range ztdsl, g k
  | 0 => by_simp
  | p + 1 => by
    rw [Finset.sum_range_succ, sum_pairs g p, show 2 * ztr = 2 * p + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ]; ring
theorem sublist_sum_le {l₁ l₂ : List ℕ} (h : l₁.Sublist l₂) : l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => simp
  | cons a _ ih => zuosc; omega
  | cons_cons a _ ih => zuosc; omega

/-- Two entries weigh at most the total. -/
theorem pair_le_sum (ns : List Shp) {q : ℕ} (hq : q < ns.length / 2) :
    (nd ns ztbtl).2.1 + (nd ns ztbhl).2.1 ≤ (ns.map fun x => x.2.1).sum := by
  zulrh
  have hsub : ({2 * q, 2 * q + 1} : Finset ℕ) ⊆ range ns.length := by
    grind
  have := Finset.sum_le_sum_of_subset (f := fun k => (nd ns k).2.1) hsub
  simp_all
variable (κ F G H : ℕ → ℕ)
/-- **One merge.** -/
theorem pairCost_le (hF : Monotone F) (hG : Monotone G) (hH : Monotone H)
    (ns : List Shp) {γ₀ Gl q : ℕ} (hq : q < ns.length / 2) (hγ : γ₀ + fuseLoss ≤ Gl) :
    pairCost κ F G H ns γ₀ q ≤ ztwtv *
      phiL κ F G H Gl (ns.map fun x => x.2.1).sum := by
  unfold pairCost mergeCostV phiL
  have h1 := hF hγ; have h2 := hG hγ; have h3 := hH hγ
  have h4 := Nat.clog_mono_right 2 (Nat.add_le_add_right (pair_le_sum ns hq) 1)
  calc κ 4 * ztwtv * F ztoku *
        G ztoku * (H ztoku +
          Nat.clog 2 ((nd ns ztbtl).2.1 + (nd ns ztbhl).2.1 + 1) + 1)
      ≤ κ 4 * ztwtv * F Gl * G Gl *
        (H Gl + Nat.clog 2 ((ns.map fun x => x.2.1).sum + 1) + 1) := by gcongr
    _ = _ := by_ring

/-- **One level.** -/
theorem lvCost_le (hF : Monotone F) (hG : Monotone G) (hH : Monotone H)
    (ns : List Shp) {γ₀ Gl : ℕ} (hγ : γ₀ + fuseLoss ≤ Gl) :
    lvCost κ F G H ns γ₀ ≤ phiL κ F G H Gl (ns.map fun x => x.2.1).sum *
      ztmzi + 344 * ns.length + 40 := by
  set Φ := phiL κ F G H Gl (ns.map fun x => x.2.1).sum with hΦ
  set p := ns.length / 2 with hp
  have h1 : ∑ q ∈ range p, ztbrl ≤
      ∑ q ∈ range p, ztxde :=
    Finset.sum_le_sum fun q hq => by
      have := pairCost_le κ F G H hF hG hH ns (Finset.mem_range.mp hq) hγ
      grind
  have h2 : ∑ q ∈ range p, ztxde =
      ztykm * Φ + p * ztkhs := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_pairs (fun k => kb zthit),
      Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h3 : ∑ k ∈ range ztdsl, kb zthit ≤ (ns.map kb).sum := by
    zulrh
    exact Finset.sum_le_sum_of_subset ztmbc
  have h4 : ztykm * Φ ≤ (ns.map kb).sum * Φ :=
    Nat.mul_le_mul_right _ h3
  have h5 : p * ztkhs ≤ ns.length * Φ + 331 * ns.length := by
    have : p ≤ ns.length := by_omega
    nlinarith
  unfold lvCost
  grind
theorem kb_split (G0 : ℕ) : ∀ ns : List Shp, (ns.map kb).sum =
    ((ns.filter ztmmf).map kb).sum + ((ns.filter fun x => !leafP G0 x).map kb).sum
  | [] => by_simp
  | a :: l => by
    rw [List.filter_cons, List.filter_cons, List.map_cons, List.sum_cons, kb_split G0 l]
    grind
theorem sum_lin : ∀ ns : List Shp, (ns.map fun x => 60 * ztelb).sum =
    120 * (ns.map fun x => x.2.1).sum + 420 * ns.length
  | [] => by_simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, sum_lin l]; ring

/-- The merged nodes. -/
theorem nonleaf_le (G0 : ℕ) : ∀ ns : List Shp, (∀ x ∈ ns, leafP G0 x = false → G0 + 1 ≤ x.2.2) →
    ((ns.filter fun x => !leafP G0 x).map kb).sum ≤
      (ns.map fun x => 60 * ztelb).sum / ztctb
  | [], _ => by_simp
  | a :: l, h => by
    have ih := nonleaf_le G0 l fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    have hsplit : 60 * ztjfe / ztctb + (l.map fun x => 60 * ztelb).sum / ztctb
        ≤ (60 * ztjfe + (l.map fun x => 60 * ztelb).sum) / ztctb :=
      Nat.div_add_div_le_add_div
    cases hl : leafP G0 a
    · simp only [Bool.not_false, ite_true, List.map_cons, List.sum_cons]
      have ha := h a List.mem_cons_self hl
      have hk : kb a ≤ 60 * ztjfe / ztctb := Nat.div_le_div_left ha by_omega
      omega
    grind

/-- The leaves of the next level are leaves of this one. -/
theorem leaves_pairUp_sublist {G0 t : ℕ} (ht : G0 < t) : ∀ ns : List Shp,
    ((pairUp ns t).filter ztmmf).Sublist (ns.filter ztmmf)
  | [] => by_rfl
  | [a] => by_rfl
  | a :: b :: rest => by
    have ih := leaves_pairUp_sublist ht rest
    have hm : leafP G0 ztnqw = false := by
      unfold leafP; simp_all
    simp only [pairUp, List.filter_cons, hm, Bool.false_eq_true, ite_false]
    grind
theorem mem_pairUp {t : ℕ} : ∀ {ns : List Shp} {x : Shp}, x ∈ pairUp ns t → x ∈ ns ∨ x.2.2 = t
  | [], _, h => by_tauto
  | [_], _, h => by_tauto
  | a :: b :: rest, x, h => by
    simp only [pairUp, List.mem_cons] at h
    zuy
    · simp_all
    · rcases mem_pairUp h with h' | h'
      · simp_all
      omega

/-- The invariant of the cost analysis along the levels. -/
def PInv (G0 Gl J L LS0 : ℕ) (ns : List Shp) (γ₀ : ℕ) : Prop :=
  1 ≤ ns.length ∧ ns.length ≤ J ∧ (ns.map fun x => x.2.1).sum = L ∧
    γ₀ + Nat.clog 2 ns.length ≤ Gl ∧ G0 ≤ γ₀ ∧ ((ns.filter ztmmf).map kb).sum ≤ LS0 ∧
    ∀ x ∈ ns, leafP G0 x = false → G0 + 1 ≤ x.2.2

/-- **The cost of the merge tree.** -/
theorem totCost_le (hF : Monotone F) (hG : Monotone G) (hH : Monotone H)
    {G0 Gl J L LS0 : ℕ} : ∀ (f : ℕ) (ns : List Shp) (γ₀ : ℕ), ns.length ≤ f →
    PInv G0 Gl J L LS0 ns γ₀ →
    totCost κ F G H Gl f ns γ₀ ≤ Nat.clog 2 ns.length * (lvBound κ F G H Gl G0 J L LS0 + 2) := by
  intro f
  induction f with
  | zero => intro ns γ₀ hf h; have := h.1; omega
  | succ f ih =>
    intro ns γ₀ hf h
    obtain ⟨h1, hJ, hL, hcl, hG0, hLS, hnl⟩ := h
    zujtp
    · rw [totCost, ite_eq_left hlen]; omega
    · zudhr

      have hcl2 := clog_half hj2
      zudom
      have htγ : γ₀ + 1 ≤ t := by zvnup; unfold lvTgt; grind
      rw [totCost, ite_eq_right hlen]
      rw [← ht]
      -- this level
      have hlv := lvCost_le κ F G H hF hG hH ns (γ₀ := γ₀) (Gl := Gl) by_omega
      zvnlm at hlv
      have hkb : (ns.map kb).sum ≤ LS0 + ztckq / ztctb := by
        rw [kb_split G0 ns]
        have := nonleaf_le G0 ns hnl
        rw [sum_lin, hL] at this
        have : (120 * L + 420 * ns.length) / ztctb ≤ ztckq / ztctb :=
          Nat.div_le_div_right by_omega
        omega
      have hlvb : lvCost κ F G H ns γ₀ ≤ lvBound κ F G H Gl G0 J L LS0 := by
        unfold lvBound
        have : phiL κ F G H Gl L * ztmzi ≤
            phiL κ F G H Gl L * ztyox :=
          Nat.mul_le_mul_left _ by_omega
        omega
      -- the next level
      zuhzf
      have hinv : PInv G0 Gl J L LS0 ztdvp t := by
        refine ⟨by_omega, by_omega, by zuoym; exact hL, ?_, by_omega,
          le_trans (sublist_sum_le ((leaves_pairUp_sublist by_omega ns).map kb)) hLS,
          fun x hx hxl => ?_⟩
        · rw [hlen', ht]; unfold lvTgt; split_ifs with h3
          · rw [show ztftn / 2 = 1 by omega, Nat.clog_one_right]; omega
          · omega
        · rcases mem_pairUp hx with h' | h'
          · grind
          · omega
      have := ih ztdvp t by_omega hinv
      rw [hlen'] at this
      rw [hcl2]
      nlinarith
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Chazelle
@[expose] public section
variable {A : ℕ} {m : ℕ → ℕ} {Φ : (ℕ → ℕ) → Prop}

/-- A pinned cell lies below the bound. -/
theorem addr_lt (h : Robust A m Φ) {x v : ℕ}
    (hΦ : ∀ m', ztwv → Φ m' → m' x = v) : x < A := by
  zubdk

  have := hΦ m' he zthho
  grind

/-- A cell bounded by a constant lies below the bound. -/
theorem le_lt (h : Robust A m Φ) {x v : ℕ}
    (hΦ : ∀ m', ztwv → Φ m' → m' x ≤ v) : x < A := by
  zubdk

  have := hΦ m' he zthho
  grind

/-- A pointer to a pinned cell lies below the bound. -/
theorem ptr_lt (h : Robust A m Φ) {p y v : ℕ}
    (hΦ : ∀ m', ztwv → Φ m' → m' (m' p + y) = v) : p < A := by
  zucuz

  let m' : ℕ → ℕ := fun a => if a = p then V else if a = V + y then v + 1 else m a
  have he : ztbrd := fun a ha => by
    grind
  have := hΦ m' he zthho
  grind

/-- One level of indirection before a bounded address. -/
theorem bound2_lt (h : Robust A m Φ) {p u : ℕ}
    (hΦ : ∀ m', ztwv → Φ m' → m' ztrtv < A) : p < A := by
  zucuz

  let m' : ℕ → ℕ := fun a => if a = p then V else if a = V + u then A else m a
  have he : ztbrd := fun a ha => by
    grind
  have := hΦ m' he zthho
  grind

/-- Two levels of indirection before a bounded address. -/
theorem bound3_lt (h : Robust A m Φ) {p u w : ℕ}
    (hΦ : ∀ m', ztwv → Φ m' → m' (m' ztrtv + w) < A) : p < A := by
  zucuz

  let V2 := V + u + 1
  let m' : ℕ → ℕ := fun a =>
    if a = p then V else if a = V + u then V2 else if a = V2 + w then A else m a
  have he : ztbrd := fun a ha => by
    grind
  have := hΦ m' he zthho
  grind

/-- A robust normal form lies below the bound. -/
theorem nfWithin_lt {f : ℕ} {N : NF} (hN : NFWithin m f A N) : f < A := by
  by_contra hf
  let m' : ℕ → ℕ := fun a => if a = f then m f + 1 else m a
  have he : ztbrd := fun a ha => by_grind
  have h1 := (hN m' he).1
  have h2 := hN.holds.1
  grind

/-- **The cells of the grade table lie below the bound.** -/
theorem tab_lt {O : OracleIface} {P : Polygon} {h : ℕ}
    (hR : Robust A m fun m' => GradeRaw O P m' h A) (hn : 2 ≤ P.n) (hΛ : 1 ≤ m h) :
    h < A ∧ h + 1 < A ∧ h + 2 < A ∧ h + 3 < A ∧
    m ztzgl = P.n ∧ m (m ztgn + 1) = topGrade P.n ∧ m ztgn + 1 < A ∧
    (∀ i, i ≤ topGrade P.n + 1 → m (m ztgn + 2 + i) = 2 ^ i ∧
      m (m ztgn + topGrade P.n + 4 + i) = Cost.ceilBeta i ∧
      m ztgn + 2 + i < A ∧ m ztgn + topGrade P.n + 4 + i < A) ∧
    (∀ y, y ≤ P.n → m (m ztbba + y) = y / 2 ∧ m ztbba + y < A) ∧
    (∀ g i, g < m h → i < gradeCount P.n g →
      m zteu + g < A ∧ m ztwjz + 3 * i + 2 < A ∧
      m (m ztbajn + 2) = gradeGran g ∧
      m ztbajn + 2 < A) := by
  zumbr
  -- the header
  have h0 : ztpox := le_lt hR (x := h) (v := topGrade P.n + 1) fun m' _ hm' => hm'.1
  have h1 : ztsir := ptr_lt hR (p := h + 1) (y := 0) (v := P.n) fun m' _ hm' => hm'.2.1.1
  have h3 : ztsit := ptr_lt hR (p := h + 3) (y := 2) (v := 1) fun m' _ hm' => by
    have := hm'.2.2.1 2 hn; omega
  have h2 : ztsis := bound3_lt hR (p := h + 2) (u := 0) (w := 3 * 0) fun m' he hm' => by
    obtain ⟨-, -, -, -, hwf, -⟩ := hm'.2.2.2 0 0 by_grind
      (by unfold gradeCount; omega)
    have := hwf.1; omega
  refine ⟨h0, h1, h2, h3, hG.2.1.1, hG.2.1.2.1, ?_, fun i hi => ?_, fun y hy => ?_,
    fun g i hg hi => ?_⟩
  · exact addr_lt hR (v := topGrade P.n) fun m' he hm' => by
      have := hm'.2.1.2.1; simp_all
  · obtain ⟨a1, a2⟩ := hG.2.1.2.2.1 i hi
    refine ⟨a1, a2, addr_lt hR (v := 2 ^ i) fun m' he hm' => ?_,
      addr_lt hR (v := Cost.ceilBeta i) fun m' he hm' => ?_⟩
    · have := (hm'.2.1.2.2.1 i hi).1; simp_all
    · have := (hm'.2.1.2.2.1 i hi).2
      simp_all
  · refine ⟨hG.2.2.1 y hy, addr_lt hR (v := y / 2) fun m' he hm' => ?_⟩
    have := hm'.2.2.1 y hy; simp_all
  · have hgi : ∀ m' : ℕ → ℕ, ztwv → g < m' h := fun m' he => by_simp_all
    have hT : ztzjl := bound2_lt hR (p := m zteu + g) (u := 3 * i)
      fun m' he hm' => by
        obtain ⟨-, -, -, -, hwf, -⟩ := hm'.2.2.2 g i ztoas hi
        have := hwf.1; grind
    have hO : m ztwjz + 3 * i + 2 < A := ptr_lt hR (y := 2) (v := gradeGran g)
      fun m' he hm' => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e3⟩ := hm'.2.2.2 g i ztoas hi
        simp_all
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e3⟩ := hG.2.2.2 g i hg hi
    refine ⟨hT, hO, e3, addr_lt hR (v := gradeGran g) fun m' he hm' => ?_⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e4⟩ := hm'.2.2.2 g i ztoas hi
    simp_all
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs Chazelle
@[expose] public section
def proC : Stmt := block [.constN 160024 1, .constN 160080 2, .constN 160081 5, .constN 160082 6,
  .constN 160083 3, .constN 160084 4, .constN 160086 7, .constN 160087 8, .constN 160029 0]

/-- The registers of the cover and the table reads. -/
def proL : Stmt := block [.copyN 160010 160001, .addN 160011 160001 160002,
  .copyN 160026 160003,
  .addN 160031 160000 160083, .loadN 160020 160031,
  .addN 160031 160000 160024, .loadN 160101 160031,
  .addN 160021 160101 160080,
  .addN 160031 160000 160080, .loadN 160022 160031,
  .addN 160031 160022 160003, .subN 160031 160031 160024, .loadN 160031 160031,
  .addN 160031 160031 160080, .loadN 160031 160031, .addN 160031 160031 160080,
  .loadN 160033 160031,
  .addN 160031 160101 160024, .loadN 160102 160031, .addN 160031 160101 160102,
  .addN 160031 160031 160084, .addN 160031 160031 160003, .loadN 160103 160031,
  .addN 160031 160021 160103, .loadN 160032 160031, .constN 160014 0]

/-- `⌈log₂ λ⌉` in `160104`, by scanning the powers of two. -/
def clogS : Stmt := .seq ztkqw
  (.whileLtN 160105 160003 (block [.addN 160104 160104 160024, .addN 160031 160021 160104,
    .loadN 160105 160031]))

/-- `Gλ = 2^⌈βλ⌉ + λ (⌈log₂ λ⌉ + 2)` in `160032`. -/
def mulS : Stmt := .seq zthdx
  (.seq (.whileLtN 160108 160003 (block [.addN 160107 160107 160106, .addN 160108 160108 160024]))
    ztnrz)

/-- The whole host at the allocator; the record pointer above it. -/
def proH : Stmt := block [.copyN 160027 9999, .inputSize 160028, .subN 160028 160028 160024,
  .storeN 160027 160024, .addN 160030 160027 160024, .storeN 160030 160029,
  .addN 160030 160030 160024, .storeN 160030 160029, .addN 160030 160030 160024,
  .storeN 160030 160028, .addN 9999 9999 160086, .copyN 160015 9999]

/-- The registers written by `proL`. -/
def ProRG (r : ℕ) : Prop :=
  r = 160010 ∨ r = 160011 ∨ r = 160014 ∨ r = 160020 ∨ r = 160021 ∨ r = 160022 ∨
    r = 160026 ∨ (160031 ≤ r ∧ r ≤ 160033) ∨ (160101 ≤ r ∧ r ≤ 160103)
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 8000000 in
theorem proC_exec (hw : WordsBounded W c) (hW : 8 ≤ W) :
    ∃ c' k, Exec P W proC c c' k ∧ k = 9 ∧ WordsBounded W c' ∧
      c'.nreg 160024 = 1 ∧ c'.nreg 160080 = 2 ∧ c'.nreg 160081 = 5 ∧ c'.nreg 160082 = 6 ∧
      c'.nreg 160083 = 3 ∧ c'.nreg 160084 = 4 ∧ c'.nreg 160086 = 7 ∧ c'.nreg 160087 = 8 ∧
      c'.nreg 160029 = 0 ∧
      (∀ r, (r < 160024 ∨ (160029 < r ∧ r < 160080) ∨ 160087 < r ∨
        (160024 < r ∧ r < 160029) ∨ r = 160085) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold proC
  exec_block
  all_goals try omega
  refine ⟨rfl, by_omega, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
    by config_simp, by config_simp, by config_simp, by config_simp, fun r hr => ?_, rfl, rfl, rfl,
    rfl⟩
  zubi
  repeat (rw [Machine.upd_other _ _ _ by_omega])
set_option maxHeartbeats 16000000 in
theorem proL_exec (hw : WordsBounded W c) {h a L lam : ℕ}
    (h00 : c.nreg 160000 = h) (h01 : c.nreg 160001 = a) (h02 : c.nreg 160002 = L)
    (h03 : c.nreg 160003 = lam) (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2)
    (h83 : c.nreg 160083 = 3) (h84 : c.nreg 160084 = 4) (hl : 1 ≤ lam)
    (hW1 : h + 3 ≤ W) (hW2 : a + L ≤ W) (hW3 : c.nmem ztgn + 2 ≤ W)
    (hW4 : c.nmem zteu + lam ≤ W)
    (hW5 : c.nmem ztxqu + 2 ≤ W)
    (hW6 : c.nmem ztbaqd + 2 ≤ W)
    (hW7 : c.nmem ztgn + c.nmem ztzkr + 4 + lam ≤ W)
    (hW8 : c.nmem ztgn + 2 + c.nmem ztwuo
      ≤ W) :
    ∃ c' k, Exec P W proL c c' k ∧ k = 26 ∧ WordsBounded W c' ∧
      c'.nreg 160010 = a ∧ c'.nreg 160011 = a + L ∧ c'.nreg 160026 = lam ∧
      c'.nreg 160020 = c.nmem ztbba ∧ c'.nreg 160101 = c.nmem ztgn ∧
      c'.nreg 160021 = c.nmem ztgn + 2 ∧ c'.nreg 160022 = c.nmem zteu ∧
      c'.nreg 160033 = c.nmem (c.nmem ztbaqd + 2) ∧
      c'.nreg 160102 = c.nmem ztzkr ∧
      c'.nreg 160103 = c.nmem ztwuo ∧
      c'.nreg 160032 = c.nmem (c.nmem ztgn + 2 +
        c.nmem ztwuo) ∧
      c'.nreg 160014 = 0 ∧
      (∀ r, ¬ ProRG r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold proL
  exec_block
  all_goals try (config_simp; (try simp only [h00, h01, h02, h03, h24, h80, h83, h84]); omega)
  refine ⟨rfl, by_omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl,
    rfl⟩
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · config_simp
  · unfold ProRG at hr
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])

/-- `⌈log₂ λ⌉` is the first `c` with `λ ≤ 2^c`. -/
theorem clog_eq_of {lam c : ℕ} (h1 : lam ≤ 2 ^ c) (h2 : c ≤ Nat.clog 2 lam) :
    c = Nat.clog 2 lam := le_antisymm h2 (Nat.clog_le_of_le_pow h1)
set_option maxHeartbeats 8000000 in
theorem clogS_exec (hw : WordsBounded W c) {PW lam : ℕ}
    (h21 : c.nreg 160021 = PW) (h03 : c.nreg 160003 = lam) (h24 : c.nreg 160024 = 1)
    (hpow : ∀ i, i ≤ lam → c.nmem ztjlf = 2 ^ i) (hl : 1 ≤ lam) (hW : PW + lam ≤ W) :
    ∃ c' k, Exec P W clogS c c' k ∧ k ≤ 5 * lam + 4 ∧ WordsBounded W c' ∧
      c'.nreg 160104 = Nat.clog 2 lam ∧
      ztfjo ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hcl : ztscd := by
    exact Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  obtain ⟨c1, k1, e1, hk1, hw1, i04, i05, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      ztkqw c c1 k1 ∧ k1 = 2 ∧ WordsBounded W c1 ∧
      c1.nreg 160104 = 0 ∧ c1.nreg 160105 = 2 ^ 0 ∧
      (∀ r, r ≠ 160104 → r ≠ 160105 → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, by_omega, by config_simp, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; zuouf; have := hpow 0 by_omega; omega
    simp_all
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ ∃ i, i ≤ Nat.clog 2 lam ∧
    c'.nreg 160104 = i ∧ c'.nreg 160105 = 2 ^ i ∧
    ztfjo ∧ c'.nmem = c.nmem ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, e, ⟨hw', i, hi, h04, h05, fr', hm', hrr', hrm', ho'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 160105) (b := 160003)
      (body := block [.addN 160104 160104 160024, .addN 160031 160021 160104,
        .loadN 160105 160031]) I (fun c' => 5 * (Nat.clog 2 lam - c'.nreg 160104))
      ztbms
      (fun c2 ⟨hw2, i, hi, h04, h05, fr2, hm2, hrr2, hrm2, ho2⟩ htest => by
        have c03 : ztupf := by_simp_all
        have c21 : ztupg := by_simp_all
        have c24 : ztizc := by_simp_all
        zuiif
        have hil : i < Nat.clog 2 lam := by
          zukr
          have := Nat.le_pow_clog (b := 2) by_norm_num lam
          grind
        obtain ⟨c3, k3, e3, hk3, hw3, q04, q05, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
            (block [.addN 160104 160104 160024, .addN 160031 160021 160104, .loadN 160105 160031])
            c2 c3 k3 ∧ k3 = 3 ∧ WordsBounded W c3 ∧ c3.nreg 160104 = i + 1 ∧
            c3.nreg 160105 = 2 ^ ztg ∧
            (∀ r, r ≠ 160104 → r ≠ 160105 → r ≠ 160031 → c3.nreg r = c2.nreg r) ∧
            c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧
            c3.output = c2.output := by
          exec_block
          all_goals try (config_simp; (try simp only [h04, c21, c24]); omega)
          refine ⟨rfl, by_omega, by_simp_all, ?_, fun r a1 a2 a3 => ?_, rfl,
            rfl, rfl, rfl⟩
          · config_simp; simp only [h04, c21, c24, hm2]; grind
          simp_all
        refine ⟨c3, k3, e3, by_grind, ?_⟩
        omega)
      ⟨hw1, 0, Nat.zero_le _, i04, i05, fun r a1 a2 _ => fr1 r a1 a2, hm1, hrr1, hrm1, ho1⟩
  have c03 : c'.nreg 160003 = lam := by_simp_all
  zuiif
  have hk' : k ≤ 5 * Nat.clog 2 lam + 2 := by
    omega
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw', ?_, fr', hm', hrr', hrm', ho'⟩
  rw [h04]; exact clog_eq_of by_omega hi
set_option maxHeartbeats 8000000 in
theorem mulS_exec (hw : WordsBounded W c) {lam cl G2 : ℕ}
    (h04 : c.nreg 160104 = cl) (h03 : c.nreg 160003 = lam) (h32 : c.nreg 160032 = G2)
    (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2)
    (hW : G2 + lam * ztfqo + cl + 2 ≤ W) :
    ∃ c' k, Exec P W mulS c c' k ∧ k ≤ 4 * lam + 6 ∧ WordsBounded W c' ∧
      c'.nreg 160032 = G2 + lam * ztfqo ∧
      (∀ r, r ≠ 160032 → r ≠ 160106 → r ≠ 160107 → r ≠ 160108 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c1, k1, e1, hk1, hw1, i06, i07, i08, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      zthdx c c1 k1 ∧ k1 = 3 ∧
      WordsBounded W c1 ∧ c1.nreg 160106 = cl + 2 ∧ c1.nreg 160107 = 0 ∧ c1.nreg 160108 = 0 ∧
      (∀ r, r ≠ 160106 → r ≠ 160107 → r ≠ 160108 → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [h04, h80]); omega)
    simp_all
  obtain ⟨c2, k2, e2, hk2, hw2, -, -, h07, fr2, hm2, hrr2, hrm2, ho2⟩ :=
    forN (P := P) (W := W) (ri := 160108) (rn := 160003)
      (body := block [.addN 160107 160107 160106, .addN 160108 160108 160024])
      (fun i c' => WordsBounded W c' ∧ c'.nreg 160108 = i ∧ c'.nreg 160003 = lam ∧
        c'.nreg 160107 = i * ztfqo ∧
        (∀ r, r ≠ 160107 → r ≠ 160108 → c'.nreg r = c1.nreg r) ∧ c'.nmem = c1.nmem ∧
        c'.rreg = c1.rreg ∧ c'.rmem = c1.rmem ∧ c'.output = c1.output)
      lam 2 (fun i c' h => ztcbv)
      (fun i c2 hi ⟨hw2, h08, c03, h07, fr2, hm2, hrr2, hrm2, ho2⟩ => by
        have c06 : c2.nreg 160106 = cl + 2 := by_simp_all
        have c24 : ztizc := by
          simp_all
        have hbound : ztg * ztfqo ≤ lam * ztfqo := by_simp_all
        exec_block
        all_goals try (config_simp; (try simp only [h08, h07, c06, c24]); nlinarith)
        refine ⟨by_omega, by_omega, by_simp_all, by_simp_all, ?_,
          fun r a1 a2 => ?_, hm2, hrr2, hrm2, ho2⟩
        · config_simp; grind
        simp_all)
      (j₀ := 0) ⟨hw1, i08, by_simp_all,
        by omega, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩ (Nat.zero_le _)
  obtain ⟨c3, k3, e3, hk3, hw3, q32, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
      ztnrz c2 c3 k3 ∧ k3 = 1 ∧ WordsBounded W c3 ∧
      c3.nreg 160032 = G2 + lam * ztfqo ∧ (∀ r, r ≠ 160032 → c3.nreg r = c2.nreg r) ∧
      c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    have c32 : c2.nreg 160032 = G2 := by
      simp_all
    exec_block
    all_goals try (config_simp; (try simp only [c32, h07]); nlinarith)
    simp_all
  refine ⟨c3, k1 + ztdve, .seq e1 ztbpc, by_omega, hw3, q32,
    fun r a1 a2 a3 a4 => ?_, by_simp_all, by_simp_all,
    by simp_all, by_simp_all⟩
  simp_all
set_option maxHeartbeats 16000000 in
theorem proH_exec (hw : WordsBounded W c) {A : ℕ}
    (hA : c.nreg ALLOC = A) (h24 : c.nreg 160024 = 1) (h29 : c.nreg 160029 = 0)
    (h86 : c.nreg 160086 = 7) (hn : 1 ≤ P.n) (hW : A + 7 ≤ W) (hWn : P.n ≤ W) :
    ∃ c' k, Exec P W proH c c' k ∧ k = 12 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = A + 7 ∧ c'.nreg 160027 = A ∧ c'.nreg 160015 = A + 7 ∧
      HostAt c'.nmem A ztqg ∧
      ztzt ∧
      (∀ r, r ≠ 160027 → r ≠ 160028 → r ≠ 160030 → r ≠ 160015 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold proH
  exec_block
  all_goals try (config_simp; (try simp only [hA, h24, h29, h86]); omega)
  refine ⟨rfl, by_omega, ?_, ?_, ?_, ztolw, fun a ha => ?_,
    fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl⟩
  · simp_all
  · simp_all
  · simp_all
  · config_simp; simp only [hA, h24, Machine.upd_apply]; split_ifs <;> first | omega | simp [Host.whole]
  · have hi0 : ztfla := by zvohn at hi; omega
    zufpy
    zuiow

  · config_simp; simp only [hA, h24, Machine.upd_apply]; grind
  simp_all
end proofs
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Chazelle
@[expose] public section
noncomputable def leafShp (lam b a : ℕ) : List Shp :=
  (cover lam b a).map fun q => (q.2, 2 ^ q.1, gradeGran q.1)
theorem nd_map_of_lt {l : List ztw} {f : ℕ × ℕ → Shp} {k : ℕ} (hk : k < l.length) :
    nd (l.map f) k = f (l.getD k ztdr) := by
  unfold nd
  simp_all
theorem cover_getD_zero {lam b x : ℕ} (h : x < b) : ((cover lam b x).getD 0 ztdr).2 = x := by
  zuosd; rfl
theorem cover_getD_succ {lam b : ℕ} (x : ℕ) : ∀ k, k + 1 < (cover lam b x).length →
    ((cover lam b x).getD zts ztdr).2 =
      ((cover lam b x).getD k ztdr).2 + 2 ^ ((cover lam b x).getD k ztdr).1 := by
  induction x using cover_ind (b := b) with
  | h x ih =>
    zugf
    zubfn
    · rw [cover_of_lt hx] at hk ⊢
      zubhv
      · have hx' : x + 2 ^ nextG lam b x < b := by
          zukr
          zuhku
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        exact cover_getD_zero hx'
      grind
    · zuhku
theorem leafShp_length (lam b a : ℕ) : (leafShp lam b a).length = (cover lam b a).length := by
  simp [leafShp]
theorem leafShp_consec (lam b a : ℕ) : Consec ztfsz := by
  zugf
  zuedj

  rw [nd_map_of_lt hk, nd_map_of_lt by_omega]
  exact cover_getD_succ a k hk
variable {lam b a : ℕ}
theorem leafShp_first (h : a < b) : (nd ztfsz 0).1 = a := by
  have hl : 0 < (cover lam b a).length := by zuosd; simp
  unfold leafShp
  rw [nd_map_of_lt hl]
  exact cover_getD_zero h
theorem leafShp_sum (lam b a : ℕ) :
    ((leafShp lam b a).map fun x => x.2.1).sum = b - a := by
  rw [← cover_sum (lam := lam) (b := b) a, leafShp, List.map_map]; rfl

/-- **At least two leaves.** -/
theorem two_le_cover (_hl : 1 ≤ lam) (h : 2 ^ ztma < b - a) :
    2 ≤ (cover lam b a).length := by
  zukr
  have hab : ztmua := by_grind
  have hsum := cover_sum (lam := lam) (b := b) a
  rw [cover_of_lt hab] at hsum hc
  simp only [List.length_cons] at hc
  have h0 : (cover lam b (a + 2 ^ nextG lam b a)).length = 0 := by_omega
  rw [List.length_eq_zero_iff] at h0
  zvmzn at hsum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum
  have := Nat.pow_le_pow_right ztciz (nextG_le lam b a)
  omega

/-- The leaves' granularities are at most `γ'_{λ-1}` and at least `1`. -/
theorem leafShp_gran : ∀ k, k < (leafShp lam b a).length →
    (nd ztfsz k).2.2 ≤ gradeGran ztma ∧ 1 ≤ (nd ztfsz k).2.2 := by
  zugf
  zuedj

  zulqo
  have hq := mem_cover (lam := lam) (b := b) a ztxdd by_simp_all
  refine ⟨gradeGran_mono hq.1, ?_⟩
  exact le_trans (Nat.one_le_two_pow) (two_pow_ceilBeta_le_gradeGran _)
set_option maxHeartbeats 8000000 in
/-- **The leaves form a level.** -/
theorem leaves_levelAt {O : OracleIface} {P : Polygon} {m0 m5 m6 m8 : ℕ → ℕ}
    {A h lam a b : ℕ} (hR : Robust A m0 fun m' => GradeRaw O P m' h A) (hn : 2 ≤ P.n)
    (hlΛ : lam ≤ m0 h) (hl : 1 ≤ lam) (_hab : a < b) (hbn : b + 1 ≤ P.n)
    (h5 : ∀ x, x < A → m5 x = m0 x) (hhost : HostAt m5 A ztqg)
    (h6rec : ∀ k, k < (cover lam b a).length →
      RecAt m6 m5 ztgzq A (m0 zteu) ztxdd k)
    (h65 : ∀ x, x < A + 7 → m6 x = m5 x)
    (h8ent : ∀ k, k < (cover lam b a).length →
      m8 (A + 7 + 6 * (cover lam b a).length + 2 * k) = A + 7 + 6 * k ∧
      m8 (A + 7 + 6 * (cover lam b a).length + 2 * k + 1) = m6 (A + 7 + 6 * k + 5))
    (h86 : ∀ x, x < A + 7 + 6 * (cover lam b a).length → m8 x = m6 x) :
    LevelAt P m8 (A + 7 + 8 * (cover lam b a).length) (A + 7 + 6 * (cover lam b a).length) A
      ztfsz := by
  set j := (cover lam b a).length with hj
  zuc
  have hΛ : 1 ≤ m0 h := by_omega
  obtain ⟨-, -, h2, -, -, -, -, -, -, hent⟩ := tab_lt hR hn hΛ
  zumbr
  zugf
  zuedj

  zulqo
  have hmem0 : (cover lam b a).getD k ztdr ∈ cover lam b a := by
    grind
  set q := (cover lam b a).getD k ztdr with hq
  have hmem := mem_cover (lam := lam) (b := b) a q hmem0
  obtain ⟨hg, hdvd, hax, hxb⟩ := hmem
  set g := q.1 with hgdef
  set x := q.2 with hxdef
  obtain ⟨i, hi⟩ := hdvd
  zubtm
  have hxi : ztpqk := by rw [hi, Nat.mul_div_cancel_left _ hpos]
  have hgΛ : g < m0 h := by_omega
  have hic : ztsjc := by
    zulbt
    have : ztmvw := by
      grind
    have := (Nat.le_div_iff_mul_le hpos).mpr this
    omega
  obtain ⟨H, C, N, hd, hwf, hCP, -, -, hCs, hCm, hN, hc, -⟩ := hG.2.2.2 g i hgΛ hic
  obtain ⟨hT, hO, -, -⟩ := hent g i hgΛ hic
  have hCs' : C.s = x := by rw [hCs]; unfold gradeStart; grind
  have hCm' : ztsau := by
    rw [hCm]; unfold gradeLen
    have : x + 2 ^ g ≤ P.n - 1 := by_omega
    rw [hi] at this
    apply min_eq_left; rw [mul_comm]; omega
  set R := m0 ztzmy with hRdef
  set B := m0 ztqby with hBdef
  have hB5 : B + 5 ≤ A := hwf.1
  have hR3 : R + 3 * i + 1 < A := by_omega
  -- the record, read in `m0`
  obtain ⟨r0, rj, r5⟩ := h6rec k hk
  rw [← hq, hxi] at rj r5
  have e5 : m5 ztzmy = R := h5 _ hT
  have eR : m5 ztqby = B := h5 _ by_omega
  have eF : m5 zthcf = m0 zthcf := h5 _ hR3
  have hwords : ∀ t, 1 ≤ t → t ≤ 4 → m8 (A + 7 + 6 * k + t) = m0 ztnji := fun t t1 t4 => by
    rw [h86 _ by_omega, rj t t1 t4, e5, eR, h5 _ by_omega]
  have hd0 : m8 (A + 7 + 6 * k) = A := by rw [h86 _ by_omega, r0]
  have hf : m8 (A + 7 + 6 * j + 2 * k + 1) = m0 zthcf := by
    grind
  have h8m0 : ∀ y, y < A → m8 y = m0 y := fun y hy => by
    rw [h86 _ by_omega, h65 _ by_omega, h5 _ hy]
  refine ⟨C, hCs', hCm', ?_⟩
  rw [(h8ent k hk).1, hf]
  obtain ⟨-, -, d1, d2, d3, d4⟩ := hd
  refine ⟨ztcbl, hCP, hd0, by_omega, by_omega, by_omega, N,
    (hN.transport h8m0).mono by_omega, hc⟩
  · rw [hd0]
    exact hostAt_agree (A := A + 7) hhost rfl by_omega fun y hy => by
      rw [h86 _ by_omega, h65 _ by_omega]
  · zuody; have := poly_whole zta by_omega; grind
  · rw [hwords 1 le_rfl by_norm_num]; exact d1
  · rw [hwords 2 by_norm_num by_norm_num]; exact d2
  · rw [hwords 3 by_norm_num by_norm_num]; exact d3
  · rw [hwords 4 by_norm_num le_rfl]; exact d4
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs Chazelle Chazelle.Merge
@[expose] public section
macro "l41dec" : tactic => `(tactic| first | decide | omega)

/-- `160066 := 160015` (the base of the leaves' level array). -/
def baseB : Stmt := block [.copyN 160066 160015]

/-- The output: the NF of the single node. -/
def epiB : Stmt := block [.addN 160031 160066 160024, .loadN 160004 160031]

/-- The prologue: constants, table reads, `Gλ`, the host. -/
def l41A : Stmt := .seq proC (.seq proL (.seq clogS (.seq mulS proH)))

/-- The leaves: the cover, the base of the level array, the level array. -/
def l41B : Stmt := .seq coverS (.seq baseB l0S)

/-- **Lemma 4.1 on the RAM.** -/
def l41S (sM : Stmt) : Stmt := .seq l41A (.seq l41B (.seq ztwgw epiB))

/-- The chord bound of the leaves. -/
noncomputable def leafKb (lam a L : ℕ) : ℕ :=
  (((leafShp lam ztqy a).filter (leafP ztwsz)).map kb).sum

/-- **The step bound of Lemma 4.1** (before the cost bridge). -/
noncomputable def l41Big (κ F G H : ℕ → ℕ) (lam a L : ℕ) : ℕ :=
  40 * lam ^ 2 + 169 * lam + 84 + 11 * (cover lam ztqy a).length +
    Nat.clog 2 (cover lam ztqy a).length *
      (lvBound κ F G H ztcad ztwsz (cover lam ztqy a).length L
        ztdow + 2)
theorem bandOf_not_l41 {r : ℕ} (h : bandOf r ∉ l41Bands) :
    zteuy ∧ bandOf r ∉ mergeBands ∪ oracleBands := by
  unfold l41Bands at h
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at h
  zujfw
  have := h.2
  unfold bandOf bL41 at this
  omega
theorem okModel_chain {P : Polygon} (hG : GoodEnv P) (C : Chain) (hC : C.P = Qof P) :
    OkModel P ztc := by
  zuc
  have hn : ztgag := by have := hG.1.1; omega
  refine ⟨Host.whole P.n, C, by zuojy, by zvmxg; exact hostRegular_whole hn,
    ?_, ?_, rfl⟩
  · rw [hC]; have := poly_whole zta by_omega; simp_all
  · rw [hC]; exact (shearInvariance ztbhs P).1 hG.1
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 4000000 in
theorem baseB_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W baseB c c' k ∧ k = 1 ∧ WordsBounded W c' ∧
      c'.nreg 160066 = c.nreg 160015 ∧ (∀ r, r ≠ 160066 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold baseB
  exec_block
  simp_all
set_option maxHeartbeats 4000000 in
theorem epiB_exec (hw : WordsBounded W c) {B : ℕ} (h66 : c.nreg 160066 = B)
    (h24 : c.nreg 160024 = 1) (hW : B + 1 ≤ W) :
    ∃ c' k, Exec P W epiB c c' k ∧ k = 2 ∧ WordsBounded W c' ∧
      c'.nreg 160004 = c.nmem ztvf ∧
      (∀ r, r ≠ 160004 → r ≠ 160031 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold epiB
  exec_block
  all_goals try (config_simp; (try simp only [h66, h24]); omega)
  simp_all
end proofs
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs Chazelle Chazelle.Merge
@[expose] public section
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
/-- **The prologue on the RAM.** -/
theorem l41A_exec {O : OracleIface} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    {c : Config} (hw : WordsBounded W c) {A h a L lam : ℕ}
    (hA : c.nreg ALLOC = A) (r0 : c.nreg 160000 = h) (r1 : c.nreg 160001 = a)
    (r2 : c.nreg 160002 = L) (r3 : c.nreg 160003 = lam)
    (hR : Robust A c.nmem fun m' => GradeRaw O P m' h A) (hlΛ : lam ≤ c.nmem h) (h7 : 7 ≤ lam)
    (han : a + L + 1 ≤ P.n) (hL1 : 2 ^ ztma < L) (_hL2 : L ≤ 2 ^ lam)
    (hbud : A + 20 * lam + 100 ≤ W) :
    ∃ c5 k, Exec P W l41A c c5 k ∧ k ≤ 9 * lam + 70 ∧ 9 ≤ k ∧ WordsBounded W c5 ∧
      c5.nreg ALLOC = A + 7 ∧ HostAt c5.nmem A ztqg ∧
      (∀ x, x < A → c5.nmem x = c.nmem x) ∧ c5.rreg = c.rreg ∧ c5.rmem = c.rmem ∧
      c5.output = c.output ∧
      (∀ r, zteuy → r ≠ ALLOC → c5.nreg r = c.nreg r) ∧
      c5.nreg 160000 = h ∧ c5.nreg 160010 = a ∧ c5.nreg 160011 = a + L ∧
      c5.nreg 160014 = 0 ∧ c5.nreg 160015 = A + 7 ∧ c5.nreg 160020 = c.nmem ztbba ∧
      c5.nreg 160021 = c.nmem ztgn + 2 ∧ c5.nreg 160022 = c.nmem zteu ∧
      c5.nreg 160024 = 1 ∧ c5.nreg 160026 = lam ∧ c5.nreg 160027 = A ∧
      c5.nreg 160032 = gradeGran lam ∧ c5.nreg 160033 = gradeGran ztma ∧
      c5.nreg 160080 = 2 ∧ c5.nreg 160081 = 5 ∧ c5.nreg 160082 = 6 ∧ c5.nreg 160083 = 3 ∧
      c5.nreg 160084 = 4 ∧ c5.nreg 160087 = 8 := by
  zuk
  zubnx

  have hΛtg : c.nmem h ≤ topGrade P.n + 1 := hRaw.1
  zups

  zvojf at tS0 tS1 tS1lt tpow
  zvncs at tent
  have hltg : ztrgu := by_omega
  have hcb : ztuki := Cost.ceilBeta_le lam
  have hpowl := tpow lam hltg
  have hpowcb := tpow (Cost.ceilBeta lam) by_omega
  obtain ⟨e0T, e0O, e0G, e0G'⟩ := tent ztma 0 by_omega ztqat
  simp only [Nat.mul_zero, Nat.add_zero] at e0O e0G e0G'
  have eTl : T + lam - 1 = T + ztma := by_omega
  zucvv
  have hGl : 2 ^ Cost.ceilBeta lam + lam * (Nat.clog 2 lam + 2) = gradeGran lam := by
    zulun
  have hcl : ztscd := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hpl : 2 ^ ztma ≤ 2 ^ lam := Nat.pow_le_pow_right by_norm_num by_omega
  clear tent thalf
  -- 1. constants
  obtain ⟨c1, k1, e1, hk1, hw1, q24, q80, q81, q82, q83, q84, q86, q87, q29, fr1, hm1, hrr1,
    hrm1, ho1⟩ := proC_exec (P := P) hw by_omega
  -- 2. the table reads
  obtain ⟨c2, k2, e2, hk2, hw2, p10, p11, p26, p20, p101, p21, p22, p33, p102, p103, p32, p14, fr2,
      hm2, hrr2, hrm2, ho2⟩ :=
    proL_exec (P := P) hw1 (h := h) (a := a) (L := L) (lam := lam)
      by_grind by_grind
      by_grind by_grind
      q24 q80 q83 q84 by_omega
      by_omega by_omega by_grind by_grind
      by_grind by_grind
      by_grind by_grind
  zvmxz at p20; rw [hm1, hS] at p21; zvmxz at p22
  rw [hm1, hT, eTl, e0G] at p33
  rw [hm1, hS, tS1, hpowl.2.1, hpowcb.1] at p32
  zvmxz at hm2
  have c2r : ∀ r, ¬ ProRG r → c2.nreg r = c1.nreg r := fr2
  have c2_03 : ztupf := by
    rw [c2r _ ztggm, fr1 _ ztbuo]; exact r3
  have c2_24 : ztizc := by rw [c2r _ ztggm]; omega
  -- 3. ⌈log₂ λ⌉
  obtain ⟨c3, k3, e3, hk3, hw3, s04, fr3, hm3, hrr3, hrm3, ho3⟩ :=
    clogS_exec (P := P) hw2 p21 c2_03 c2_24
      ztbmx by_omega by_omega
  -- 4. Gλ
  obtain ⟨c4, k4, e4, hk4, hw4, s32, fr4, hm4, hrr4, hrm4, ho4⟩ :=
    mulS_exec (P := P) hw3 (lam := lam) (cl := Nat.clog 2 lam) (G2 := 2 ^ Cost.ceilBeta lam)
      s04 ztepv
      ztepv
      ztepv
      (by rw [fr3 _ by_decide by_decide by_decide, c2r _ ztggm];
          omega)
      by_omega
  rw [hGl] at s32
  have c42 : ∀ r, r ≠ 160032 → r ≠ 160106 → r ≠ 160107 → r ≠ 160108 → r ≠ 160104 →
      r ≠ 160105 → r ≠ 160031 → c4.nreg r = c2.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 => by
    rw [fr4 r a1 a2 a3 a4, fr3 r a5 a6 a7]
  have c41 : ∀ r, ¬ ProRG r → r ≠ 160104 → r ≠ 160105 → r ≠ 160106 → r ≠ 160107 →
      r ≠ 160108 → c4.nreg r = c1.nreg r := fun r a1 a2 a3 a4 a5 a6 => by
    unfold ProRG at a1
    rw [c42 r by_omega a4 a5 a6 a2 a3 by_omega]
    exact c2r r (by unfold ProRG; exact a1)
  -- 5. the host
  have c4A : c4.nreg ALLOC = A := by
    rw [c41 _ (by rw [hAl]; unfold ProRG; decide) by_omega by_omega
      by_omega by_omega by_omega,
      fr1 _ ztec]; exact hA
  have c4c : ∀ r, 160024 ≤ r → r ≤ 160029 ∨ ztneq → r ≠ 160026 →
      r ≠ 160025 → c4.nreg r = c1.nreg r := fun r a1 a2 a3 a4 =>
    c41 r ztqgf by_omega by_omega by_omega by_omega by_omega
  obtain ⟨c5, k5, e5, hk5, hw5, h5A, h527, h515, hhost, hm54, fr5, hrr5, hrm5, ho5⟩ :=
    proH_exec (P := P) hw4 c4A
      ztecb
      ztecb
      ztecb by_omega
      by_omega by_omega
  have c52 : ∀ r, r ≠ 160032 → r ≠ 160106 → r ≠ 160107 → r ≠ 160108 → r ≠ 160104 →
      r ≠ 160105 → r ≠ 160031 → r ≠ 160027 → r ≠ 160028 → r ≠ 160030 → r ≠ 160015 →
      r ≠ ALLOC → c5.nreg r = c2.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 => by
    rw [fr5 r a8 a9 a10 a11 a12]; exact c42 r a1 a2 a3 a4 a5 a6 a7
  have c5c : ∀ r, 160024 ≤ r → r ≤ 160029 ∨ ztneq → r ≠ 160026 →
      r ≠ 160025 → r ≠ 160027 → r ≠ 160028 → c5.nreg r = c1.nreg r := fun r a1 a2 a3 a4 a5 a6 => by
    rw [fr5 r a5 a6 by_omega by_omega by_omega]; exact c4c r a1 a2 a3 a4
  have p52 : ∀ r, (r = 160010 ∨ r = 160011 ∨ r = 160014 ∨ r = 160020 ∨ r = 160021 ∨
      r = 160022 ∨ r = 160026 ∨ r = 160033) → c5.nreg r = c2.nreg r := fun r hr =>
    c52 r by_omega by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega by_omega by_omega by_omega
  refine ⟨c5, k1 + ztvs, .seq e1 ztbxo, by_omega,
    by omega, hw5, h5A, hhost, fun x hx => by rw [hm54 x zthrs, hm4, hm3, hm2],
    by zunlr, by zunls,
    by zunlt, fun r hr hra => ?_, ?_, by zumzt; omega,
    by zumzt; omega, by zumzt; omega, h515,
    by zumzt; omega, by rw [p52 _ by_decide, p21, hS],
    by zumzt; omega,
    by zumxr; omega,
    by zumzt; omega, h527,
    by rw [fr5 _ by_decide by_decide by_decide by_decide by_omega]; omega,
    by zumzt; omega,
    by zumxr; omega,
    by zumxr; omega,
    by zumxr; omega,
    by zumxr; omega,
    by zumxr; omega,
    by zumxr; omega⟩
  · rw [fr5 r by_omega by_omega by_omega by_omega hra,
      c41 r ztqgf by_omega by_omega by_omega by_omega by_omega]
    exact fr1 r by_omega
  · rw [c52 _ by_decide by_decide by_decide by_decide by_decide by_decide by_decide
      by_decide by_decide by_decide by_decide by_omega,
      c2r _ ztggm, fr1 _ ztbuo]
    exact r0
end proofs
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs Chazelle Chazelle.Merge
@[expose] public section
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
/-- **The leaves on the RAM.** -/
theorem l41B_exec {O : OracleIface} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    {c c5 : Config} (hw5 : WordsBounded W c5) {A h a L lam : ℕ}
    (hR : Robust A c.nmem fun m' => GradeRaw O P m' h A) (hlΛ : lam ≤ c.nmem h) (h7 : 7 ≤ lam)
    (han : a + L + 1 ≤ P.n) (hL1 : 2 ^ ztma < L) (hL2 : L ≤ 2 ^ lam)
    (m5c : ∀ x, x < A → c5.nmem x = c.nmem x) (hhost : HostAt c5.nmem A ztqg)
    (h5A : c5.nreg ALLOC = A + 7) (s10 : c5.nreg 160010 = a) (s11 : c5.nreg 160011 = a + L)
    (s14 : c5.nreg 160014 = 0) (s15 : c5.nreg 160015 = A + 7)
    (s20 : c5.nreg 160020 = c.nmem ztbba) (s21 : c5.nreg 160021 = c.nmem ztgn + 2)
    (s22 : c5.nreg 160022 = c.nmem zteu) (s24 : c5.nreg 160024 = 1)
    (s26 : c5.nreg 160026 = lam) (s27 : c5.nreg 160027 = A) (s81 : c5.nreg 160081 = 5)
    (s82 : c5.nreg 160082 = 6) (s87 : c5.nreg 160087 = 8)
    (hbud : A + 40 * lam ^ 2 + 160 * lam + 11 * (cover lam ztqy a).length + 30 ≤ W) :
    ∃ c8 k, Exec P W l41B c5 c8 k ∧
      k ≤ 40 * lam ^ 2 + 160 * lam + 11 * (cover lam ztqy a).length + 10 ∧
      WordsBounded W c8 ∧ c8.nreg ALLOC = A + 7 + 8 * (cover lam ztqy a).length ∧
      c8.nreg ALLOC ≤ A + 7 + k ∧
      LevelAt P c8.nmem (A + 7 + 8 * (cover lam ztqy a).length)
        (A + 7 + 6 * (cover lam ztqy a).length) A ztwyd ∧
      (∀ x, x < A → c8.nmem x = c.nmem x) ∧
      c8.nreg 160014 = (cover lam ztqy a).length ∧
      c8.nreg 160066 = A + 7 + 6 * (cover lam ztqy a).length ∧
      (∀ r, ¬ CovRG r → ¬ L0RG r → r ≠ 160066 → r ≠ ALLOC → c8.nreg r = c5.nreg r) ∧
      c8.rreg = c5.rreg ∧ c8.rmem = c5.rmem ∧ c8.output = c5.output := by
  zuk
  zubnx

  zups

  obtain ⟨D, hD⟩ : ∃ D, c.nmem (h + 3) = D := zths
  zvojf at tS0 tS1 tS1lt tpow s21
  rw [hD] at thalf s20
  zvncs at tent s22
  have hltg : ztrgu := by have := hRaw.1; omega
  have hpl : 2 ^ lam = 2 * 2 ^ ztma := by rw [← pow_succ']; grind
  zuhyu
  have hsq : 40 * lam ^ 2 + 160 * lam = ztelf * ztnff := by_ring
  -- 6. the cover
  have hCR : CovRegs c5 lam ztqy D ztenx T A := ⟨s11, s26, s24, s20, s21, s22, s27⟩
  have hent5 : ∀ g, g ≤ lam - 1 → ∀ i, ztg * 2 ^ g ≤ a + L →
      c5.nmem ztbps + 3 * i + 1 < A + 7 ∧ c5.nmem (c5.nmem ztbps + 3 * i) + 4 < A + 7 := by
    intro g hg i hi
    have hgΛ : g < c.nmem h := by_omega
    zubtm
    have hic : ztsjc := by
      zulbt
      have : ztmvw := by
        grind
      have := (Nat.le_div_iff_mul_le hpos).mpr this
      omega
    obtain ⟨eT, eO, -, -⟩ := tent g i hgΛ hic
    obtain ⟨-, -, -, -, hwf, -⟩ := hRaw.2.2.2 g i hgΛ hic
    zvncs at hwf
    have := hwf.1
    rw [m5c _ eT, m5c _ by_omega]
    omega
  have hCT : CovTab c5.nmem lam ztqy D ztenx T ztgzq W :=
    ⟨fun y hy => by rw [m5c _ (thalf y by_omega).2]; exact (thalf y by_omega).1,
      fun i hi => by
        rw [m5c _ (tpow i by_omega).2.2.1]
        exact (tpow i by_omega).1,
      by have := (thalf ztqy by_omega).2; omega,
      by have := (tpow lam hltg).2.2.1; omega,
      by have := (tent ztma 0 by_omega ztqat).1; omega, hent5,
      by omega, by_nlinarith⟩
  obtain ⟨c6, k6, e6, hk6, hw6, h614, h615, hrec, hm65, fr6, hrr6, hrm6, ho6⟩ :=
    coverS_exec (P := P) hw5 hCR hCT by_omega s10 by_omega by_omega s14 s15
  zufpg
  -- 7. the base of the leaves
  obtain ⟨c7, k7, e7, hk7, hw7, b66, fr7, hm7, hrr7, hrm7, ho7⟩ := baseB_exec (P := P) hw6
  have c75 : ∀ r, r ≠ 160066 → ¬ CovRG r → c7.nreg r = c5.nreg r := fun r a1 a2 => by
    rw [fr7 r a1, fr6 r a2]
  have c7A : c7.nreg ALLOC = A + 7 := by
    rw [c75 _ by_omega (by rw [hAl]; unfold CovRG AscRG; decide)]; omega
  -- 8. the level array of the leaves
  obtain ⟨c8, k8, e8, hk8, hw8, h8A, h8Ak, hent8, hm87, fr8, hrr8, hrm8, ho8⟩ :=
    l0S_exec (P := P) hw7 c7A ztlhb
      ztlhb
      ztbsi
      ztbsi
      ztbsi
      ztbsi
      by_nlinarith
  have m65 : ∀ x, x < A + 7 → c6.nmem x = c5.nmem x := fun x hx => hm65 x zthrs
  have m86 : ∀ x, x < A + 7 + 6 * j → c8.nmem x = c6.nmem x := fun x hx => by
    rw [hm87 x zthrs, hm7]
  have hLev : LevelAt P c8.nmem (A + 7 + 8 * j) (A + 7 + 6 * j) A ztwyd :=
    leaves_levelAt hR by_omega hlΛ by_omega by_omega by_omega
      (fun x hx => m5c x hx) hhost (by zvncs; omega) m65
      (fun k hk => by
        obtain ⟨u1, u2⟩ := hent8 k hk
        exact ⟨u1, by rw [u2, hm7]⟩)
      m86
  refine ⟨c8, k6 + zttqm, .seq e6 (.seq e7 e8), by_nlinarith, hw8, h8A, by_omega, hLev,
    fun x hx => by rw [m86 x by_omega, m65 x by_omega, m5c x hx], ?_, ?_,
    fun r a1 a2 a3 a4 => by rw [fr8 r a2 a4]; exact c75 r a3 a1, by rw [hrr8, hrr7, hrr6],
    by rw [hrm8, hrm7, hrm6], by rw [ho8, ho7, ho6]⟩
  · rw [fr8 _ ztqfz by_omega, fr7 _ by_decide]; omega
  · rw [fr8 _ ztqfz by_omega, b66]; omega
