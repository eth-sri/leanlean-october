module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRMgB
public import Chazelle.Core.DownPhaseDrvRInv

/-!
# Down-phase driver (RAM side): merges on a region host, one merge step

`mgStep sM`: the top of the union (`mgTop`), its model descriptor at the allocator (`mgDesc`,
six words: `0`, host handle, start `0`, `m₁ + m₂`, top index, bit), the arguments of the merge
(`mgArgs`), the merge `sM` (`MergeSpec`), and the new accumulated chain (`mgOut`):
`mgStep_exec`.

Registers (band `bDownDrv`): `219103` the degree cap `D`, `219104` the context handle,
`219110 … 219113` the accumulated chain (descriptor, normal form, edges, granularity),
`219114 … 219116` the next piece (descriptor, normal form, edges).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs BuildRam SignK L41 Chazelle Chazelle.Merge

@[expose] public section

/-- The model descriptor of the union at the allocator. -/
def mgDesc : Stmt :=
  block [.copyN 219137 9999, .storeN 9999 219140,
    .addN 219126 219137 219141, .storeN 219126 219100,
    .addN 219126 219126 219141, .storeN 219126 219140,
    .addN 219126 219126 219141, .addN 219127 219112 219116, .storeN 219126 219127,
    .addN 219126 219126 219141, .storeN 219126 219138,
    .addN 219126 219126 219141, .storeN 219126 219139,
    .addN 9999 9999 219146]

/-- The arguments of the merge. -/
def mgArgs : Stmt :=
  block [.addN 100000 219110 219141, .addN 100001 219114 219141, .addN 100002 219137 219141,
    .copyN 100003 219111, .copyN 100004 219115, .copyN 100005 219113, .addN 100006 219113 219141,
    .copyN 100007 219103, .copyN 100009 219104]

/-- The accumulated chain after the merge. -/
def mgOut : Stmt :=
  block [.copyN 219110 219137, .copyN 219111 100008, .addN 219112 219112 219116,
    .addN 219113 219113 219141]

/-- **One merge step.** -/
def mgStep (sM : Stmt) : Stmt := .seq mgTop (.seq mgDesc (.seq mgArgs (.seq sM mgOut)))

/-- The cost of the merge of one step: degree cap `D`, chord counts `x, y` of the parts, their
granularity bound `γ`, the length `M` of the union. -/
def mgCostV (κ F G H : ℕ → ℕ) (D x y γ M : ℕ) : ℕ :=
  κ D * (x + y + 1) * F (γ + fuseLoss) * G (γ + fuseLoss) *
    (H (γ + fuseLoss) + Nat.clog 2 (M + 1) + 1)

/-- The bands of a merge step. -/
def mgBands : Finset ℕ := insert bDownDrv (mergeBands ∪ oracleBands)

theorem mgBands_subset : mgBands ⊆ drvBands := ⌖

/-- The registers `mgDesc` writes. -/
def Bdesc (r : ℕ) : Bool := decide (r = 219126 ∨ r = 219127 ∨ r = 219137 ∨ r = 9999)

theorem wrM_mgDesc : wrM Bdesc mgDesc = true := ⌖

/-- The registers `mgArgs` writes. -/
def Bargs (r : ℕ) : Bool := decide (100000 ≤ r ∧ r ≤ 100009)

theorem wr_mgArgs : wr Bargs mgArgs = true := ⌖

/-- The registers `mgOut` writes. -/
def Bout (r : ℕ) : Bool := decide (219110 ≤ r ∧ r ≤ 219113)

theorem wr_mgOut : wr Bout mgOut = true := ⌖

section exec

variable {P : Polygon} {W : ℕ}

theorem mgDesc_exec (c : Config) (hw : WordsBounded W c) {A HB ma mp : ℕ}
    (a40 : c.nreg 219140 = 0) (a41 : c.nreg 219141 = 1) (a46 : c.nreg 219146 = 6)
    (a00 : c.nreg 219100 = HB) (a12 : c.nreg 219112 = ma) (a16 : c.nreg 219116 = mp)
    (aA : c.nreg 9999 = A) (hAW : A + 6 ≤ W) (hmp : ma + mp ≤ W) :
    ∃ c' k, Exec P W mgDesc c c' k ∧ k = 14 ∧ c'.nreg 219137 = A ∧ c'.nreg 9999 = A + 6 ∧
      c'.nmem A = 0 ∧ c'.nmem (A + 1) = HB ∧ c'.nmem (A + 2) = 0 ∧
      c'.nmem (A + 3) = ma + mp ∧ c'.nmem (A + 4) = c.nreg 219138 ∧
      c'.nmem (A + 5) = c.nreg 219139 ∧ (∀ a, a < A → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have aT := hw.1 219138
  have aB := hw.1 219139
  unfold mgDesc
  exec_block
  all_goals try (config_simp; (try simp only [a40, a41, a46, a00, a12, a16, aA]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · config_simp; ϴ aA
  · config_simp; ϴ aA, a46
  · config_simp; simp only [aA, a41, a40, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [aA, a41, a40, a00, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [aA, a41, a40, a00, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [aA, a41, a40, a00, a12, a16, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [aA, a41, a40, a00, a12, a16, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [aA, a41, a40, a00, a12, a16, Machine.upd_apply]; split_ifs <;> omega
  · intro a ha; config_simp; ϴ aA, a41, Machine.upd_apply
    split_ifs <;> first | rfl | omega
  · config_simp
  · config_simp
  · config_simp

theorem mgArgs_exec (c : Config) (hw : WordsBounded W c) {D1 D2 A f1 f2 γ D g : ℕ}
    (b10 : c.nreg 219110 = D1) (b14 : c.nreg 219114 = D2) (b37 : c.nreg 219137 = A)
    (b11 : c.nreg 219111 = f1) (b15 : c.nreg 219115 = f2) (b13 : c.nreg 219113 = γ)
    (b03 : c.nreg 219103 = D) (b04 : c.nreg 219104 = g) (b41 : c.nreg 219141 = 1)
    (h1 : D1 + 1 ≤ W) (h2 : D2 + 1 ≤ W) (h3 : A + 1 ≤ W) (h4 : γ + 1 ≤ W) :
    ∃ c' k, Exec P W mgArgs c c' k ∧ k = 9 ∧
      c'.nreg 100000 = D1 + 1 ∧ c'.nreg 100001 = D2 + 1 ∧ c'.nreg 100002 = A + 1 ∧
      c'.nreg 100003 = f1 ∧ c'.nreg 100004 = f2 ∧ c'.nreg 100005 = γ ∧
      c'.nreg 100006 = γ + 1 ∧ c'.nreg 100007 = D ∧ c'.nreg 100009 = g ∧ c'.nmem = c.nmem := by
  unfold mgArgs
  exec_block
  all_goals try (config_simp; (try simp only [b10, b14, b37, b11, b15, b13, b03, b04, b41]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
    (try simp only [b10, b14, b37, b11, b15, b13, b03, b04, b41])

theorem mgOut_exec (c : Config) (hw : WordsBounded W c) {A ma mp γ : ℕ}
    (b37 : c.nreg 219137 = A) (b12 : c.nreg 219112 = ma) (b16 : c.nreg 219116 = mp)
    (b13 : c.nreg 219113 = γ) (b41 : c.nreg 219141 = 1) (h1 : ma + mp ≤ W) (h2 : γ + 1 ≤ W) :
    ∃ c' k, Exec P W mgOut c c' k ∧ k = 4 ∧ c'.nreg 219110 = A ∧
      c'.nreg 219111 = c.nreg 100008 ∧ c'.nreg 219112 = ma + mp ∧ c'.nreg 219113 = γ + 1 := by
  unfold mgOut
  exec_block
  all_goals try (config_simp; (try simp only [b37, b12, b16, b13, b41]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> (try simp only [b37, b12, b16, b13, b41])


/-- **One merge step**: the union of the accumulated chain `C₁ = ⟨H.poly Q, 0, m₁⟩` (descriptor
at `r219110 + 1`, normal form at `r219111`, granularity `≤ r219113`) and the next piece `C₂`
(at `r219114 + 1`, `r219115`, `r219116` edges): a model descriptor of the union at the
allocator, its `(γ + 1)`-canonical normal form, written back into `219110 … 219113`. -/
theorem mgStep_exec {sM : Stmt} {κ F G Hf : ℕ → ℕ} {X : MemCtx}
    (hM : MergeMeets sM κ F G Hf X OkModel) (hXc : X.CapLocal)
    (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config) (hw : WordsBounded W c)
    (hK : MgConst c) {H : Host} {HB NP D g γ ma mp γ1 γ2 : ℕ} {C1 C2 : Chain} {N1 N2 : NF}
    (h00 : c.nreg 219100 = HB) (h01 : c.nreg 219101 = NP) (h03 : c.nreg 219103 = D)
    (h04 : c.nreg 219104 = g) (h07 : c.nreg 219107 = H.length)
    (h12 : c.nreg 219112 = ma) (h13 : c.nreg 219113 = γ) (h16 : c.nreg 219116 = mp)
    (hHA : Robust (c.nreg ALLOC) c.nmem (fun m => HostAt m HB H))
    (hHok : H.length ≤ 64) (hwf : HostWF P.n H) (hreg : HostRegular (Qof P).n H)
    (hsimp : (H.poly (Qof P)).Simple) (hHB : HB + 3 * H.length + 4 ≤ c.nreg ALLOC)
    (hNP : NP = (H.pts P.n).length)
    (hd1 : Robust (c.nreg ALLOC) c.nmem
      (fun m => m (c.nreg 219110 + 1) = HB ∧ ChainDescAt m (c.nreg 219110 + 1) (Qof P) H C1))
    (hd2 : Robust (c.nreg ALLOC) c.nmem
      (fun m => m (c.nreg 219114 + 1) = HB ∧ ChainDescAt m (c.nreg 219114 + 1) (Qof P) H C2))
    (hd1A : c.nreg 219110 + 6 ≤ c.nreg ALLOC) (hd2A : c.nreg 219114 + 6 ≤ c.nreg ALLOC)
    (hs1 : C1.s = 0) (hm1 : C1.m = ma) (hs2 : C2.s = ma) (hm2 : C2.m = mp)
    (hlen : C1.m + C2.m + 1 ≤ C1.P.n)
    (hN1 : NFWithin c.nmem (c.nreg 219111) (c.nreg ALLOC) N1)
    (hN2 : NFWithin c.nmem (c.nreg 219115) (c.nreg ALLOC) N2)
    (hc1 : IsCanonicalNF (chainModel C1) (Qof P) N1 γ1 D)
    (hc2 : IsCanonicalNF (chainModel C2) (Qof P) N2 γ2 D) (hγ1 : γ1 ≤ γ) (hγ2 : γ2 ≤ γ)
    (hgen : SharedGeneric (jOf C1 C2 hlen))
    (hfd : (chainModel (jOf C1 C2 hlen).whole).FullDegLe (Qof P) D) (hD : 4 ≤ D)
    (hX : X.holds P c.nmem g (c.nreg ALLOC)) (hcap : γ + fuseLoss ≤ X.cap P c.nmem g)
    (hγW : γ + 1 ≤ W)
    (hroom : c.nreg ALLOC + 6 +
      mgCostV κ F G Hf D N1.chords.length N2.chords.length γ (ma + mp) ≤ W) :
    ∃ c' k, Exec P W (mgStep sM) c c' k ∧
      k ≤ 60 * H.length + 360 + mgCostV κ F G Hf D N1.chords.length N2.chords.length γ (ma + mp) ∧
      c'.nreg 219110 = c.nreg ALLOC ∧ c.nreg ALLOC + 6 ≤ c'.nreg 219111 ∧
      c'.nreg 219112 = ma + mp ∧ c'.nreg 219113 = γ + 1 ∧ c.nreg ALLOC + 6 ≤ c'.nreg ALLOC ∧
      Robust (c'.nreg ALLOC) c'.nmem (fun m => m (c.nreg ALLOC) = 0 ∧
        m (c.nreg ALLOC + 1) = HB ∧
        ChainDescAt m (c.nreg ALLOC + 1) (Qof P) H (jOf C1 C2 hlen).whole) ∧
      ModelDescWF P (c'.nreg ALLOC) c'.nmem (c.nreg ALLOC) ∧
      (∃ N, NFWithin c'.nmem (c'.nreg 219111) (c'.nreg ALLOC) N ∧
        IsCanonicalNF (chainModel (jOf C1 C2 hlen).whole) (Qof P) N (γ + 1) D) ∧
      (∀ q, bandOf q = bDownDrv → (q < 219110 ∨ (219113 < q ∧ q < 219120) ∨ 219139 < q) →
        c'.nreg q = c.nreg q) ∧
      Frame mgBands c c' k := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hhw : hostWords P.n = 256 * P.n + 16 := rfl
  have hfl : fuseLoss = 1 := rfl
  set A₀ := c.nreg ALLOC with hA₀
  set D1 := c.nreg 219110 with hD1
  set D2 := c.nreg 219114 with hD2
  set f1 := c.nreg 219111 with hf1
  set f2 := c.nreg 219115 with hf2
  have hP1 := hd1.holds.2.2.1
  have hP2 := hd2.holds.2.2.1
  have hC1n : C1.P.n = NP := by rw [hP1, DownMath.host_poly_n, hQn, hNP]
  have hlen' : ma + C2.m + 1 ≤ NP := by rw [← hC1n, ← hm1]; exact hlen
  have hNW : NP ≤ 64 * P.n := by
    have h1 := Host.pts_length_le hwf
    have h2 : H.length * P.n ≤ 64 * P.n := Nat.mul_le_mul_right _ hHok
    rw [hNP]; omega
  have hAW : A₀ + 6 ≤ W := by omega
  -- the top of the union
  obtain ⟨c₁, k₁, e₁, hk₁, t38, t39, g₁⟩ := mgTop_exec hG hWn c hw hK h00 h01 h07 h12 hHA.holds
    hwf hHok (by omega) hNP hd1.holds.2 hd2.holds.2 hs1 hm1 hs2 hlen' (by omega) (by omega)
  have hw₁ := e₁.wb_right
  have u := g₁.1
  have hm₁ := g₁.2.2.1
  -- the descriptor of the union
  have a40 : c₁.nreg 219140 = 0 := by rw [u _ (by decide), hK.r40]
  have a41 : c₁.nreg 219141 = 1 := by rw [u _ (by decide), hK.r41]
  have a46 : c₁.nreg 219146 = 6 := by rw [u _ (by decide), hK.r46]
  have a00 : c₁.nreg 219100 = HB := by rw [u _ (by decide), h00]
  have a12 : c₁.nreg 219112 = ma := by rw [u _ (by decide), h12]
  have a16 : c₁.nreg 219116 = mp := by rw [u _ (by decide), h16]
  have aA : c₁.nreg 9999 = A₀ := by rw [u _ (by decide)]; rfl
  obtain ⟨c₂, k₂, e₂, hk₂, d37, dA, w0, w1, w2, w3, w4, w5, wlt, drr, drm, dout⟩ :=
    mgDesc_exec (P := P) c₁ hw₁ a40 a41 a46 a00 a12 a16 aA hAW (by omega)
  have hw₂ := e₂.wb_right
  have g₂ : FrameM Bdesc c₁ c₂ := exec_frameM e₂ wrM_mgDesc
  have v : ∀ r, Btop r = false → Bdesc r = false → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    (g₂.1 r h2).trans (u r h1)
  have hag : ∀ a, a < A₀ → c₂.nmem a = c.nmem a := fun a ha => by rw [wlt a ha, hm₁]
  -- the union's descriptor, robustly
  have hP21 : C2.P = C1.P := hP2.trans hP1.symm
  have hcons : C2.s = C1.s + C1.m := by rw [hs2, hs1, hm1]; ring
  have hΦ : ∀ m' : ℕ → ℕ, (∀ a, a < A₀ + 6 → m' a = c₂.nmem a) →
      m' A₀ = 0 ∧ m' (A₀ + 1) = HB ∧
      ChainDescAt m' (A₀ + 1) (Qof P) H (jOf C1 C2 hlen).whole := by
    intro m' hm'
    have ag : ∀ a, a < A₀ → m' a = c.nmem a := fun a ha =>
      (hm' a (by omega)).trans (hag a ha)
    obtain ⟨b1h, b1⟩ := hd1 m' ag
    obtain ⟨b2h, b2⟩ := hd2 m' ag
    refine ⟨by rw [hm' _ (by omega)]; exact w0, by rw [hm' _ (by omega)]; exact w1, ?_⟩
    refine descWhole hlen hP21 hcons b1 b2 ?_ ?_ ?_ ?_ ?_
    · rw [hm' _ (by omega), w1, b1h]
    · rw [show A₀ + 1 + 1 = A₀ + 2 by omega, hm' _ (by omega), w2, hs1]
    · rw [show A₀ + 1 + 2 = A₀ + 3 by omega, hm' _ (by omega), w3, hm1, hm2]
    · rw [show A₀ + 1 + 3 = A₀ + 4 by omega, hm' _ (by omega), w4, t38]
    · rw [show A₀ + 1 + 4 = A₀ + 5 by omega, hm' _ (by omega), w5, t39,
        show D1 + 1 + 4 = D1 + 5 by omega, show D2 + 1 + 4 = D2 + 5 by omega,
        ag _ (by omega), ag _ (by omega)]
  have hTD := hΦ c₂.nmem (fun _ _ => rfl)
  -- the arguments
  have b10 : c₂.nreg 219110 = D1 := v _ (by decide) (by decide)
  have b14 : c₂.nreg 219114 = D2 := v _ (by decide) (by decide)
  have b11 : c₂.nreg 219111 = f1 := v _ (by decide) (by decide)
  have b15 : c₂.nreg 219115 = f2 := v _ (by decide) (by decide)
  have b13 : c₂.nreg 219113 = γ := by rw [v _ (by decide) (by decide), h13]
  have b03 : c₂.nreg 219103 = D := by rw [v _ (by decide) (by decide), h03]
  have b04 : c₂.nreg 219104 = g := by rw [v _ (by decide) (by decide), h04]
  have b41 : c₂.nreg 219141 = 1 := by rw [v _ (by decide) (by decide), hK.r41]
  obtain ⟨c₃, k₃, e₃, hk₃, r0, r1, r2, r3, r4, r5, r6, r7, r9, m₃⟩ :=
    mgArgs_exec (P := P) c₂ hw₂ b10 b14 d37 b11 b15 b13 b03 b04 b41 (by omega) (by omega)
      (by omega) hγW
  have hw₃ := e₃.wb_right
  have g₃ : FrameB Bargs c₂ c₃ := exec_frameB e₃ wr_mgArgs
  have A3 : c₃.nreg ALLOC = A₀ + 6 := by rw [g₃.1 _ (by decide)]; exact dA
  have ag₃ : ∀ a, a < A₀ → c₃.nmem a = c.nmem a := fun a ha => by rw [m₃]; exact hag a ha
  have hHA₃ : HostAt c₃.nmem HB H := hHA c₃.nmem ag₃
  obtain ⟨b1h, b1⟩ := hd1 c₃.nmem ag₃
  obtain ⟨b2h, b2⟩ := hd2 c₃.nmem ag₃
  have hN1₃ : NFWithin c₃.nmem f1 (c₃.nreg ALLOC) N1 := by
    rw [A3]; exact (hN1.transport ag₃).mono (by omega)
  have hN2₃ : NFWithin c₃.nmem f2 (c₃.nreg ALLOC) N2 := by
    rw [A3]; exact (hN2.transport ag₃).mono (by omega)
  have hX₃ : X.holds P c₃.nmem (rd c₃ bMerge 9) (c₃.nreg ALLOC) := by
    rw [show rd c₃ bMerge 9 = g from r9, A3]
    exact X.mono P _ _ _ _ (by omega) (X.local_ P c.nmem c₃.nmem g A₀ (fun a ha => (ag₃ a ha).symm) hX)
  have hcap₃ : X.cap P c₃.nmem g = X.cap P c.nmem g := hXc P c.nmem c₃.nmem g A₀ ag₃ hX
  have hTD₃ := hΦ c₃.nmem (fun a _ => by rw [m₃])
  have pre : MergePre X OkModel P W c₃ :=
    mergePreR hG hWn hX₃ (by rw [show rd c₃ bMerge 9 = g from r9, hcap₃,
      show rd c₃ bMerge 5 = γ from r5]; exact hcap) (by rw [show rd c₃ bMerge 7 = D from r7]; exact hD)
      (by rw [show rd c₃ bMerge 5 = γ from r5, show rd c₃ bMerge 6 = γ + 1 from r6, hfl])
      hHA₃ hHok hwf hreg hsimp (by omega) b1 b1h (by omega) b2 b2h (by omega) hcons hlen
      (by rw [hs1]; omega) (by rw [hs2, hP21]; omega) hTD₃.2.2 hTD₃.2.1 (by omega)
      r0 r1 r2 r3 r4 hN1₃ hN2₃ (by rw [show rd c₃ bMerge 7 = D from r7]; exact hc1)
      (by rw [show rd c₃ bMerge 7 = D from r7]; exact hc2)
      (by rw [show rd c₃ bMerge 5 = γ from r5]; exact hγ1)
      (by rw [show rd c₃ bMerge 5 = γ from r5]; exact hγ2) hgen
      (by rw [show rd c₃ bMerge 7 = D from r7]; exact hfd)
  have hmc : mergeCost κ F G Hf c₃ =
      mgCostV κ F G Hf D N1.chords.length N2.chords.length γ (ma + mp) := by
    have x1 := hN1₃.nfAt.1
    have x2 := hN2₃.nfAt.1
    have x3 : c₃.nmem (A₀ + 1 + 2) = ma + mp := by
      rw [m₃, show A₀ + 1 + 2 = A₀ + 3 by omega]; exact w3
    unfold mergeCost mgCostV
    rw [show rd c₃ bMerge 7 = D from r7, show rd c₃ bMerge 3 = f1 from r3,
      show rd c₃ bMerge 4 = f2 from r4, show rd c₃ bMerge 5 = γ from r5,
      show rd c₃ bMerge 2 = A₀ + 1 from r2, x1, x2, x3]
  obtain ⟨c₄, k₄, e₄, hk₄, post, fr₄⟩ := hM P W c₃ hw₃ pre
    (by show c₃.nreg ALLOC + mergeCost κ F G Hf c₃ ≤ W; rw [A3, hmc]; omega)
  have hk₄' : k₄ ≤ mgCostV κ F G Hf D N1.chords.length N2.chords.length γ (ma + mp) := by
    have : k₄ ≤ mergeCost κ F G Hf c₃ := hk₄
    rw [hmc] at this; exact this
  have hw₄ := e₄.wb_right
  -- the new normal form
  have hJA : JunctionAt c₃.nmem (rd c₃ bMerge 0) (rd c₃ bMerge 1) (rd c₃ bMerge 2) (Qof P) H
      (jOf C1 C2 hlen) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [show rd c₃ bMerge 0 = D1 + 1 from r0, jOf_left]; exact b1
    · rw [show rd c₃ bMerge 1 = D2 + 1 from r1, jOf_right hlen hP21 hcons]; exact b2
    · rw [show rd c₃ bMerge 2 = A₀ + 1 from r2]; exact hTD₃.2.2
  obtain ⟨N, hN8, hNW8, hNc⟩ := post H (jOf C1 C2 hlen) N1 N2 hJA
    (by rw [show rd c₃ bMerge 3 = f1 from r3]; exact hN1₃.nfAt)
    (by rw [show rd c₃ bMerge 4 = f2 from r4]; exact hN2₃.nfAt)
  rw [show rd c₃ bMerge 6 = γ + 1 from r6, show rd c₃ bMerge 7 = D from r7] at hNc
  -- the band-21 registers survive the merge
  have hmb : ∀ q, bandOf q = bDownDrv → c₄.nreg q = c₃.nreg q := fun q hq => by
    refine fr₄.1 q (by rw [hq]; decide) ?_
    simp only [bandOf, bDownDrv] at hq; unfold ALLOC; omega
  have q37 : c₄.nreg 219137 = A₀ := by
    rw [hmb _ (by decide), g₃.1 _ (by decide)]; exact d37
  have q12 : c₄.nreg 219112 = ma := by
    rw [hmb _ (by decide), g₃.1 _ (by decide), v _ (by decide) (by decide), h12]
  have q16 : c₄.nreg 219116 = mp := by
    rw [hmb _ (by decide), g₃.1 _ (by decide), v _ (by decide) (by decide), h16]
  have q13 : c₄.nreg 219113 = γ := by
    rw [hmb _ (by decide), g₃.1 _ (by decide)]; exact b13
  have q41 : c₄.nreg 219141 = 1 := by
    rw [hmb _ (by decide), g₃.1 _ (by decide)]; exact b41
  obtain ⟨c₅, k₅, e₅, hk₅, o10, o11, o12, o13⟩ :=
    mgOut_exec (P := P) c₄ hw₄ q37 q12 q16 q13 q41 (by omega) hγW
  have g₅ : FrameB Bout c₄ c₅ := exec_frameB e₅ wr_mgOut
  have A5 : c₅.nreg ALLOC = c₄.nreg ALLOC := g₅.1 _ (by decide)
  have A4 : A₀ + 6 ≤ c₄.nreg ALLOC := by have := fr₄.2.2.2.2.2.1; omega
  have m5 : ∀ a, a < A₀ + 6 → c₅.nmem a = c₂.nmem a := fun a ha => by
    rw [g₅.2.2.1, fr₄.2.2.1 a (by omega), m₃]
  have hΦ5 : Robust (c₅.nreg ALLOC) c₅.nmem (fun m => m A₀ = 0 ∧ m (A₀ + 1) = HB ∧
      ChainDescAt m (A₀ + 1) (Qof P) H (jOf C1 C2 hlen).whole) := fun m' hm' =>
    hΦ m' (fun a ha => (hm' a (by omega)).trans (m5 a ha))
  have ag₅ : ∀ a, a < A₀ → c₅.nmem a = c.nmem a := fun a ha => (m5 a (by omega)).trans (hag a ha)
  -- the frame
  have hB21 : ∀ r, bandOf r = bDownDrv → r ≠ ALLOC := fun r hr => by
    simp only [bandOf, bDownDrv] at hr; unfold ALLOC; omega
  have F1 : Frame mgBands c c₁ k₁ := NFLoc.frame_of_frameB g₁ (fun r hr => by
    simp only [Btop, Bool.or_eq_true, decide_eq_true_eq] at hr
    unfold mgBands
    rcases hr with (h | h) | h
    · have : bandOf r = bDownDrv := by simp only [bandOf, bDownDrv]; omega
      exact ⟨by rw [this]; decide, by unfold ALLOC; omega⟩
    · have : bandOf r = bSign := by simp only [bandOf, bSign]; omega
      exact ⟨by rw [this]; decide, by unfold ALLOC; omega⟩
    · have : bandOf r = bLocate := by simp only [bandOf, bLocate]; omega
      exact ⟨by rw [this]; decide, by unfold ALLOC; omega⟩) k₁
  have F2 : Frame mgBands c₁ c₂ k₂ := by
    refine ⟨fun r hr hra => g₂.1 r ?_, fun r _ => by rw [drr],
      fun a ha => wlt a (lt_of_lt_of_eq ha aA), fun a _ => by rw [drm], dout,
      by show c₁.nreg 9999 ≤ c₂.nreg 9999; rw [dA, aA]; omega,
      by show c₂.nreg 9999 ≤ c₁.nreg 9999 + k₂; rw [dA, aA]; omega⟩
    simp only [Bdesc, decide_eq_false_iff_not]
    rintro (rfl | rfl | rfl | rfl)
    · exact hr (by unfold mgBands; decide)
    · exact hr (by unfold mgBands; decide)
    · exact hr (by unfold mgBands; decide)
    · exact hra rfl
  have F3 : Frame mgBands c₂ c₃ k₃ := NFLoc.frame_of_frameB g₃ (fun r hr => by
    simp only [Bargs, decide_eq_true_eq] at hr
    have : bandOf r = bMerge := by simp only [bandOf, bMerge]; omega
    exact ⟨by rw [this]; decide, by unfold ALLOC; omega⟩) k₃
  have F4 : Frame mgBands c₃ c₄ k₄ := fr₄.mono (Finset.subset_insert _ _) le_rfl
  have F5 : Frame mgBands c₄ c₅ k₅ := NFLoc.frame_of_frameB g₅ (fun r hr => by
    simp only [Bout, decide_eq_true_eq] at hr
    have : bandOf r = bDownDrv := by simp only [bandOf, bDownDrv]; omega
    exact ⟨by rw [this]; decide, by unfold ALLOC; omega⟩) k₅
  have FF := F1.trans (F2.trans (F3.trans (F4.trans F5)))
  simp only [Finset.union_self] at FF
  refine ⟨c₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    o10, ?_, o12, o13, by omega, hΦ5, ?_, ⟨N, ?_, hNc⟩, ?_, FF⟩
  · rw [o11]; have : A₀ + 6 ≤ rd c₄ bMerge 8 := by rw [← A3]; exact hN8
    exact this
  · refine ⟨by omega, fun _ => ?_⟩
    obtain ⟨y0, y1, y2⟩ := hΦ5.holds
    exact chainWF_host (hHA c₅.nmem ag₅) hHok hwf (by omega) y2 y1 (by omega)
      (by rw [jOf_whole_s, jOf_whole_P, hs1]; omega)
  · rw [o11, A5, g₅.2.2.1]; exact hNW8
  · intro q hq hr
    have hq' : 210000 ≤ q ∧ q < 220000 := by simp only [bandOf, bDownDrv] at hq; omega
    rw [g₅.1 q (by simp only [Bout, decide_eq_false_iff_not]; omega), hmb q hq,
      g₃.1 q (by simp only [Bargs, decide_eq_false_iff_not]; omega),
      v q (by simp only [Btop, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
        (by simp only [Bdesc, decide_eq_false_iff_not]; omega)]

end exec

end

end DrvR

end Chazelle.Core
