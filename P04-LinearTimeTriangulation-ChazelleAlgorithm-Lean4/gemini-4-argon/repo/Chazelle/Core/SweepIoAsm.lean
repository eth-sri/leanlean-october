module

public import Chazelle.Core.SweepIoSpec2
public import Chazelle.Core.SweepRamStage0

/-!
# The sweep RAM (WP-D), the assembly (piece I), part 1: transports

Facts of the stage outputs survive later steps that keep the memory below the allocator, grow the
allocator and keep the relevant registers:

* `st0S_md`, `st0S_transport`: the stage-0 state `St0S` (with new model descriptors, or as is);
* `out_transport`: the outputs of stages 2/3 (`SweepEv.Out`);
* `aenv_transport`: the environment of the answer phase (`AEnv`), along the frame of an
  initialisation (`InitSpec`) and of the write of `sw 11`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep

@[expose] public section

variable {P : Polygon} {W : ℕ}

/-! ## Descriptors -/

/-- A model descriptor survives a change of the memory above its bound. -/
theorem asm_modelDesc {m m' : ℕ → ℕ} {D E E' : ℕ} {M : Model}
    (hd : ModelDescAt m D (Qof P) M) (hwf : ModelDescWF P E m D)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    ModelDescAt m' D (Qof P) M ∧ ModelDescWF P E' m' D := by
  rcases hd with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, hL, hM⟩
  · obtain ⟨w1, w2, w3⟩ := ShotList.modelDesc_keep hwf h0 hC he hE
    exact ⟨Or.inl ⟨w2, H, C, w3, rfl⟩, w1⟩
  · have hD6 := hwf.1
    have e0 : m' D = m D := he _ (by omega)
    have e1 : m' (D + 1) = m (D + 1) := he _ (by omega)
    refine ⟨Or.inr ⟨by rw [e0, h1], by rwa [e1], hM⟩, by omega, fun h => ?_⟩
    rw [e0, h1] at h; exact absurd h one_ne_zero

/-- A junction survives a change of the memory above its bound. -/
theorem asm_junction {m m' : ℕ → ℕ} {b0 b1 b2 E E' : ℕ} {H : Host} {J : Merge.Junction}
    (hJ : JunctionAt m b0 b1 b2 (Qof P) H J) (hwf : JunctionWF P E m b0 b1 b2)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    JunctionAt m' b0 b1 b2 (Qof P) H J ∧ JunctionWF P E' m' b0 b1 b2 := by
  obtain ⟨wl, wr', ww, hreg⟩ := hwf
  obtain ⟨j0, w0⟩ := chainDesc_keep wl hJ.1 he hE
  obtain ⟨j1, w1⟩ := chainDesc_keep wr' hJ.2.1 he hE
  obtain ⟨j2, w2⟩ := chainDesc_keep ww hJ.2.2 he hE
  refine ⟨⟨j0, j1, j2⟩, w0, w1, w2, fun H' hH' => ?_⟩
  have hb : m' b2 = m b2 := he _ (by have := ww.1; omega)
  rw [hb] at hH'
  obtain ⟨-, -, hEb, -⟩ := ww.2 H J.whole hJ.2.2
  have hH : HostAt m' (m b2) H := ShotList.hostAt_agree hJ.2.2.1 hEb he
  rw [NFLoc.hostAt_unique hH' hH]
  exact hreg H hJ.2.2.1

/-! ## The stage-0 state -/

/-- **`St0S` with new model descriptors.** -/
theorem st0S_md {c c' : Config} {H : Host} {J : Merge.Junction} (h : SweepEv.St0S P c H J)
    (hr : ∀ j, j < 96 → j ≠ 11 → j ≠ 30 → j ≠ 31 → c'.nreg (sw j) = c.nreg (sw j))
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC)
    (md30 : ModelDescAt c'.nmem (c'.nreg (sw 30)) (Qof P) (chainModel J.left))
    (w30 : ModelDescWF P (c'.nreg ALLOC) c'.nmem (c'.nreg (sw 30)))
    (md31 : ModelDescAt c'.nmem (c'.nreg (sw 31)) (Qof P) (chainModel J.right))
    (w31 : ModelDescWF P (c'.nreg ALLOC) c'.nmem (c'.nreg (sw 31))) :
    SweepEv.St0S P c' H J := by
  obtain ⟨h90, h91, h92, h93, hJ, hwf, d20, w20, d21, w21, h23, h24, h40, h45, h33, h34, h35,
    -, -, -, -⟩ := h
  have r : ∀ j, j < 96 → j ≠ 11 → j ≠ 30 → j ≠ 31 → c'.nreg (sw j) = c.nreg (sw j) := hr
  obtain ⟨hJ', hwf'⟩ := asm_junction hJ hwf hm hA
  obtain ⟨d20', w20'⟩ := chainDesc_keep w20 d20 hm hA
  obtain ⟨d21', w21'⟩ := chainDesc_keep w21 d21 hm hA
  refine ⟨by rw [r 90 (by omega) (by omega) (by omega) (by omega), h90],
    by rw [r 91 (by omega) (by omega) (by omega) (by omega), h91],
    by rw [r 92 (by omega) (by omega) (by omega) (by omega), h92],
    by rw [r 93 (by omega) (by omega) (by omega) (by omega), h93], ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [r 23 (by omega) (by omega) (by omega) (by omega), r 3 (by omega) (by omega) (by omega) (by omega), h23],
    by rw [r 24 (by omega) (by omega) (by omega) (by omega), r 4 (by omega) (by omega) (by omega) (by omega), h24],
    fun k hk => by rw [r (40 + k) (by omega) (by omega) (by omega) (by omega)]; exact h40 k hk,
    fun k hk => by rw [r (45 + k) (by omega) (by omega) (by omega) (by omega)]; exact h45 k hk,
    by rw [r 33 (by omega) (by omega) (by omega) (by omega), h33],
    by rw [r 34 (by omega) (by omega) (by omega) (by omega), h34],
    by rw [r 35 (by omega) (by omega) (by omega) (by omega), h35], md30, w30, md31, w31⟩
  · rwa [r 0 (by omega) (by omega) (by omega) (by omega), r 1 (by omega) (by omega) (by omega) (by omega),
      r 2 (by omega) (by omega) (by omega) (by omega)]
  · rwa [r 0 (by omega) (by omega) (by omega) (by omega), r 1 (by omega) (by omega) (by omega) (by omega),
      r 2 (by omega) (by omega) (by omega) (by omega)]
  · rwa [r 20 (by omega) (by omega) (by omega) (by omega)]
  · rwa [r 20 (by omega) (by omega) (by omega) (by omega)]
  · rwa [r 21 (by omega) (by omega) (by omega) (by omega)]
  · rwa [r 21 (by omega) (by omega) (by omega) (by omega)]

/-- **`St0S` survives** a step keeping `sw 0 … 99`, the memory below the allocator, and growing
the allocator. -/
theorem st0S_transport {c c' : Config} {H : Host} {J : Merge.Junction}
    (h : SweepEv.St0S P c H J) (hr : ∀ j, j < 100 → j ≠ 11 → c'.nreg (sw j) = c.nreg (sw j))
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    SweepEv.St0S P c' H J := by
  have h' := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, d30, w30, d31, w31⟩ := h'
  obtain ⟨d30', w30'⟩ := asm_modelDesc d30 w30 hm hA
  obtain ⟨d31', w31'⟩ := asm_modelDesc d31 w31 hm hA
  rw [← hr 30 (by omega) (by omega)] at d30' w30'
  rw [← hr 31 (by omega) (by omega)] at d31' w31'
  exact st0S_md h (fun j hj h11 _ _ => hr j (by omega) h11) hm hA d30' w30' d31' w31'

/-! ## The outputs of stages 2/3 -/

/-- **The outputs of stages 2/3 survive** a step keeping their registers and the memory below the
allocator. -/
theorem out_transport {c c' : Config} {J : Merge.Junction} {N₂ : NF}
    (h : SweepEv.Out P J N₂ c)
    (hr : ∀ j, j = 200 ∨ j = 201 ∨ j = 300 ∨ j = 301 ∨ j = 302 → c'.nreg (sw j) = c.nreg (sw j))
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)
    (hs : rd c bSweep 200 + 5 * rd c bSweep 201 ≤ c.nreg ALLOC)
    (hl : rd c bSweep 300 + 7 * rd c bSweep 301 ≤ c.nreg ALLOC)
    (ht : rd c bSweep 302 + 3 * (2 * N₂.nChords) ≤ c.nreg ALLOC) :
    SweepEv.Out P J N₂ c' := by
  have e : ∀ j, j = 200 ∨ j = 201 ∨ j = 300 ∨ j = 301 ∨ j = 302 → rd c' bSweep j = rd c bSweep j :=
    fun j hj => hr j hj
  unfold SweepEv.Out at h ⊢
  rw [show rd c' bSweep 200 = rd c bSweep 200 from e 200 (by simp),
    show rd c' bSweep 201 = rd c bSweep 201 from e 201 (by simp),
    show rd c' bSweep 300 = rd c bSweep 300 from e 300 (by simp),
    show rd c' bSweep 301 = rd c bSweep 301 from e 301 (by simp),
    show rd c' bSweep 302 = rd c bSweep 302 from e 302 (by simp)]
  obtain ⟨rs, ls, hrl, hrs, hsok, hrw, hll, hls, hlok, hlw, htab, htw⟩ := h
  have htabeq : ∀ j, j < 2 * N₂.nChords →
      tabOf J (Qof P) c'.nmem (rd c bSweep 302) j = tabOf J (Qof P) c.nmem (rd c bSweep 302) j := by
    intro j hj
    unfold tabOf
    rw [hm _ (by omega), hm (rd c bSweep 302 + 3 * j + 1) (by omega),
      hm (rd c bSweep 302 + 3 * j + 2) (by omega)]
  refine ⟨rs, ls, hrl, fun i hi => ?_, hsok, hrw, hll, fun i hi => ?_, hlok, hlw, ?_, fun j hj => ?_⟩
  · rw [hm _ (by omega), hm (rd c bSweep 200 + 5 * i + 1) (by omega),
      hm (rd c bSweep 200 + 5 * i + 2) (by omega), hm (rd c bSweep 200 + 5 * i + 3) (by omega),
      hm (rd c bSweep 200 + 5 * i + 4) (by omega)]
    exact hrs i hi
  · rw [hm _ (by omega), hm (rd c bSweep 300 + 7 * i + 1) (by omega),
      hm (rd c bSweep 300 + 7 * i + 2) (by omega), hm (rd c bSweep 300 + 7 * i + 3) (by omega),
      hm (rd c bSweep 300 + 7 * i + 4) (by omega), hm (rd c bSweep 300 + 7 * i + 5) (by omega),
      hm (rd c bSweep 300 + 7 * i + 6) (by omega)]
    exact hls i hi
  · intro j hj h1 h2 h3
    have := htab j hj h1 h2 h3
    rw [htabeq j hj]; exact this
  · rw [hm _ (by omega), hm (rd c bSweep 302 + 3 * j + 1) (by omega),
      hm (rd c bSweep 302 + 3 * j + 2) (by omega)]
    exact htw j hj

/-! ## The environment of the answer phase -/

/-- **`AEnv` survives** a step keeping `sw j` for `j < 700` other than `sw 11` and the registers
`sw 620 … 659`, the memory below the allocator, and growing the allocator. -/
theorem aenv_transport {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
    {H : Host} {N₁ N₂ : NF} {E : ℕ} {c c' : Config} (hX : X.CapLocal)
    (h : AEnv P W X Ok J H N₁ N₂ E c)
    (hr : ∀ j, j < 700 → j ≠ 11 → (j < 620 ∨ 660 ≤ j) → c'.nreg (sw j) = c.nreg (sw j))
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    AEnv P W X Ok J H N₁ N₂ E c' := by
  have r : ∀ j, j < 620 → j ≠ 11 → c'.nreg (sw j) = c.nreg (sw j) := fun j h1 h2 =>
    hr j (by omega) h2 (Or.inl h1)
  have e3 := r 3 (by omega) (by omega)
  have e4 := r 4 (by omega) (by omega)
  have e5 := r 5 (by omega) (by omega)
  have e6 := r 6 (by omega) (by omega)
  have e10 := r 10 (by omega) (by omega)
  have e20 := r 20 (by omega) (by omega)
  have e21 := r 21 (by omega) (by omega)
  have e30 := r 30 (by omega) (by omega)
  have e31 := r 31 (by omega) (by omega)
  have eTB : c'.nreg TBR = c.nreg TBR := r 600 (by omega) (by omega)
  have eTL : c'.nreg TLR = c.nreg TLR := r 601 (by omega) (by omega)
  have hmE : ∀ a, a < E → c'.nmem a = c.nmem a := fun a ha => hm a (by have := h.hE; omega)
  have h3 : ∀ j, j < 5 → c.nreg (sw 30) + 1 + j < c.nreg ALLOC := by
    intro j hj; have := h.hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1; omega
  have h3' : ∀ j, j < 5 → c.nreg (sw 31) + 1 + j < c.nreg ALLOC := by
    intro j hj; have := h.hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have h20 : ∀ j, j < 5 → c.nreg (sw 20) + j < c.nreg ALLOC := by
    intro j hj; have := h.hst.2.2.2.2.2.2.2.1.1; omega
  have h21 : ∀ j, j < 5 → c.nreg (sw 21) + j < c.nreg ALLOC := by
    intro j hj; have := h.hst.2.2.2.2.2.2.2.2.2.1.1; omega
  obtain ⟨b3, -⟩ := Restore.nf_bounds h.hN₁
  obtain ⟨b4, -⟩ := Restore.nf_bounds h.hN₂
  have hEA := h.hE
  refine
    { hG := h.hG
      hWh := h.hWh
      hX := ?_
      hcap := ?_
      hP := h.hP
      hOk₁ := h.hOk₁
      hOk₂ := h.hOk₂
      hN₁ := by rw [e3]; exact Robust.transport h.hN₁ hmE
      hN₂ := by rw [e4]; exact Robust.transport h.hN₂ hmE
      hNF₁ := h.hNF₁
      hNF₂ := h.hNF₂
      hdeg₁ := by rw [e6]; exact h.hdeg₁
      hdeg₂ := by rw [e6]; exact h.hdeg₂
      hsg₁ := by rw [e5]; exact h.hsg₁
      hsg₂ := by rw [e5]; exact h.hsg₂
      hst := st0S_transport h.hst (fun j hj h11 => r j (by omega) h11) hm hA
      hE := by omega
      hWm := h.hWm
      hK := ?_
      htab := ?_
      hbig₁ := by rw [eTL]; exact h.hbig₁
      hbig₂ := by rw [eTL]; exact h.hbig₂
      hbigE := ?_
      hTB := by rw [eTB]; exact h.hTB
      hTW := by rw [eTB, eTL]; have := h.hTW; omega
      hout := ?_
      hstops := ?_
      hlog := ?_
      htabw := ?_
      hK₁ := by rw [e3, hm _ (by omega)]; exact h.hK₁
      hK₂ := by rw [e4, hm _ (by omega)]; exact h.hK₂
      hmd₁ := fun j hj => by rw [e30, e20, hm _ (h3 j hj), hm _ (h20 j hj)]; exact h.hmd₁ j hj
      hmd₂ := fun j hj => by rw [e31, e21, hm _ (h3' j hj), hm _ (h21 j hj)]; exact h.hmd₂ j hj }
  · rw [e10]; exact X.mono _ _ _ _ _ hA (X.local_ _ _ _ _ _ (fun a ha => (hm a ha).symm) h.hX)
  · rw [e5, e10, hX _ _ _ _ _ hm h.hX]; exact h.hcap
  · obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := h.hK
    exact ⟨(r 610 (by omega) (by omega)).trans k0, (r 611 (by omega) (by omega)).trans k1,
      (r 612 (by omega) (by omega)).trans k6, (r 613 (by omega) (by omega)).trans k4,
      (r 614 (by omega) (by omega)).trans k5, (r 615 (by omega) (by omega)).trans k2,
      (r 616 (by omega) (by omega)).trans k3⟩
  · intro j hj
    rw [eTL] at hj
    rw [eTB, hm _ (by have := h.hTW; omega)]
    exact h.htab j hj
  · show rd c' bSweep 201 + rd c' bSweep 301 + 2 * N₂.nChords < 2 ^ c'.nreg TLR
    rw [eTL, show rd c' bSweep 201 = rd c bSweep 201 from r 201 (by omega) (by omega),
      show rd c' bSweep 301 = rd c bSweep 301 from r 301 (by omega) (by omega)]
    exact h.hbigE
  · exact out_transport h.hout (fun j hj => r j (by omega) (by omega)) hm h.hstops h.hlog h.htabw
  · show rd c' bSweep 200 + 5 * rd c' bSweep 201 ≤ c'.nreg ALLOC
    rw [show rd c' bSweep 200 = rd c bSweep 200 from r 200 (by omega) (by omega),
      show rd c' bSweep 201 = rd c bSweep 201 from r 201 (by omega) (by omega)]
    have := h.hstops; omega
  · show rd c' bSweep 300 + 7 * rd c' bSweep 301 ≤ c'.nreg ALLOC
    rw [show rd c' bSweep 300 = rd c bSweep 300 from r 300 (by omega) (by omega),
      show rd c' bSweep 301 = rd c bSweep 301 from r 301 (by omega) (by omega)]
    have := h.hlog; omega
  · show rd c' bSweep 302 + 3 * (2 * N₂.nChords) ≤ c'.nreg ALLOC
    rw [show rd c' bSweep 302 = rd c bSweep 302 from r 302 (by omega) (by omega)]
    have := h.htabw; omega

end

end SweepIo

end Chazelle.Core
