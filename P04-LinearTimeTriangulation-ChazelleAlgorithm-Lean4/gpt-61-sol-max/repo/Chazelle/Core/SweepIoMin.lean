module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoGather

/-!
# The sweep RAM (WP-D), answers: the candidate accumulator

Every answer is the earliest of a few candidate points on the query ray (`Sweep` candidate
principle, `SweepIoAns.whole_firstHit_of_mem`).  The accumulator at a register block `A`
(`A … A + 12`) keeps the earliest candidate offered so far: a flag (`A`), its walk position
(`A + 1`, `A + 2`) in the chain model with tag `A + 3` (`Mod tag`), and its abscissa record
(`A + 4 … A + 7`).  `offer` computes the abscissa record of a new candidate (`absKey`, into
`A + 8 … A + 11`) and keeps the earlier one along the ray (`absCmp`, bit in `A + 12`).

`AccOK … L c`: the flag is `1` iff some candidate was offered (`L` the set of their ray
parameters), and then the kept candidate has the least parameter.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **The accumulator state**: `L` is the set of the ray parameters of the offered candidates. -/
def AccOK (P : Polygon) (A : ℕ) (Mod : ℕ → Chain) (R₀ : ℝ) (z : Point) (σ : ℝ) (L : Set ℝ)
    (c : Config) : Prop :=
  c.nreg A ≤ 1 ∧ (c.nreg A = 0 → L = ∅) ∧
    (c.nreg A = 1 → ∃ τ ∈ L, (∀ τ' ∈ L, τ ≤ τ') ∧ c.nreg (A + 3) ≤ 2 ∧
      ProperPos (chainModel (Mod (c.nreg (A + 3)))) (Qof P) P.n ⟨c.nreg (A + 1), c.nreg (A + 2)⟩ ∧
      c.nreg (A + 1) < (chainModel (Mod (c.nreg (A + 3)))).W.n ∧
      (chainModel (Mod (c.nreg (A + 3)))).pos (Qof P) ⟨c.nreg (A + 1), c.nreg (A + 2)⟩ =
        rayPt z σ τ ∧
      AbsRec P c (A + 4) (rayPt z σ τ).1 R₀)

/-- Take the candidate: copy its position, tag and record, set the flag. -/
def takeL (A e h t : ℕ) : List Instr :=
  [.copyN (A + 1) e, .copyN (A + 2) h, .copyN (A + 3) t, .copyN (A + 4) (A + 8),
    .copyN (A + 5) (A + 9), .copyN (A + 6) (A + 10), .copyN (A + 7) (A + 11), .constN A 1]

/-- **Offer the candidate** at the position `(e, h)` of the chain model of the descriptor `dsc`
(tag register `t`), for the direction code in `dR`. -/
def offer (A dsc e h t dR : ℕ) : Stmt :=
  .seq (callAbs dsc e h (A + 8))
    (.ifLtN A K1 (block (takeL A e h t))
      (.ifLtN dR K1
        (.seq (callAbsCmp (A + 4) (A + 8) (A + 12)) (.ifLtN K0 (A + 12) (block (takeL A e h t)) .skip))
        (.ifLtN K1 dR
          (.seq (callAbsCmp (A + 4) (A + 8) (A + 12)) (.ifLtN K0 (A + 12) (block (takeL A e h t)) .skip))
          (.seq (callAbsCmp (A + 8) (A + 4) (A + 12)) (.ifLtN K0 (A + 12) (block (takeL A e h t)) .skip)))))

/-- The cost of an offer. -/
def offerK : ℕ := 17000

/-- The empty accumulator. -/
theorem accOK_init (A : ℕ) (Mod : ℕ → Chain) (R₀ : ℝ) (z : Point) (σ : ℝ) {c : Config}
    (h : c.nreg A = 0) : AccOK P A Mod R₀ z σ ∅ c :=
  ⟨by omega, fun _ => rfl, fun h' => by omega⟩

/-- The register effect of `takeL`. -/
theorem takeL_val (m f : ℕ → ℕ) {A e h t : ℕ} (_he : e < A ∨ A + 12 < e) (hh : h < A ∨ A + 12 < h)
    (ht : t < A ∨ A + 12 < t) :
    regB m (takeL A e h t) f A = 1 ∧ regB m (takeL A e h t) f (A + 1) = f e ∧
    regB m (takeL A e h t) f (A + 2) = f h ∧ regB m (takeL A e h t) f (A + 3) = f t ∧
    regB m (takeL A e h t) f (A + 4) = f (A + 8) ∧ regB m (takeL A e h t) f (A + 5) = f (A + 9) ∧
    regB m (takeL A e h t) f (A + 6) = f (A + 10) ∧ regB m (takeL A e h t) f (A + 7) = f (A + 11) ∧
    (∀ q, (q < A ∨ A + 7 < q) → regB m (takeL A e h t) f q = f q) := by
  simp only [takeL, regB, regI, upd]
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp_all
  all_goals grind

/-- **Taking a candidate** that precedes every offered one. -/
theorem take_irs {A e h t : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {z : Point} {σ : ℝ} {L : Set ℝ}
    {τ : ℝ} (hI : IInv W c₀ c) (hW1 : 1 ≤ W) (hA : 240700 ≤ A ∧ A + 12 < 250000)
    (hout : (e < A ∨ A + 12 < e) ∧ (h < A ∨ A + 12 < h) ∧ (t < A ∨ A + 12 < t))
    (hmin : ∀ τ' ∈ L, τ ≤ τ') (htag : c.nreg t ≤ 2)
    (he : c.nreg e < (chainModel (Mod (c.nreg t))).W.n)
    (hpp : ProperPos (chainModel (Mod (c.nreg t))) (Qof P) P.n ⟨c.nreg e, c.nreg h⟩)
    (hpos : (chainModel (Mod (c.nreg t))).pos (Qof P) ⟨c.nreg e, c.nreg h⟩ = rayPt z σ τ)
    (hrec : AbsRec P c (A + 8) (rayPt z σ τ).1 R₀) :
    IRS P W c₀ (block (takeL A e h t)) c 8 (fun c' =>
      AccOK P A Mod R₀ z σ (insert τ L) c' ∧ (∀ r, (r < A ∨ A + 7 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  have sc : ∀ j, j ≤ 7 → IScr (A + j) := fun j hj => iscr_sw (by omega) (by omega)
  have hok : okB W c.nmem (takeL A e h t) c.nreg := by
    simp only [takeL, okB, okI]
    ram_grind
  refine (IRS.block _ hI hok).mono (by simp [takeL]) ?_
  rintro c' rfl
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, vo⟩ := takeL_val c.nmem c.nreg hout.1 hout.2.1 hout.2.2
  unfold AccOK
  simp only
  refine ⟨⟨by rw [v0], fun h0 => by omega, fun _ => ⟨τ, Set.mem_insert _ _,
    fun τ' hτ' => ?_, by omega, by grind,
    by grind, by grind, ?_⟩⟩, vo, trivial⟩
  · grind
  · refine absRec_transport (c := c) hrec ?_ ?_ ?_ ?_
    all_goals omega

/-- An abscissa record determines its abscissa. -/
theorem absRec_val {r : ℕ} {x x' R : ℝ} (h : AbsRec P c r x R) (h' : AbsRec P c r x' R) :
    x = x' := by
  obtain ⟨-, h⟩ := h
  obtain ⟨-, h'⟩ := h'
  rcases h with ⟨k, hx⟩ | ⟨k, hx⟩ | ⟨k, -, s, hs, -, he⟩ <;>
    rcases h' with ⟨k', hx'⟩ | ⟨k', hx'⟩ | ⟨k', -, s', hs', -, he'⟩ <;>
    first | omega | (rw [hx, hx']) | skip
  rw [← he, ← he', SignK.symPtIn_unique hs hs']

theorem dirOf_eq_one {d : ℕ} (h : d = 1) : dirOf d = 1 := by aesop
theorem dirOf_eq_neg {d : ℕ} (h : d ≠ 1) : dirOf d = -1 := by simp_all [dirOf]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **An offer**: the accumulator keeps the earliest candidate. -/
theorem offer_irs {A dsc e h t dR : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {z : Point} {L : Set ℝ}
    {τ : ℝ} (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hW3 : P.n + 3 ≤ W)
    (hA : 240700 ≤ A ∧ A + 12 < 250000)
    (hregs : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ e ∧ e < 250000 ∧ 240000 ≤ h ∧
      h < 250000 ∧ 240000 ≤ t ∧ t < 250000 ∧ 240000 ≤ dR ∧ dR < 250000)
    (hout : (dsc < A ∨ A + 12 < dsc) ∧ (e < A ∨ A + 12 < e) ∧ (h < A ∨ A + 12 < h) ∧
      (t < A ∨ A + 12 < t) ∧ (dR < A ∨ A + 12 < dR))
    (hacc : AccOK P A Mod R₀ z (dirOf (c.nreg dR)) L c)
    (htag : c.nreg t ≤ 2) (hctx : ChainCtx P W c dsc (Mod (c.nreg t)))
    (hR : (Mod (c.nreg t)).radius = R₀)
    (he : c.nreg e < (chainModel (Mod (c.nreg t))).W.n)
    (hpp : ProperPos (chainModel (Mod (c.nreg t))) (Qof P) P.n ⟨c.nreg e, c.nreg h⟩)
    (hpos : (chainModel (Mod (c.nreg t))).pos (Qof P) ⟨c.nreg e, c.nreg h⟩ =
      rayPt z (dirOf (c.nreg dR)) τ)
    (hy : |z.2| < R₀) (hroom : c.nreg ALLOC + offerK ≤ W) :
    IRS P W c₀ (offer A dsc e h t dR) c offerK (fun c' =>
      AccOK P A Mod R₀ z (dirOf (c.nreg dR)) (insert τ L) c' ∧
      (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  
  have hW1 : 1 ≤ W := by omega
  set σ := dirOf (c.nreg dR) with hσ
  
  -- the record of the candidate
  refine IRS.mono (K := 16707 + (17000 - 16707)) (IRS.seq (callAbs_irs (dsc := dsc) (re := e) (rh := h)
    (o := A + 8) hI hctx ⟨hregs.1, hregs.2.1, hregs.2.2.1, hregs.2.2.2.1, hregs.2.2.2.2.1,
      hregs.2.2.2.2.2.1⟩ ⟨by omega, by omega⟩ he hpp (by simp_all)
      (by omega_nf)) ?_) (by omega_nf) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨hrec₁, k1, hal₁, hm₁⟩
  rw [hpos, hR] at hrec₁
  have k1' : ∀ r, bandOf r ∉ oracleBands → (r < A + 8 ∨ A + 11 < r) → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 => k1 r h1 (by omega) h3
  have nob : ∀ r, 240000 ≤ r → r < 250000 → bandOf r ∉ oracleBands := fun r h1 h2 =>
    not_oracle_sw h1 h2
  have keep : ∀ r, 240000 ≤ r → r < 250000 → (r < A + 8 ∨ A + 11 < r) →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    k1' r (nob r h1 h2) h3 (by omega_nf)
  have e1 := keep e hregs.2.2.1 hregs.2.2.2.1 (by omega)
  have h1 := keep h hregs.2.2.2.2.1 hregs.2.2.2.2.2.1 (by omega)
  have t1 := keep t hregs.2.2.2.2.2.2.1 hregs.2.2.2.2.2.2.2.1 (by omega)
  have d1 := keep dR hregs.2.2.2.2.2.2.2.2.1 hregs.2.2.2.2.2.2.2.2.2 (by omega)
  have a1 : ∀ j, j ≤ 7 → c₁.nreg (A + j) = c.nreg (A + j) := fun j hj =>
    keep _ (by omega) (by omega) (by omega)
  have a0 : c₁.nreg A = c.nreg A := by grind
  have k1₁ : c₁.nreg K1 = 1 := (hK.fix hI₁).2.1
  
  -- the final frame of a take
  have fin_take : ∀ c' : Config, (∀ r, (r < A ∨ A + 7 < r) → c'.nreg r = c₁.nreg r) →
      (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) := fun c' hk r hr1 hr2 hr3 => by
    rw [hk r (by omega)]; grind
  by_cases hf : c₁.nreg A < c₁.nreg K1
  · -- the accumulator is empty: take
    have hf0 : c.nreg A = 0 := by omega
    have hL : L = ∅ := hacc.2.1 hf0
    refine (IRS.ifT hf (take_irs (L := L) (τ := τ) (Mod := Mod) hI₁ hW1 hA ⟨hout.2.1, hout.2.2.1, hout.2.2.2.1⟩
      (by grind) (by omega) (by grind)
      (by grind) (by grind) hrec₁)).mono (by omega) ?_
    rintro c' ⟨hacc', hk, hm⟩
    have hAc : c'.nreg ALLOC = c₁.nreg ALLOC := hk _ (by omega_nf)
    refine ⟨hacc', fin_take c' hk, by omega, fun a ha => by grind⟩
  · -- compare with the kept candidate
    have hf1 : c.nreg A = 1 := by
      rw [k1₁, a0] at hf; have := hacc.1; omega
    obtain ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, hrecA⟩ := hacc.2.2 hf1
    have hrecA₁ : AbsRec P c₁ (A + 4) (rayPt z σ τa).1 R₀ :=
      absRec_transport hrecA (a1 4 (by norm_num)) (by grind)
        (by grind)
        (by grind)
    -- the comparison step for either order
    have cmp : ∀ (a b : ℕ), (a = A + 4 ∧ b = A + 8 ∨ a = A + 8 ∧ b = A + 4) →
        (∀ x₁ x₂ : ℝ, AbsRec P c₁ a x₁ R₀ → AbsRec P c₁ b x₂ R₀ → (x₁ < x₂ ↔ τ < τa)) →
        IRS P W c₀ (.seq (callAbsCmp a b (A + 12))
          (.ifLtN K0 (A + 12) (block (takeL A e h t)) .skip)) c₁ (269 + 10)
          (fun c' => AccOK P A Mod R₀ z σ (insert τ L) c' ∧
            (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ ALLOC →
              c'.nreg r = c.nreg r) ∧
            c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
      intro a b hab hiff
      have hxa : AbsRec P c₁ a (if a = A + 4 then (rayPt z σ τa).1 else (rayPt z σ τ).1) R₀ := by
        rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · grind
        grind
      have hxb : AbsRec P c₁ b (if b = A + 4 then (rayPt z σ τa).1 else (rayPt z σ τ).1) R₀ := by
        rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · grind
        grind
      refine IRS.seq (callAbsCmp_irs hI₁ hG hW3 ⟨by omega,
        by omega,
        by omega,
        by omega⟩ ⟨by omega, by omega⟩ hxa hxb
        (by grind [offerK])) ?_
      rintro c₂ hI₂ hA₂ hA₂' ⟨hbit, k2, hal₂, hm₂⟩
      have hb' := (hiff _ _ hxa hxb)
      have k2' : ∀ r, bandOf r ∉ oracleBands → r ≠ A + 12 → r ≠ ALLOC → c₂.nreg r = c₁.nreg r := k2
      have keep2 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ A + 12 → c₂.nreg r = c₁.nreg r :=
        fun r h1 h2 h3 => k2' r (nob r h1 h2) h3 (by omega_nf)
      have k0₂ : c₂.nreg K0 = 0 := (hK.fix hI₂).1
      by_cases hc : c₂.nreg K0 < c₂.nreg (A + 12)
      · -- take
        rw [k0₂] at hc
        have hlt : τ < τa := hb'.1 (hbit.2.1 (by have := hbit.1; omega))
        refine (IRS.ifT (by omega) (take_irs (L := L) (τ := τ) (Mod := Mod) hI₂ hW1 hA
          ⟨hout.2.1, hout.2.2.1, hout.2.2.2.1⟩ (fun τ' hτ' => (hlt.trans_le (hmin τ' hτ')).le)
          (by rw [keep2 t (by omega) (by omega) (by omega), t1]; exact htag)
          (by rw [keep2 t (by omega) (by omega) (by omega), keep2 e (by omega) (by omega) (by omega),
            t1, e1]; exact he)
          (by rw [keep2 t (by omega) (by omega) (by omega), keep2 e (by omega) (by omega) (by omega),
            keep2 h (by omega) (by omega) (by omega), t1, e1, h1]; exact hpp)
          (by rw [keep2 t (by omega) (by omega) (by omega), keep2 e (by omega) (by omega) (by omega),
            keep2 h (by omega) (by omega) (by omega), t1, e1, h1, hpos])
          (absRec_transport hrec₁ (keep2 _ (by omega) (by omega) (by omega))
            (by rw [show A + 8 + 1 = A + 9 by omega]; exact keep2 _ (by omega) (by omega) (by omega))
            (by rw [show A + 8 + 2 = A + 10 by omega]; exact keep2 _ (by omega) (by omega) (by omega))
            (by rw [show A + 8 + 3 = A + 11 by omega]; exact keep2 _ (by omega) (by omega) (by omega)))))
          |>.mono (by omega) ?_
        rintro c' ⟨hacc', hk, hm⟩
        refine ⟨hacc', fun r hr1 hr2 hr3 => ?_, ?_, fun a ha => ?_⟩
        · rw [hk r (by omega), k2' r hr1 (by omega) hr3]; grind
        · rw [hk ALLOC (by omega_nf)]; omega
        · rw [hm, hm₂ a (by omega)]; grind
      · -- keep
        rw [k0₂] at hc
        have hge : ¬ τ < τa := fun h' => by
          have := (hbit.2.2 (hb'.2 h')); omega
        refine (IRS.ifF (by omega) (IRS.skip (K := 8) hI₂ ?_)).mono (by omega)
          (fun _ h => h)
        refine ⟨⟨?_, fun h0 => ?_, fun _ => ⟨τa, Set.mem_insert_of_mem _ hτa, fun τ' hτ' => ?_, ?_⟩⟩,
          fun r hr1 hr2 hr3 => ?_, hal₁.trans hal₂, fun a ha => by rw [hm₂ a (by omega)]; grind⟩
        · rw [keep2 A (by omega) (by omega) (by omega), a0]; exact hacc.1
        · rw [keep2 A (by omega) (by omega) (by omega), a0, hf1] at h0; omega
        · rcases hτ' with rfl | hτ'
          · grind
          · exact hmin τ' hτ'
        · have r1 : c₂.nreg (A + 1) = c.nreg (A + 1) := by
            rw [keep2 _ (by omega) (by omega) (by omega)]; grind
          have r2 : c₂.nreg (A + 2) = c.nreg (A + 2) := by
            rw [keep2 _ (by omega) (by omega) (by omega)]; grind
          have r3 : c₂.nreg (A + 3) = c.nreg (A + 3) := by
            rw [keep2 _ (by omega) (by omega) (by omega)]; grind
          rw [r1, r2, r3]
          refine ⟨htagA, hppA, heA, hposA, absRec_transport hrecA ?_ ?_ ?_ ?_⟩
          · rw [keep2 _ (by omega) (by omega) (by omega)]; grind
          · rw [keep2 _ (by omega) (by omega) (by omega), show A + 4 + 1 = A + 5 by omega]
            grind
          · rw [keep2 _ (by omega) (by omega) (by omega), show A + 4 + 2 = A + 6 by omega]
            grind
          · rw [keep2 _ (by omega) (by omega) (by omega), show A + 4 + 3 = A + 7 by omega]
            grind
        · rw [k2' r hr1 (by omega) hr3]; grind
    -- the direction
    have hfneg : σ = -1 → ∀ x₁ x₂ : ℝ, AbsRec P c₁ (A + 4) x₁ R₀ → AbsRec P c₁ (A + 8) x₂ R₀ →
        (x₁ < x₂ ↔ τ < τa) := by
      intro hs x₁ x₂ h₁ h₂
      have e₁ := absRec_val h₁ hrecA₁
      have e₂ := absRec_val h₂ hrec₁
      rw [e₁, e₂, Chazelle.Visibility.rayPt_fst, Chazelle.Visibility.rayPt_fst, hs]; constructor <;> intro h <;> linarith
    have hfpos : σ = 1 → ∀ x₁ x₂ : ℝ, AbsRec P c₁ (A + 8) x₁ R₀ → AbsRec P c₁ (A + 4) x₂ R₀ →
        (x₁ < x₂ ↔ τ < τa) := by
      intro hs x₁ x₂ h₁ h₂
      have e₁ := absRec_val h₁ hrec₁
      have e₂ := absRec_val h₂ hrecA₁
      rw [e₁, e₂, Chazelle.Visibility.rayPt_fst, Chazelle.Visibility.rayPt_fst, hs]; constructor <;> intro h <;> linarith
    refine (IRS.ifF hf ?_).mono (K := 269 + 10 + 4 + 2) (by omega) (fun _ h => h)
    by_cases hd0 : c₁.nreg dR < c₁.nreg K1
    · have hs : σ = -1 := by rw [hσ]; apply dirOf_eq_neg; omega
      exact (IRS.ifT hd0 (cmp _ _ (Or.inl ⟨rfl, rfl⟩) (hfneg hs))).mono (by omega) (fun _ h => h)
    · refine (IRS.ifF hd0 ?_).mono (K := 269 + 10 + 4) (by omega) (fun _ h => h)
      by_cases hd1 : c₁.nreg K1 < c₁.nreg dR
      · have hs : σ = -1 := by rw [hσ]; apply dirOf_eq_neg; omega
        exact IRS.ifT hd1 (cmp _ _ (Or.inl ⟨rfl, rfl⟩) (hfneg hs))
      · have hs : σ = 1 := by rw [hσ]; apply dirOf_eq_one; omega
        exact IRS.ifF hd1 (cmp _ _ (Or.inr ⟨rfl, rfl⟩) (hfpos hs))

/-! ## Filtered offers -/

/-- A point of the chain or of the boundary of its box. -/
def OnCB (C : Chain) (x : Point) : Prop :=
  x ∈ C.set ∨ |x.1| = C.radius ∨ |x.2| = C.radius

/-- **A walk position off the open slit** is a point of the chain or of the box boundary. -/
theorem walk_pos_good (C : Chain) (Q : Polygon) {n : ℕ} {x : WPos}
    (he : x.edge < (chainModel C).W.n) (hp : ProperPos (chainModel C) Q n x) (h5 : x.edge ≠ 5)
    (hs : x.edge = 2 * C.m + 6 → (chainModel C).param Q x = 0) :
    OnCB C ((chainModel C).pos Q x) := by
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hpos : (chainModel C).pos Q x = sidePt (C.sideWalk C.sideBeta) x.edge
      ((chainModel C).param Q x) := rfl
  set t := (chainModel C).param Q x
  have hR := C.radius_pos
  obtain ⟨b0, b1, b2, b3, b4, -, -⟩ := C.sidePt_box C.sideBeta t
  rcases (by omega : x.edge = 0 ∨ x.edge = 1 ∨ x.edge = 2 ∨ x.edge = 3 ∨ x.edge = 4 ∨
    6 ≤ x.edge) with h | h | h | h | h | h
  · right; grind
  · right; grind
  · right; grind
  · right; grind
  · right; grind
  · left
    rw [hpos, show x.edge = (x.edge - 6) + 6 by omega]
    exact C.sideWalk_tour_pt_mem C.sideBeta (by omega) (fun h' => hs (by omega)) hp.1 hp.2.1

/-- **A filtered offer**: the position `(e, h)` is normalised in place (bits at `o`); positions on
the slit edge `5` and on the slit edge `2m + 6` with a positive parameter are dropped (they are
above the top of the chain); the others are offered.  `nR` holds the walk length `2m + 7`. -/
def offerF (A dsc e h t dR nR o : ℕ) : Stmt :=
  .seq (normS dsc e h o)
    (.ifLtN e K5 (offer A dsc e h t dR)
      (.ifLtN K5 e
        (.seq (.instr (.addN o e K1))
          (.ifLtN o nR (offer A dsc e h t dR)
            (.ifLtN nR o (offer A dsc e h t dR)
              (.ifLtN K0 h .skip (offer A dsc e h t dR)))))
        .skip))

/-- The cost of a filtered offer. -/
def offerFK : ℕ := 11015 + offerK + 20

/-- Points of the slit edges with a positive parameter are above the top. -/
theorem slit_above (C : Chain) (Q : Polygon) {n : ℕ} {x : WPos}
    (hp : ProperPos (chainModel C) Q n x)
    (h : x.edge = 5 ∨ (x.edge = 2 * C.m + 6 ∧ 0 < (chainModel C).param Q x)) :
    C.top.2 < ((chainModel C).pos Q x).2 := by
  have hpos : (chainModel C).pos Q x = sidePt (C.sideWalk C.sideBeta) x.edge
      ((chainModel C).param Q x) := rfl
  set t := (chainModel C).param Q x
  have hT := C.top_snd_lt_radius
  obtain ⟨-, -, -, -, -, b5, b6⟩ := C.sidePt_box C.sideBeta t
  rcases h with h | ⟨h, ht⟩
  · rw [hpos, h, b5]; simp only
    have : 0 < (1 - t) * (C.radius - C.top.2) := mul_pos (by linarith [hp.2.1]) (by linarith)
    nlinarith
  simp_all

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **A filtered offer.** -/
theorem offerF_irs {A dsc e h t dR nR o : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {z : Point}
    {L : Set ℝ} {τ : ℝ} (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hW3 : P.n + 3 ≤ W)
    (hA : 240700 ≤ A ∧ A + 12 < 250000)
    (hregs : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240700 ≤ e ∧ e < 250000 ∧ 240700 ≤ h ∧
      h < 250000 ∧ 240000 ≤ t ∧ t < 250000 ∧ 240000 ≤ dR ∧ dR < 250000 ∧ 240000 ≤ nR ∧
      nR < 250000 ∧ 240700 ≤ o ∧ o + 1 < 250000)
    (hdist : e ≠ h ∧ o ≠ e ∧ o ≠ h ∧ o + 1 ≠ e ∧ o + 1 ≠ h ∧ o ≠ t ∧ o ≠ dR ∧ o ≠ nR ∧
      h ≠ t ∧ h ≠ dR ∧ h ≠ nR ∧ o ≠ dsc ∧ h ≠ dsc ∧ o + 1 ≠ t ∧ o + 1 ≠ dR ∧ o + 1 ≠ nR ∧
      o + 1 ≠ dsc)
    (hout : (dsc < A ∨ A + 12 < dsc) ∧ (e < A ∨ A + 12 < e) ∧ (h < A ∨ A + 12 < h) ∧
      (t < A ∨ A + 12 < t) ∧ (dR < A ∨ A + 12 < dR) ∧ (o + 1 < A ∨ A + 12 < o))
    (hacc : AccOK P A Mod R₀ z (dirOf (c.nreg dR)) L c)
    (htag : c.nreg t ≤ 2) (hctx : ChainCtx P W c dsc (Mod (c.nreg t)))
    (hR : (Mod (c.nreg t)).radius = R₀) (hn : c.nreg nR = 2 * (Mod (c.nreg t)).m + 7)
    (he : c.nreg e < (chainModel (Mod (c.nreg t))).W.n)
    (hpp : ProperPos (chainModel (Mod (c.nreg t))) (Qof P) P.n ⟨c.nreg e, c.nreg h⟩)
    (hpos : (chainModel (Mod (c.nreg t))).pos (Qof P) ⟨c.nreg e, c.nreg h⟩ =
      rayPt z (dirOf (c.nreg dR)) τ)
    (hy : |z.2| < R₀) (hroom : c.nreg ALLOC + offerFK ≤ W) :
    IRS P W c₀ (offerF A dsc e h t dR nR o) c offerFK (fun c' =>
      (∃ L', AccOK P A Mod R₀ z (dirOf (c.nreg dR)) L' c' ∧
        (L' = L ∨ (L' = insert τ L ∧ OnCB (Mod (c.nreg t)) (rayPt z (dirOf (c.nreg dR)) τ))) ∧
        (z.2 ≤ (Mod (c.nreg t)).top.2 → L' = insert τ L)) ∧
      (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ h → r ≠ o → r ≠ o + 1 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  set σ := dirOf (c.nreg dR) with hσ
  set C := Mod (c.nreg t) with hCdef
  have nob : ∀ r, 240000 ≤ r → r < 250000 → bandOf r ∉ oracleBands := fun r h1 h2 =>
    not_oracle_sw h1 h2
  -- normalise
  refine IRS.seq (K₁ := 11015) (K₂ := offerK + 20) (normS_exact (normS_irs (dsc := dsc) (pe := e) (ph := h) (o := o)
    hI (hK.fix hI) hctx ⟨hregs.1, hregs.2.1, hregs.2.2.1, hregs.2.2.2.1, hregs.2.2.2.2.1,
      hregs.2.2.2.2.2.1⟩
    ⟨hregs.2.2.2.2.2.2.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.2.2.2.2.2.2, hdist.2.1, hdist.2.2.1,
      hdist.2.2.2.1, hdist.2.2.2.2.1, hdist.1⟩ he hpp
    (fun _ _ _ _ => by rw [hpos, hR]; exact hy) (by omega_nf))
    ⟨by omega, by omega⟩) ?_ |>.mono (by omega_nf) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨n1e, n1h, k1, -, -⟩, hal1, hm1⟩
  have keep1 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ h → r ≠ o → r ≠ o + 1 →
      c₁.nreg r = c.nreg r := fun r a1 a2 a3 a4 a5 => k1 r (nob r a1 a2) a3 a4 a5
        (by omega_nf)
  have t1 := keep1 t hregs.2.2.2.2.2.2.1 hregs.2.2.2.2.2.2.2.1 (Ne.symm hdist.2.2.2.2.2.2.2.2.1)
    (Ne.symm hdist.2.2.2.2.2.1) (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have d1 := keep1 dR hregs.2.2.2.2.2.2.2.2.1 hregs.2.2.2.2.2.2.2.2.2.1
    (Ne.symm hdist.2.2.2.2.2.2.2.2.2.1) (Ne.symm hdist.2.2.2.2.2.2.1)
    (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have nR1 := keep1 nR hregs.2.2.2.2.2.2.2.2.2.2.1 hregs.2.2.2.2.2.2.2.2.2.2.2.1
    (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.1) (Ne.symm hdist.2.2.2.2.2.2.2.1)
    (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have ds1 := keep1 dsc hregs.1 hregs.2.1 (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.1) (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have a1 : ∀ j, j ≤ 12 → c₁.nreg (A + j) = c.nreg (A + j) := fun j hj =>
    keep1 _ (by omega) (by omega) (by omega)
      (by omega) (by omega)
  -- the normalised position
  set u : WPos := ⟨c.nreg e, c.nreg h⟩ with hu
  obtain ⟨hNP, hue, hup, -, hcase⟩ := Restore.normOf_facts hpp
  have hu1 : (⟨c₁.nreg e, c₁.nreg h⟩ : WPos) = Restore.normOf (chainModel C) (Qof P) u := by
    rw [n1e, n1h]; unfold nhgt
    rcases hn' : Restore.normOf (chainModel C) (Qof P) u with ⟨e', h'⟩
    grind
  have hpp1 : ProperPos (chainModel C) (Qof P) P.n ⟨c₁.nreg e, c₁.nreg h⟩ := by ram_grind
  have hpos1 : (chainModel C).pos (Qof P) ⟨c₁.nreg e, c₁.nreg h⟩ = rayPt z σ τ := by
    grind
  have he1 : c₁.nreg e < (chainModel C).W.n := by omega
  have hcase1 : c₁.nreg h = 0 ∨ 0 < (chainModel C).param (Qof P) ⟨c₁.nreg e, c₁.nreg h⟩ := by
    grind
  have hacc1 : AccOK P A Mod R₀ z σ L c₁ := by
    obtain ⟨f1, f2, f3⟩ := hacc
    have a0 : c₁.nreg A = c.nreg A := by grind
    refine ⟨by omega, fun h0 => f2 (by omega), fun h1 => ?_⟩
    obtain ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, hrecA⟩ := f3 (by omega)
    rw [a1 1 (by norm_num), a1 2 (by norm_num), a1 3 (by norm_num)]
    exact ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, absRec_transport hrecA (a1 4 (by norm_num))
      (by grind)
      (by grind)
      (by grind)⟩
  have hctx1 : ChainCtx P W c₁ dsc C := hctx.transport ds1 (fun a _ => by rw [hm1]) hal1.ge
  have hm : C.m = (Mod (c.nreg t)).m := rfl
  -- offering at a configuration with the same facts
  have doOffer : ∀ c₂ : Config, IInv W c₀ c₂ → c₂.nreg e = c₁.nreg e → c₂.nreg h = c₁.nreg h →
      c₂.nreg t = c.nreg t → c₂.nreg dR = c.nreg dR → c₂.nmem = c₁.nmem →
      c₂.nreg ALLOC = c₁.nreg ALLOC → (∀ j, j ≤ 12 → c₂.nreg (A + j) = c₁.nreg (A + j)) →
      ChainCtx P W c₂ dsc C → c₂.nreg ALLOC + offerK ≤ W →
      OnCB C (rayPt z σ τ) →
      IRS P W c₀ (offer A dsc e h t dR) c₂ offerK (fun c' =>
        (∃ L', AccOK P A Mod R₀ z σ L' c' ∧
          (L' = L ∨ (L' = insert τ L ∧ OnCB C (rayPt z σ τ))) ∧
          (z.2 ≤ C.top.2 → L' = insert τ L)) ∧
        (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ ALLOC →
          c'.nreg r = c₂.nreg r) ∧
        c₂.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c₂.nreg ALLOC → c'.nmem a = c₂.nmem a)) := by
    intro c₂ hI₂ e2 h2 t2 d2 m2 al2 a2 hctx2 hroom2 hgood
    have hacc2 : AccOK P A Mod R₀ z (dirOf (c₂.nreg dR)) L c₂ := by
      obtain ⟨f1, f2, f3⟩ := hacc1
      have a0 : c₂.nreg A = c₁.nreg A := by simpa using a2 0 (by norm_num)
      rw [d2]
      refine ⟨by omega, fun h0 => f2 (by omega), fun h1 => ?_⟩
      obtain ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, hrecA⟩ := f3 (by omega)
      rw [a2 1 (by norm_num), a2 2 (by norm_num), a2 3 (by norm_num)]
      exact ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, absRec_transport hrecA (a2 4 (by norm_num))
        (by grind)
        (by grind)
        (by grind)⟩
    refine (offer_irs (L := L) (τ := τ) (Mod := Mod) hI₂ hK hG hW3 hA
      ⟨hregs.1, hregs.2.1, by omega, hregs.2.2.2.1, by omega, hregs.2.2.2.2.2.1,
        hregs.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.2.1,
        hregs.2.2.2.2.2.2.2.2.2.1⟩
      ⟨hout.1, hout.2.1, hout.2.2.1, hout.2.2.2.1, hout.2.2.2.2.1⟩ hacc2 (by omega)
      (by grind) (by grind) (by grind)
      (by grind) (by grind) hy hroom2).mono
      le_rfl ?_
    grind
  have k5 : c₁.nreg K5 = 5 := (hK.fix hI₁).2.2.2.2.1
  have k1₁ : c₁.nreg K1 = 1 := (hK.fix hI₁).2.1
  have hnW : 2 * C.m + 7 ≤ W := hctx.2.2.2.2.2
  have hn' : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hz2 : (rayPt z σ τ).2 = z.2 := rfl
  -- dropping a point above the top
  have drop : ∀ c₂ : Config, IInv W c₀ c₂ → c.nreg ALLOC ≤ c₂.nreg ALLOC →
      (∀ a, a < c.nreg ALLOC → c₂.nmem a = c.nmem a) →
      (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ h → r ≠ o → r ≠ o + 1 →
        r ≠ ALLOC → c₂.nreg r = c.nreg r) →
      (∀ j, j ≤ 12 → c₂.nreg (A + j) = c₁.nreg (A + j)) →
      C.top.2 < z.2 → ∀ K, IRS P W c₀ .skip c₂ K (fun c' =>
        (∃ L', AccOK P A Mod R₀ z σ L' c' ∧
          (L' = L ∨ (L' = insert τ L ∧ OnCB C (rayPt z σ τ))) ∧ (z.2 ≤ C.top.2 → L' = insert τ L)) ∧
        (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ h → r ≠ o → r ≠ o + 1 →
          r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
    intro c₂ hI₂ hal hmm hk a2 habove K
    refine IRS.skip hI₂ ⟨⟨L, ?_, Or.inl rfl, fun h' => absurd h' (not_le.2 habove)⟩, hk, hal, hmm⟩
    obtain ⟨f1, f2, f3⟩ := hacc1
    have a0 : c₂.nreg A = c₁.nreg A := by simpa using a2 0 (by norm_num)
    refine ⟨by omega, fun h0 => f2 (by omega), fun h1 => ?_⟩
    obtain ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, hrecA⟩ := f3 (by omega)
    rw [a2 1 (by norm_num), a2 2 (by norm_num), a2 3 (by norm_num)]
    exact ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, absRec_transport hrecA (a2 4 (by norm_num))
      (by rw [show A + 4 + 1 = A + 5 by omega]; exact a2 5 (by norm_num))
      (by rw [show A + 4 + 2 = A + 6 by omega]; exact a2 6 (by norm_num))
      (by rw [show A + 4 + 3 = A + 7 by omega]; exact a2 7 (by norm_num))⟩
  -- the frame of `c₁`
  have fr1 : ∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ h → r ≠ o → r ≠ o + 1 →
      r ≠ ALLOC → c₁.nreg r = c.nreg r := fun r a1 _ a3 a4 a5 a6 => k1 r a1 a3 a4 a5 a6
  have hm1' : ∀ a, a < c.nreg ALLOC → c₁.nmem a = c.nmem a := fun a _ => by rw [hm1]
  -- finishing an offer
  have fin : ∀ c₂ c' : Config, (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ h →
      r ≠ o → r ≠ o + 1 → r ≠ ALLOC → c₂.nreg r = c.nreg r) →
      c.nreg ALLOC ≤ c₂.nreg ALLOC → (∀ a, a < c.nreg ALLOC → c₂.nmem a = c.nmem a) →
      (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ ALLOC →
          c'.nreg r = c₂.nreg r) → c₂.nreg ALLOC ≤ c'.nreg ALLOC →
      (∀ a, a < c₂.nreg ALLOC → c'.nmem a = c₂.nmem a) →
      (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ h → r ≠ o → r ≠ o + 1 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :=
    fun c₂ c' h2 a2 m2 h' a' m' => ⟨fun r b1 b2 b3 b4 b5 b6 => (h' r b1 b2 b6).trans
      (h2 r b1 b2 b3 b4 b5 b6), a2.trans a', fun a ha => (m' a (by omega)).trans (m2 a ha)⟩
  by_cases hlt5 : c₁.nreg e < c₁.nreg K5
  · -- a box edge below `5`
    rw [k5] at hlt5
    refine (IRS.ifT (by omega) ((doOffer c₁ hI₁ rfl rfl t1 d1 rfl rfl (fun _ _ => rfl)
      hctx1 (by rw [hal1]; unfold offerFK at hroom; omega) ?_).mono le_rfl ?_)).mono
      (by omega) (fun _ h => h)
    · rw [← hpos1]
      exact walk_pos_good C (Qof P) he1 hpp1 (by show c₁.nreg e ≠ 5; omega)
        (fun h' => by change c₁.nreg e = 2 * C.m + 6 at h'; omega)
    · rintro c' ⟨hL', hk', ha', hm'⟩
      exact ⟨hL', fin c₁ c' fr1 hal1.ge hm1' hk' ha' hm'⟩
  · refine IRS.ifF hlt5 ?_ |>.mono (K := offerK + 18) (by omega) (fun _ h => h)
    rw [k5] at hlt5
    by_cases hgt5 : c₁.nreg K5 < c₁.nreg e
    · rw [k5] at hgt5
      refine IRS.ifT (by omega) ?_ |>.mono (K := offerK + 16) (by omega) (fun _ h => h)
      have hok : c₁.nreg e + c₁.nreg K1 ≤ W := by omega
      refine IRS.seq (IRS.reg hI₁ (iscr_sw hregs.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega))
        (Exec.addN hI₁.hw o e K1 hok)) ?_ |>.mono (K := 1 + (offerK + 8)) (by omega) (fun _ h => h)
      rintro c₂ hI₂ hA₂ hA₂' rfl
      have u : ∀ r, r ≠ o → (upd c₁.nreg o (c₁.nreg e + c₁.nreg K1)) r = c₁.nreg r := fun r hr =>
        upd_other _ _ _ hr
      have e2 := u e (Ne.symm hdist.2.1)
      have h2 := u h (Ne.symm hdist.2.2.1)
      have t2 := (u t (Ne.symm hdist.2.2.2.2.2.1)).trans t1
      have d2 := (u dR (Ne.symm hdist.2.2.2.2.2.2.1)).trans d1
      have n2 := (u nR (Ne.symm hdist.2.2.2.2.2.2.2.1)).trans nR1
      have al2 := u ALLOC (by unfold ALLOC; omega)
      have a2 : ∀ j, j ≤ 12 → (upd c₁.nreg o (c₁.nreg e + c₁.nreg K1)) (A + j) = c₁.nreg (A + j) :=
        fun j hj => u _ (by omega)
      have hctx2 : ChainCtx P W { c₁ with nreg := upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) } dsc C :=
        hctx1.transport (u dsc (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.1)) (fun _ _ => rfl) al2.ge
      have fr2 : ∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ h → r ≠ o →
          r ≠ o + 1 → r ≠ ALLOC → (upd c₁.nreg o (c₁.nreg e + c₁.nreg K1)) r = c.nreg r :=
        fun r b1 b2 b3 b4 b5 b6 => (u r b4).trans (fr1 r b1 b2 b3 b4 b5 b6)
      have off2 : OnCB C (rayPt z σ τ) → IRS P W c₀ (offer A dsc e h t dR)
          { c₁ with nreg := upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) } offerK _ := fun hg =>
        doOffer _ hI₂ e2 h2 t2 d2 rfl al2 a2 hctx2 (by
          show upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) ALLOC + offerK ≤ W
          rw [al2, hal1]; unfold offerFK at hroom; omega) hg
      have alg : c.nreg ALLOC ≤ ({ c₁ with nreg := upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) } :
          Config).nreg ALLOC := by
        omega
      have finish : ∀ c' : Config, (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ ALLOC →
          c'.nreg r = upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) r) →
          upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) ALLOC ≤ c'.nreg ALLOC →
          (∀ a, a < upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) ALLOC → c'.nmem a = c₁.nmem a) →
          (∀ r, bandOf r ∉ oracleBands → (r < A ∨ A + 12 < r) → r ≠ h → r ≠ o → r ≠ o + 1 →
            r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
          c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :=
        fun c' h' a' m' => fin { c₁ with nreg := upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) } c' fr2
          alg hm1' h' a' m'
      by_cases hb1 : upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) o < upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) nR
      · rw [upd_same, n2, hn, k1₁] at hb1
        refine IRS.ifT (by simp only; rw [upd_same, n2, hn, k1₁]; exact hb1)
          ((off2 ?_).mono le_rfl ?_) |>.mono (by omega) (fun _ h => h)
        · rw [← hpos1]
          exact walk_pos_good C (Qof P) he1 hpp1 (by show c₁.nreg e ≠ 5; omega)
            (fun h' => by change c₁.nreg e = 2 * C.m + 6 at h'; omega)
        · rintro c' ⟨hL', hk', ha', hm'⟩
          exact ⟨hL', finish c' hk' ha' hm'⟩
      · refine IRS.ifF (by omega) ?_ |>.mono
          (K := offerK + 6) (by omega) (fun _ h => h)
        rw [upd_same, n2, hn, k1₁] at hb1
        by_cases hb2 : upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) nR < upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) o
        · rw [upd_same, n2, hn, k1₁] at hb2
          omega
        · refine IRS.ifF (by omega) ?_ |>.mono
            (K := offerK + 4) (by omega) (fun _ h => h)
          rw [upd_same, n2, hn, k1₁] at hb2
          have hlast : c₁.nreg e = 2 * C.m + 6 := by omega
          have k0₂ : upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) K0 = 0 := by
            rw [u K0 (by unfold K0 sw; omega)]; exact (hK.fix hI₁).1
          by_cases hb3 : upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) K0 < upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) h
          · -- drop: above the top
            rw [k0₂, h2] at hb3
            have hpar : 0 < (chainModel C).param (Qof P) ⟨c₁.nreg e, c₁.nreg h⟩ :=
              hcase1.resolve_left (by omega)
            have habove := slit_above C (Qof P) hpp1 (Or.inr ⟨hlast, hpar⟩)
            rw [hpos1, hz2] at habove
            refine IRS.ifT (by simp only; omega)
              (drop _ hI₂ alg hm1' fr2 a2 habove offerK)
          · refine IRS.ifF (by omega)
              ((off2 ?_).mono (by omega) ?_)
            · rw [k0₂, h2] at hb3
              rw [← hpos1]
              exact walk_pos_good C (Qof P) he1 hpp1 (by show c₁.nreg e ≠ 5; omega) (fun _ => by
                show (chainModel C).param (Qof P) ⟨c₁.nreg e, c₁.nreg h⟩ = 0
                rw [show c₁.nreg h = 0 by omega]; rfl)
            · rintro c' ⟨hL', hk', ha', hm'⟩
              exact ⟨hL', finish c' hk' ha' hm'⟩
    · -- the slit edge `5`: drop
      rw [k5] at hgt5
      have h5 : c₁.nreg e = 5 := by omega
      have habove := slit_above C (Qof P) hpp1 (Or.inl h5)
      rw [hpos1, hz2] at habove
      exact IRS.ifF (by omega) (drop c₁ hI₁ hal1.ge hm1' fr1 (fun _ _ => rfl) habove _)

/-! ## Transport -/

/-- **The accumulator survives** a step keeping its block. -/
theorem AccOK.transport {A : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {z : Point} {σ : ℝ} {L : Set ℝ}
    {c c' : Config} (h : AccOK P A Mod R₀ z σ L c) (hr : ∀ j, j ≤ 12 → c'.nreg (A + j) = c.nreg (A + j)) :
    AccOK P A Mod R₀ z σ L c' := by
  obtain ⟨f1, f2, f3⟩ := h
  have a0 : c'.nreg A = c.nreg A := by simpa using hr 0 (by norm_num)
  refine ⟨by omega, fun h0 => f2 (by omega), fun h1 => ?_⟩
  obtain ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, hrecA⟩ := f3 (by omega)
  rw [hr 1 (by norm_num), hr 2 (by norm_num), hr 3 (by norm_num)]
  exact ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, absRec_transport hrecA (hr 4 (by norm_num))
    (by grind)
    (by grind)
    (by grind)⟩

end

end SweepIo

end Chazelle.Core
