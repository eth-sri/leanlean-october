module

public import Chazelle.Core.RestoreTShot
public import Chazelle.Core.RestoreTShotMath
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics

/-!
# WP-E, the candidate test on the RAM: runs with the oracle bands

The run steps of the candidate test (`RS`) stay in the bands `dBands` of the restoration.  The
shot calls the shooter, which writes in the caller's oracle bands `Bo`; `RSB B` is `RS` with the
relative frame of an arbitrary band set `B` (in the test, `dBands ∪ Bo`).

* `RSB.of_RS`, `RSB.seq`, `RSB.ifT`, `RSB.ifF`, `RSB.skip`, `RSB.mono`: the combinators.
* `KeyG.mono`, `XG.mono`: the operation contracts allow a larger cost bound.
* `shot_rsb`: the shot of the test (`shotListG gKey xcR sh RS0`) as a run step: the wrapper's
  postcondition, and the band `bRestore` below the shot block unchanged.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK NFLoc ShotList ShotListG

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **A run step in the bands `B`.** -/
def RSB (B : Finset ℕ) (P : Polygon) (W : ℕ) (c₀ : Config) (s : Stmt) (c : Config) (K : ℕ)
    (Q : Config → Prop) : Prop :=
  ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ TInv W c₀ c' ∧ RF B (c₀.nreg ALLOC) c c' k ∧ Q c'

theorem RSB.of_RS {B : Finset ℕ} (hB : dBands ⊆ B) {s : Stmt} {K : ℕ} {Q : Config → Prop}
    (h : RS P W c₀ s c K Q) : RSB B P W c₀ s c K Q := by
  obtain ⟨c', k, ex, hk, hI, hrf, hq⟩ := h
  exact ⟨c', k, ex, hk, hI, hrf.mono hB le_rfl, hq⟩

theorem RSB.mono {B : Finset ℕ} {s : Stmt} {K K' : ℕ} {Q Q' : Config → Prop}
    (h : RSB B P W c₀ s c K Q) (hK : K ≤ K') (hQ : ∀ c', Q c' → Q' c') : RSB B P W c₀ s c K' Q' := by
  obtain ⟨c', k, ex, hk, hI, hrf, hq⟩ := h
  exact ⟨c', k, ex, by omega, hI, hrf, hQ c' hq⟩

theorem RSB.seq {B : Finset ℕ} {s t : Stmt} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop}
    (h₁ : RSB B P W c₀ s c K₁ Q₁)
    (h₂ : ∀ c₁, TInv W c₀ c₁ → c₁.nreg ALLOC ≤ c.nreg ALLOC + K₁ → Q₁ c₁ →
      RSB B P W c₀ t c₁ K₂ Q₂) : RSB B P W c₀ (.seq s t) c (K₁ + K₂) Q₂ := by
  obtain ⟨c₁, k₁, e₁, hk₁, hI₁, hrf₁, hq₁⟩ := h₁
  obtain ⟨c', k₂, e₂, hk₂, hI', hrf₂, hq⟩ := h₂ c₁ hI₁ (by have := hrf₁.2.2.2.2.2.2; omega) hq₁
  exact ⟨c', k₁ + k₂, .seq e₁ e₂, by omega, hI', hrf₁.trans hrf₂, hq⟩

theorem RSB.ifT {B : Finset ℕ} {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : c.nreg a < c.nreg b) (h : RSB B P W c₀ t c K Q) :
    RSB B P W c₀ (.ifLtN a b t e) c (K + 2) Q := by
  obtain ⟨c', k, ex, hk, hI, hrf, hq⟩ := h
  exact ⟨c', k + 1, .ifLtN_true ht ex, by omega, hI, hrf.mono subset_rfl (by omega), hq⟩

theorem RSB.ifF {B : Finset ℕ} {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : ¬ c.nreg a < c.nreg b) (h : RSB B P W c₀ e c K Q) :
    RSB B P W c₀ (.ifLtN a b t e) c (K + 2) Q := by
  obtain ⟨c', k, ex, hk, hI, hrf, hq⟩ := h
  exact ⟨c', k + 2, .ifLtN_false ht ex, by omega, hI, hrf.mono subset_rfl (by omega), hq⟩

theorem RSB.skip {B : Finset ℕ} {K : ℕ} {Q : Config → Prop} (hI : TInv W c₀ c) (hq : Q c) :
    RSB B P W c₀ .skip c K Q :=
  ⟨c, 0, .skip hI.hw, by omega, hI, RF.refl c 0, hq⟩

/-! ## Larger cost bounds -/

theorem KeyG.mono {M : Model} {R : ℕ} {E : Config → Prop} {kc : ℕ → ℕ → ℕ → ℕ → Stmt}
    {Bk : ℕ → Bool} {K K' : ℕ} (h : KeyG P W M R E kc Bk K) (hK : K ≤ K') :
    KeyG P W M R E kc Bk K' := by
  intro a b d e ha hb hd he c hw hctx hx hxe hx0 hy hye hy0 hroom
  obtain ⟨c', k, ex, hk, b1, f⟩ := h a b d e ha hb hd he c hw hctx hx hxe hx0 hy hye hy0
    (by omega)
  exact ⟨c', k, ex, by omega, b1, f⟩

theorem XG.mono {M : Model} {R : ℕ} {E : Config → Prop} {Y : ℝ → Prop}
    {xc : ℕ → ℕ → ℕ → ℕ → Stmt} {Bx : ℕ → Bool} {K K' : ℕ} (h : XG P W M R E Y xc Bx K)
    (hK : K ≤ K') : XG P W M R E Y xc Bx K' := by
  intro a b d e ha hb hd he c hw hctx hp1 he1 hp2 he2 hyy hY hroom
  obtain ⟨c', k, ex, hk, b1, f⟩ := h a b d e ha hb hd he c hw hctx hp1 he1 hp2 he2 hyy hY
    (by omega)
  exact ⟨c', k, ex, by omega, b1, f⟩

/-! ## The shot -/

/-- The cost bound of the operations of the test's shot. -/
def shK : ℕ := 34000

/-- **The shot of the candidate test** as a run step: the wrapper's postcondition; the band
`bRestore` below the shot block is unchanged. -/
theorem shot_rsb {M : Model} {N : NF} {X : MemCtx} {Ok : Polygon → Model → Prop}
    {sh : Stmt} {Bs Bo : Finset ℕ} {F : ℕ → ℕ} (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo) (hXl : X.CapLocal) (hB8 : bRestore ∉ Bo)
    (hBo : oracleBands ⊆ Bo) (hpre : ShotPreG X Ok RS0 P W M (TInv W c₀) (YR M) c)
    (hroom : c.nreg ALLOC + shotCostG (F (c.nreg 84007)) shK (c.nreg 84002) ≤ W) :
    RSB (dBands ∪ Bo) P W c₀ (shotListG gKey xcR sh RS0) c
      (shotCostG (F (c.nreg 84007)) shK (c.nreg 84002))
      (fun c' => ShotPost RS0 P c c' ∧ ∀ q, 80000 ≤ q → q < 84000 → c'.nreg q = c.nreg q) := by
  have hRB : bandOf RS0 ∉ Bo := by rwx [band8 (by ufo RS0) (by ufo RS0)]
  obtain ⟨c', k, ex, hk, hpost, fT⟩ := shotListG_execR hsh hBs hXl regsOK_RS0 hRB hBo
    (stable_tinv hB8) (KeyG.mono (gKey_keyG hE) (by ufo shK)) opW_BgK
    (XG.mono (xcR_xG hE) (by ufo shK)) opW_BxR c hI.hw hpre hroom
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := fT
  have keep : ∀ q, 80000 ≤ q → q < 84000 → c'.nreg q = c.nreg q := fun q h1 h2 =>
    r₁ q (by rwx [band8 h1 (by omega)]) (by ufo ALLOC) (by ufo RS0)
  have hI' : TInv W c₀ c' := by
    refine ⟨ex.wb_right, fun q h1 h2 => by rw [keep q h1 (by omega)]; exact hI.hin q h1 h2,
      le_trans hI.hA a₁, fun a ha => by rw [m₁ a (by have := hI.hA; omega)]; exact hI.hm a ha,
      by rw [keep _ (by norm_num) (by norm_num)]; exact hI.h20,
      by rw [keep _ (by norm_num) (by norm_num)]; exact hI.h21,
      by rw [keep _ (by norm_num) (by norm_num)]; exact hI.h22,
      by rw [keep _ (by norm_num) (by norm_num)]; exact hI.h23⟩
  have hb8 : bRestore ∈ dBands := by decide
  have hblk : ∀ r, (RS0 ≤ r ∧ r < RS0 + 300) → bandOf r ∈ dBands ∪ Bo := by
    intro r h
    unfold RS0 at h
    refine Finset.mem_union_left _ ?_
    rw [band8 (by omega) (by omega)]
    exact hb8
  refine ⟨c', k, ex, hk, hI', ⟨fun r hr ha => r₁ r (fun h => hr (Finset.mem_union_right _ h)) ha
    (fun h => hr (hblk r h)),
    fun r hr => rr₁ r (fun h => hr (Finset.mem_union_right _ h)) (fun h => hr (hblk r h)),
    fun a ha => m₁ a (by have := hI.hA; omega), fun a ha => rm₁ a (by have := hI.hA; omega),
    o₁, a₁, b₁⟩, hpost, keep⟩

end

end Restore

end Chazelle.Core
