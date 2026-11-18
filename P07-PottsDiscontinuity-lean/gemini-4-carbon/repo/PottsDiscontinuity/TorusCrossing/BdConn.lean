module

public import PottsDiscontinuity.TorusCrossing.BaseConn
public import PottsDiscontinuity.TorusCrossing.BdEven
public import PottsDiscontinuity.TorusCrossing.Cochain
public import PottsDiscontinuity.TorusCrossing.Explore

/-!
# The boundary of the exploration is connected

The boundary edges of the explored region separate the class `U` (joined to the row `p₂`) from
the class `X` (the rest).  Suppose they split into two vertex-disjoint parts.  The indicator of one
part is a closed cochain, hence has a primitive `g`; `g` is constant on `U` and on `X` (it is
constant on the two port rows and does not change across non-boundary edges), so it changes by the
same amount across every boundary edge, contradicting that it changes across one part only.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (R : Rect)

theorem mem_expBd_iff {p₁ p₂ : ℤ} {A : Finset Cell} {m : Cell} :
    m ∈ R.expBd p₁ p₂ A ↔
      m ∈ R.inner ∧ IsSep (fun z => z ∈ R.expU p₁ p₂ A) m := by
  unfold expBd IsSep
  rw [Finset.mem_filter, show ∀ P Q : Prop, (P ≠ Q) ↔ (P ↔ ¬ Q) from fun P Q => by
    by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]]

theorem mem_expD_of_faceRow {p₁ : ℤ} {A : Finset Cell} {z : Cell} (hz : z ∈ R.faceRow p₁) :
    z ∈ R.expD p₁ A :=
  Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, z, hz, Relation.ReflTransGen.refl⟩

theorem mem_expU_of_faceRow {p₁ p₂ : ℤ} {A : Finset Cell} {z : Cell}
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A) (hz : z ∈ R.faceRow p₂) :
    z ∈ R.expU p₁ p₂ A :=
  Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, hb z hz, z, hz, hb z hz, Relation.ReflTransGen.refl⟩

theorem faceRow_mem {r : ℤ} {z : Cell} : z ∈ R.faceRow r ↔ z ∈ R.dcells ∧ z.2 = r :=
  Finset.mem_filter

private theorem expBd_cdeg_zero (hh : 0 < R.h) {p₁ p₂ : ℤ} {A : Finset Cell}
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A) {c : Cell} (hc : c ∈ R.pcells)
    (hx1 : R.x0 < c.1) (hx2 : c.1 < R.x0 + R.w) :
    cdeg (ind (R.expBd p₁ p₂ A)) c = 0 := by
  have hcc := mem_cells.1 (mem_pcells.1 hc).1; have hcp := (mem_pcells.1 hc).2
  have hcdeg : cdeg (ind (R.expBd p₁ p₂ A)) c = (((corners c).filter (· ∈ R.expBd p₁ p₂ A)).card : ZMod 2) := by
    rw [card_filter_corners]; unfold cdeg ind; push_cast; simp
  rw [hcdeg, Finset.filter_congr fun m _ => R.mem_expBd_iff]
  have hlbl (r : ℤ) (hr : r = R.y0 ∨ r = R.y0 + R.h) (hy : c.2 = r) :
      ((c.1 - 1, c.2) : Cell) ∈ R.expU p₁ p₂ A ↔ ((c.1 + 1, c.2) : Cell) ∈ R.expU p₁ p₂ A := by
    have hW : ((c.1 - 1, c.2) : Cell) ∈ R.faceRow r := R.faceRow_mem.2 ⟨by
      rw [mem_dcells, mem_cells]; unfold IsPrimal at *; refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega, hy⟩
    have hE : ((c.1 + 1, c.2) : Cell) ∈ R.faceRow r := R.faceRow_mem.2 ⟨by
      rw [mem_dcells, mem_cells]; unfold IsPrimal at *; refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega, hy⟩
    rcases (by omega : r = p₁ ∨ r = p₂) with rfl | rfl
    · exact iff_of_false (fun h => expU_subset_not_expD h (R.mem_expD_of_faceRow hW))
        (fun h => expU_subset_not_expD h (R.mem_expD_of_faceRow hE))
    · exact iff_of_true (R.mem_expU_of_faceRow hb hW) (R.mem_expU_of_faceRow hb hE)
  obtain ⟨k, hk⟩ := sep_deg_even R hh (· ∈ R.expU p₁ p₂ A) c hcp hx1 hx2 hcc.2.2.1 hcc.2.2.2
    (hlbl R.y0 (.inl rfl)) (hlbl (R.y0 + R.h) (.inr rfl))
  rw [hk]; push_cast; exact zmod2_two _

private theorem g_two {f g : Cell → ZMod 2} (hh : 0 < R.h) (hfin : ∀ m, f m ≠ 0 → m ∈ R.inner)
    (hg : ∀ m ∈ R.inner, g (dualEnds m).1 + g (dualEnds m).2 = f m)
    (hclosed : ∀ c : Cell, IsPrimal c → R.x0 < c.1 → c.1 < R.x0 + R.w → cdeg f c = 0)
    {i r : ℤ} (hr : r = R.y0 ∨ r = R.y0 + R.h) (hz : ((i, r) : Cell) ∈ R.dcells)
    (hz' : ((i + 2, r) : Cell) ∈ R.dcells) : g (i, r) = g (i + 2, r) := by
  have hzc := mem_cells.1 (mem_dcells.1 hz).1; have hzc' := mem_cells.1 (mem_dcells.1 hz').1
  have hzp := (mem_dcells.1 hz).2; unfold IsPrimal at hzp
  have hh' : (0 : ℤ) < R.h := by exact_mod_cast hh
  have hcd := hclosed (i + 1, r) (by unfold IsPrimal; dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
  have hzero (m : Cell) (hm : m.2 ≤ R.y0 ∨ R.y0 + R.h < m.2) : f m = 0 := by
    by_contra hne; have := (mem_inner.1 (hfin m hne)); omega
  unfold cdeg at hcd; dsimp only at hcd; rw [show i + 1 + 1 = i + 2 by ring] at hcd
  rcases hr with hr | hr
  · have e3 := hg (i + 1, r + 1) (by rw [mem_inner]; dsimp only; omega)
    have e4 := hg (i + 2, r + 1) (by rw [mem_inner]; dsimp only; omega)
    rw [show dualEnds ((i + 1, r + 1) : Cell) = ((i + 1, r + 1), (i, r)) by
      unfold dualEnds; rw [ite_eq_right (by dsimp only; omega)]; ext <;> simp] at e3
    rw [show dualEnds ((i + 2, r + 1) : Cell) = ((i + 1, r + 1), (i + 2, r)) by
      unfold dualEnds; rw [ite_eq_left (by dsimp only; omega)]; ext <;> simp; ring] at e4
    rw [hzero (i + 1, r) (.inl (by dsimp only; omega)), hzero (i + 2, r) (.inl (by dsimp only; omega)), ← e3, ← e4] at hcd
    dsimp only at hcd
    generalize g (i + 1, r + 1) = N, g (i, r) = W, g (i + 2, r) = E at hcd; revert N W E hcd; decide
  · have e1 := hg (i + 1, r) (by rw [mem_inner]; dsimp only; omega)
    have e2 := hg (i + 2, r) (by rw [mem_inner]; dsimp only; omega)
    rw [show dualEnds ((i + 1, r) : Cell) = ((i, r), (i + 1, r - 1)) by
      unfold dualEnds; rw [ite_eq_left (by dsimp only; omega)]; ext <;> simp] at e1
    rw [show dualEnds ((i + 2, r) : Cell) = ((i + 2, r), (i + 1, r - 1)) by
      unfold dualEnds; rw [ite_eq_right (by dsimp only; omega)]; ext <;> simp; ring] at e2
    rw [hzero (i + 1, r + 1) (.inr (by dsimp only; omega)), hzero (i + 2, r + 1) (.inr (by dsimp only; omega)), ← e1, ← e2] at hcd
    dsimp only at hcd
    generalize g (i + 1, r - 1) = S, g (i, r) = W, g (i + 2, r) = E at hcd; revert S W E hcd; decide

private theorem g_row {f g : Cell → ZMod 2} (hh : 0 < R.h) (hfin : ∀ m, f m ≠ 0 → m ∈ R.inner)
    (hg : ∀ m ∈ R.inner, g (dualEnds m).1 + g (dualEnds m).2 = f m)
    (hclosed : ∀ c : Cell, IsPrimal c → R.x0 < c.1 → c.1 < R.x0 + R.w → cdeg f c = 0)
    {r : ℤ} (hr : r = R.y0 ∨ r = R.y0 + R.h) :
    ∀ n : ℕ, ∀ z z' : Cell, z ∈ R.dcells → z' ∈ R.dcells → z.2 = r → z'.2 = r →
      (z'.1 - z.1).natAbs = 2 * n → g z = g z'
  | 0, z, z', _, _, _, _, hn => congrArg g (Prod.ext (by omega) (by omega))
  | n + 1, z, z', hz, hz', hzr, hz'r, hn => by
    have step {a b : Cell} (ha : a ∈ R.dcells) (hb : b ∈ R.dcells) (har : a.2 = r) (hbr : b.2 = r)
        (hlt : a.1 < b.1) (habs : (b.1 - a.1).natAbs = 2 * (n + 1)) : g a = g b := by
      have hac := mem_cells.1 (mem_dcells.1 ha).1; have hbc := mem_cells.1 (mem_dcells.1 hb).1
      have hap := (mem_dcells.1 ha).2; have hbp := (mem_dcells.1 hb).2; unfold IsPrimal at hap hbp
      have hmid : ((a.1 + 2, r) : Cell) ∈ R.dcells := by
        rw [mem_dcells, mem_cells]; unfold IsPrimal; refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega
      have h1 := g_two R hh hfin hg hclosed hr (show ((a.1, r) : Cell) ∈ R.dcells by rwa [← har]) hmid
      have h2 := g_row hh hfin hg hclosed hr n (a.1 + 2, r) b hmid hb rfl hbr (by dsimp only; omega)
      rwa [show a = (a.1, r) from Prod.ext rfl har, h1]
    by_cases hlt : z.1 < z'.1
    · exact step hz hz' hzr hz'r hlt hn
    · exact (step hz' hz hz'r hzr (by
        have hzp := (mem_dcells.1 hz).2; have hzp' := (mem_dcells.1 hz').2; unfold IsPrimal at hzp hzp'; omega) (by omega)).symm

/-- **The exploration boundary is connected.** -/
theorem bd_connected (hh : 0 < R.h) (hw' : 0 < R.w) {p₁ p₂ : ℤ} {A : Finset Cell}
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A)
    {m m' : Cell} (hm : m ∈ R.expBd p₁ p₂ A) (hm' : m' ∈ R.expBd p₁ p₂ A) :
    Relation.ReflTransGen (StepRel primalEnds (R.expBd p₁ p₂ A))
      (primalEnds m).1 (primalEnds m').1 := by
  set bd := R.expBd p₁ p₂ A
  set K : Cell → Prop := Relation.ReflTransGen (StepRel primalEnds bd) (primalEnds m).1
  by_contra hcon
  have hbdinner : ∀ e ∈ bd, e ∈ R.inner := fun _ he => (R.mem_expBd_iff.1 he).1
  have hKedge {e : Cell} (he : e ∈ bd) : K (primalEnds e).1 ↔ K (primalEnds e).2 :=
    ⟨fun h => h.tail ⟨e, he, .inl rfl⟩, fun h => h.tail ⟨e, he, .inr rfl⟩⟩
  set bd₁ := bd.filter (fun e => K (primalEnds e).1)
  set f : Cell → ZMod 2 := ind bd₁
  have hfin : ∀ e, f e ≠ 0 → e ∈ R.inner := fun e he => by
    by_contra hne; exact he (ind_apply_of_not_mem fun h => hne (hbdinner e (Finset.mem_filter.1 h).1))
  have hcdeg_eq (S : Finset Cell) (c : Cell) : cdeg (ind S) c = (((corners c).filter (· ∈ S)).card : ZMod 2) := by
    rw [card_filter_corners]; unfold cdeg ind; push_cast; simp
  have hclosed : ∀ c : Cell, IsPrimal c → R.x0 < c.1 → c.1 < R.x0 + R.w → cdeg f c = 0 := fun c hcp hx1 hx2 => by
    rw [hcdeg_eq]
    by_cases hcc : c ∈ R.pcells
    · by_cases hKc : K c
      · rw [show (corners c).filter (· ∈ bd₁) = (corners c).filter (· ∈ bd) from Finset.filter_congr fun e he =>
          ⟨fun h => (Finset.mem_filter.1 h).1, fun h => Finset.mem_filter.2 ⟨h, by
            rcases (mem_primalEnds_iff c e hcp).2 he with h1 | h1
            · rwa [← h1]
            · exact (hKedge h).2 (h1 ▸ hKc)⟩⟩, ← hcdeg_eq]
        exact R.expBd_cdeg_zero hh hp hb hcc hx1 hx2
      · rw [Finset.filter_eq_empty_iff.2 fun e he hmem => hKc <| by
          obtain ⟨hebd, hKe⟩ := Finset.mem_filter.1 hmem
          rcases (mem_primalEnds_iff c e hcp).2 he with rfl | rfl
          · exact hKe
          · exact (hKedge hebd).1 hKe]; simp
    · rw [Finset.filter_eq_empty_iff.2 fun e he hmem => hcc <| by
        have hei := mem_inner.1 (hbdinner e (Finset.mem_filter.1 hmem).1)
        rw [mem_pcells, mem_cells]; refine ⟨⟨?_, ?_, ?_, ?_⟩, hcp⟩ <;>
          (unfold corners at he; simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at he; omega)]; simp
  set g : Cell → ZMod 2 := leftPotential R.x0 R.y0 f
  have hg : ∀ e ∈ R.inner, g (dualEnds e).1 + g (dualEnds e).2 = f e := fun e he => by
    have := mem_inner.1 he
    exact leftPotential_primitive R.x0 R.y0 R.w f
      (fun e' hle => by by_contra hne; have := mem_inner.1 (hfin e' hne); omega)
      (fun e' hle => by by_contra hne; have := mem_inner.1 (hfin e' hne); omega)
      hclosed e (by omega) (by omega)
  have hfrow (r : ℤ) (h1 : R.y0 ≤ r) (h2 : r ≤ R.y0 + R.h) : ∃ z, z ∈ R.faceRow r := by
    have hwℤ : (0 : ℤ) < R.w := by exact_mod_cast hw'
    by_cases hp0 : IsPrimal (R.x0, r)
    · exact ⟨(R.x0 + 1, r), R.faceRow_mem.2 ⟨by rw [mem_dcells, mem_cells]; unfold IsPrimal at *; refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega, rfl⟩⟩
    · exact ⟨(R.x0, r), R.faceRow_mem.2 ⟨by rw [mem_dcells, mem_cells]; unfold IsPrimal at *; refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega, rfl⟩⟩
  obtain ⟨q₁, hq₁⟩ := hfrow p₁ (by omega) (by omega)
  obtain ⟨q₂, hq₂⟩ := hfrow p₂ (by omega) (by omega)
  have hrow (r : ℤ) (hr : r = R.y0 ∨ r = R.y0 + R.h) {z z' : Cell} (hz : z ∈ R.faceRow r) (hz' : z' ∈ R.faceRow r) : g z = g z' := by
    obtain ⟨hzc, hzr⟩ := R.faceRow_mem.1 hz; obtain ⟨hz'c, hz'r⟩ := R.faceRow_mem.1 hz'
    have hzp := (mem_dcells.1 hzc).2; have hzp' := (mem_dcells.1 hz'c).2; unfold IsPrimal at hzp hzp'
    exact g_row R hh hfin hg hclosed hr ((z'.1 - z.1).natAbs / 2) z z' hzc hz'c hzr hz'r (by omega)
  have hstep_eq {b c e : Cell} (he : e ∈ R.inner) (hec : dualEnds e = (b, c) ∨ dualEnds e = (c, b))
      (hiff : b ∈ R.expU p₁ p₂ A ↔ c ∈ R.expU p₁ p₂ A) : g b = g c := by
    have not_both {P Q : Prop} (h1 : P ↔ Q) (h2 : P ↔ ¬ Q) : False := by
      by_cases hp : P
      · exact (h2.1 hp) (h1.1 hp)
      · exact hp (h1.2 (Classical.byContradiction fun hq => hp (h2.2 hq)))
    have henb : e ∉ bd := fun hebd => by
      have hsep := (R.mem_expBd_iff.1 hebd).2; unfold IsSep at hsep
      rcases hec with h | h <;> rw [h] at hsep <;> dsimp only at hsep
      · exact not_both hiff hsep
      · exact not_both hiff.symm hsep
    have hfe : f e = 0 := ind_apply_of_not_mem fun h => henb (Finset.mem_filter.1 h).1
    have hge := hg e he; rw [hfe] at hge
    have hzeq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
    rcases hec with h | h <;> rw [h] at hge <;> [exact hzeq _ _ hge; exact (hzeq _ _ hge).symm]
  have step_dcells {b c : Cell} (h : StepRel dualEnds R.inner b c) : c ∈ R.dcells := by
    obtain ⟨e, he, hec⟩ := h; have hm := R.dData.mem e he
    rcases hec with h | h
    · have hc : c = (dualEnds e).2 := (congrArg Prod.snd h).symm; rw [hc]; exact hm.2
    · have hc : c = (dualEnds e).1 := (congrArg Prod.fst h).symm; rw [hc]; exact hm.1
  have hchain {t : Cell} (ht : t ∈ R.faceRow p₂) (htD : t ∉ R.expD p₁ A) :
      ∀ z, Relation.ReflTransGen (R.AvoidStep (R.expD p₁ A)) t z → z ∈ R.dcells ∧ z ∉ R.expD p₁ A ∧ g z = g t := by
    intro z hr; induction hr with
    | refl => exact ⟨(R.faceRow_mem.1 ht).1, htD, rfl⟩
    | @tail b c hbr hstep ih =>
      obtain ⟨hbc, hbD, hgb⟩ := ih
      rcases hstep with ⟨hbD', hcD, e, he, hec⟩
      have hcc := step_dcells ⟨e, he, hec⟩
      have hbU : b ∈ R.expU p₁ p₂ A := Finset.mem_filter.2 ⟨hbc, hbD, t, ht, htD, hbr⟩
      have hcU : c ∈ R.expU p₁ p₂ A := Finset.mem_filter.2 ⟨hcc, hcD, t, ht, htD, hbr.tail ⟨hbD', hcD, e, he, hec⟩⟩
      exact ⟨hcc, hcD, (hstep_eq he hec (iff_of_true hbU hcU)).symm.trans hgb⟩
  have hU {z : Cell} (hz : z ∈ R.expU p₁ p₂ A) : g z = g q₂ := by
    obtain ⟨_, _, t, ht, htD, hr⟩ := Finset.mem_filter.1 hz
    exact (hchain ht htD z hr).2.2.trans (hrow p₂ (by omega) ht hq₂)
  have hD1 {z : Cell} (hz : z ∈ R.expD p₁ A) : g z = g q₁ := by
    obtain ⟨_, p, hp', hr⟩ := R.mem_expD.1 hz
    have key : ∀ y, Relation.ReflTransGen (StepRel dualEnds (R.inner \ A)) p y → g y = g p := by
      intro y hry; induction hry with
      | refl => rfl
      | @tail b c hbr hstep ih =>
        obtain ⟨e, he, hec⟩ := hstep
        have hbD : b ∈ R.expD p₁ A := R.mem_expD.2 ⟨R.rtg_mem_dcells (R.faceRow_mem.1 hp').1 hbr, p, hp', hbr⟩
        have hcD : c ∈ R.expD p₁ A := R.mem_expD.2 ⟨R.rtg_mem_dcells (R.faceRow_mem.1 hp').1 (hbr.tail ⟨e, he, hec⟩), p, hp', hbr.tail ⟨e, he, hec⟩⟩
        exact (hstep_eq (Finset.mem_sdiff.1 he).1 hec
          (iff_of_false (fun h => expU_subset_not_expD h hbD) (fun h => expU_subset_not_expD h hcD))).symm.trans ih
    exact (key z hr).trans (hrow p₁ (by omega) hp' hq₁)
  have hX : ∀ w, Relation.ReflTransGen (StepRel dualEnds R.inner) w q₁ → w ∈ R.dcells → w ∉ R.expU p₁ p₂ A → g w = g q₁ := by
    intro w hr; induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => intro _ _; rfl
    | @head w y hstep _ ih =>
      intro hwc hwU
      by_cases hwD : w ∈ R.expD p₁ A
      · exact hD1 hwD
      · have hyU : y ∉ R.expU p₁ p₂ A := fun hyU => hwU <| by
          obtain ⟨_, hyD, t, ht, htD, hr'⟩ := Finset.mem_filter.1 hyU
          exact Finset.mem_filter.2 ⟨hwc, hwD, t, ht, htD, hr'.tail ⟨hyD, hwD, stepRel_symm hstep⟩⟩
        rcases hstep with ⟨e, he, hec⟩
        exact (hstep_eq he hec (iff_of_false hwU hyU)).trans (ih (step_dcells ⟨e, he, hec⟩) hyU)
  have hbdval {e : Cell} (he : e ∈ bd) : f e = g q₁ + g q₂ := by
    have hei := hbdinner e he; have hmem := R.dData.mem e hei
    have hsep := (R.mem_expBd_iff.1 he).2; unfold IsSep at hsep
    rw [← hg e hei]
    by_cases h1 : (dualEnds e).1 ∈ R.expU p₁ p₂ A
    · rw [hU h1, hX _ (R.dual_connected hw' hh hmem.2 (R.faceRow_mem.1 hq₁).1) hmem.2 (hsep.1 h1)]; ring
    · have h2 : (dualEnds e).2 ∈ R.expU p₁ p₂ A := by by_contra h2; exact h1 (hsep.2 h2)
      rw [hX _ (R.dual_connected hw' hh hmem.1 (R.faceRow_mem.1 hq₁).1) hmem.1 h1, hU h2]
  have e1 := hbdval hm; have e2 := hbdval hm'
  have hm1 : m ∈ bd₁ := Finset.mem_filter.2 ⟨hm, .refl⟩
  have hm2 : m' ∉ bd₁ := fun h => hcon (Finset.mem_filter.1 h).2
  change ind bd₁ m = _ at e1; change ind bd₁ m' = _ at e2
  rw [ind_apply_of_mem hm1] at e1
  rw [ind_apply_of_not_mem hm2, ← e1] at e2
  exact absurd e2 (by decide)

end Rect

end PottsDiscontinuity.TorusCrossing
