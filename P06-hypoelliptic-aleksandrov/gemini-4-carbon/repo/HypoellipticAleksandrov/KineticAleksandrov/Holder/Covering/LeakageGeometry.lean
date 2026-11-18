module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.T5
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.InflationVolume
import Mathlib.MeasureTheory.Group.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationGeometry

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
open Set MeasureTheory


/-- A bounded nonempty open order-connected real set is its open endpoint interval. -/
theorem open_ordConnected_eq_Ioo {s : Set ℝ} (hs : IsOpen s) (hn : s.Nonempty)
    (hbelow : BddBelow s) (habove : BddAbove s) (hc : s.OrdConnected) :
    s = Ioo (sInf s) (sSup s) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, b, hax, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hs.mem_nhds hx)
    rcases hax with ⟨hax, hxb⟩
    have ha : (a+x)/2 ∈ s := hsub ⟨by linarith only [hax], by linarith only [hax, hxb]⟩
    have hb : (x+b)/2 ∈ s := hsub ⟨by linarith only [hax, hxb], by linarith only [hxb]⟩
    exact ⟨lt_of_le_of_lt (csInf_le hbelow ha) (by linarith only [hax, hxb]),
      lt_of_lt_of_le (by linarith only [hxb]) (le_csSup habove hb)⟩
  · intro hx
    obtain ⟨a, ha, hax⟩ := exists_lt_of_csInf_lt hn hx.1
    obtain ⟨b, hb, hxb⟩ := exists_lt_of_lt_csSup hn hx.2
    exact hc.out ha hb ⟨hax.le, hxb.le⟩


/-- A bounded open real set is a countable disjoint union of nonempty open intervals.
Every nonempty open interval in the set is contained in one of these components. -/
theorem bounded_open_interval_components {U : Set ℝ} (hU : IsOpen U)
    (hbelow : BddBelow U) (habove : BddAbove U) :
    ∃ C : Set (Set ℝ), C.Countable ∧ C.PairwiseDisjoint id ∧
      (∀ s ∈ C, s.Nonempty ∧ s = Ioo (sInf s) (sSup s)) ∧
      (⋃ s ∈ C, s) = U ∧
      (∀ a b : ℝ, a < b → Ioo a b ⊆ U → ∃ s ∈ C, Ioo a b ⊆ s)  := by
  have isOpen_ordConnectedComponent (x : ℝ) :
      IsOpen (ordConnectedComponent U x) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [ordConnectedComponent_eq hy]
    exact ordConnectedComponent_mem_nhds.mpr (hU.mem_nhds (ordConnectedComponent_subset hy))
  let C : Set (Set ℝ) := {s | ∃ x ∈ U, s = ordConnectedComponent U x}
  have hnonempty : ∀ s ∈ C, s.Nonempty := by
    rintro s ⟨x, hx, rfl⟩
    exact nonempty_ordConnectedComponent.mpr hx
  have hopen : ∀ s ∈ C, IsOpen s := by
    rintro s ⟨x, _, rfl⟩
    exact isOpen_ordConnectedComponent x
  have hdisj : C.PairwiseDisjoint id := by
    rintro s ⟨x, _, rfl⟩ t ⟨y, _, rfl⟩ hne
    change Disjoint (ordConnectedComponent U x) (ordConnectedComponent U y)
    rw [disjoint_left]
    intro z hxz hyz
    exact hne ((ordConnectedComponent_eq hxz).trans (ordConnectedComponent_eq hyz).symm)
  have hcount : C.Countable := hdisj.countable_of_nonempty_interior fun s hs => by
    change (interior s).Nonempty
    rw [(hopen s hs).interior_eq]
    exact hnonempty s hs
  refine ⟨C, hcount, hdisj, ?_, ?_, ?_⟩
  · rintro s hs
    rcases hs with ⟨x, hx, rfl⟩
    refine ⟨nonempty_ordConnectedComponent.mpr hx, ?_⟩
    exact open_ordConnected_eq_Ioo (isOpen_ordConnectedComponent x)
      (nonempty_ordConnectedComponent.mpr hx)
      (hbelow.mono ordConnectedComponent_subset) (habove.mono ordConnectedComponent_subset)
      inferInstance
  · ext x
    constructor
    · intro hx
      obtain ⟨s, ⟨y, _, rfl⟩, hx⟩ := mem_iUnion₂.mp hx
      exact ordConnectedComponent_subset hx
    · intro hx
      exact mem_iUnion₂.mpr ⟨ordConnectedComponent U x, ⟨x, hx, rfl⟩,
        self_mem_ordConnectedComponent.mpr hx⟩
  · intro a b hab hsub
    let x := (a+b)/2
    have hx : x ∈ Ioo a b := ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
    refine ⟨ordConnectedComponent U x, ⟨x, hsub hx, rfl⟩, ?_⟩
    exact subset_ordConnectedComponent hx hsub

/-- The backward interval lies in the left extension of any interval containing its delay. -/
theorem backwardInterval_subset_component_extension {a h m l b : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hsub : Ioo a (a+m*h) ⊆ Ioo l b) :
    Ioo (a-h) a ⊆ Ioo (l-(b-l)/m) b := by
  have hab : a < a+m*h := by nlinarith only [hh, hm]
  obtain ⟨hla, hright⟩ := (Ioo_subset_Ioo_iff hab).mp hsub
  have hlen : h ≤ (b-l)/m := (le_div_iff₀ hm).mpr (by nlinarith only [hla, hright])
  intro x hx
  exact ⟨by linarith only [hx.1, hla, hlen],
    lt_of_lt_of_le hx.2 (le_trans hab.le hright)⟩




/-- A bounded forward union controls the preceding union by the sharp delay factor. -/
theorem interval_delay_of_bounded_union {ι : Type*} (a h : ι → ℝ) (I : Set ι)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i ∈ I, 0 < h i)
    (hbelow : BddBelow (⋃ i ∈ I, Ioo (a i) (a i + m*h i)))
    (habove : BddAbove (⋃ i ∈ I, Ioo (a i) (a i + m*h i))) :
    volume (⋃ i ∈ I, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i ∈ I, Ioo (a i) (a i+m*h i))  := by
  have volume_component_extension {l : ℝ} {b : ℝ} :
      volume (Ioo (l-(b-l)/m) b) =
      ENNReal.ofReal ((m+1)/m) * volume (Ioo l b) := by
    rw [Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  let U := ⋃ i ∈ I, Ioo (a i) (a i+m*h i)
  obtain ⟨C, hcount, hdisj, hcomp, hcover, hcontains⟩ :=
    bounded_open_interval_components (isOpen_biUnion fun _ _ => isOpen_Ioo) hbelow habove
  let ext : Set ℝ → Set ℝ := fun s => Ioo (sInf s-(sSup s-sInf s)/m) (sSup s)
  have hback : (⋃ i ∈ I, Ioo (a i-h i) (a i)) ⊆ ⋃ s ∈ C, ext s := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    have hai : a i < a i+m*h i := by nlinarith only [hm, hh i hi]
    obtain ⟨s, hs, hIs⟩ := hcontains (a i) (a i+m*h i) hai
      (subset_iUnion₂_of_subset i hi Subset.rfl)
    have hI := backwardInterval_subset_component_extension (hh i hi) hm
      (hIs.trans (subset_of_eq (hcomp s hs).2))
    exact mem_iUnion₂.mpr ⟨s, hs, hI hxi⟩
  have hvol : ∀ s ∈ C, volume (ext s) = ENNReal.ofReal ((m+1)/m) * volume s := by
    intro s hs
    change volume (Ioo (sInf s-(sSup s-sInf s)/m) (sSup s)) = _
    rw [volume_component_extension, ← (hcomp s hs).2]
  have hmeas : ∀ s ∈ C, MeasurableSet s := by
    intro s hs
    rw [(hcomp s hs).2]
    exact measurableSet_Ioo
  calc
    volume (⋃ i ∈ I, Ioo (a i-h i) (a i)) ≤ volume (⋃ s ∈ C, ext s) :=
      measure_mono hback
    _ ≤ ∑' s : C, volume (ext s) := measure_biUnion_le volume hcount ext
    _ = ∑' s : C, ENNReal.ofReal ((m+1)/m) * volume (s : Set ℝ) :=
      tsum_congr fun s => hvol s s.2
    _ = ENNReal.ofReal ((m+1)/m) * ∑' s : C, volume (s : Set ℝ) :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal ((m+1)/m) * volume U := by
      have hsum := measure_biUnion (μ := volume) hcount hdisj hmeas
      simp only [id_eq] at hsum
      rw [hcover] at hsum
      rw [← hsum]

/-- The sharp delayed-union inequality for a finite interval family. -/
theorem interval_delay_finset {ι : Type*} (a h : ι → ℝ) (s : Finset ι)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i ∈ s, 0 < h i) :
    volume (⋃ i ∈ s, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i ∈ s, Ioo (a i) (a i+m*h i)) := by
  apply interval_delay_of_bounded_union a h (s : Set ι) hm hh
  · obtain ⟨l, hl⟩ := (s.finite_toSet.image a).bddBelow
    refine ⟨l, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact (hl (mem_image_of_mem a hi)).trans hxi.1.le
  · obtain ⟨b, hb⟩ := (s.finite_toSet.image (fun i => a i+m*h i)).bddAbove
    refine ⟨b, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact hxi.2.le.trans (hb (mem_image_of_mem (fun i => a i+m*h i) hi))

/-- Countable delayed interval families satisfy the same sharp factor. -/
theorem interval_delay_countable {ι : Type*} [Countable ι] (a h : ι → ℝ)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i, 0 < h i) :
    volume (⋃ i, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i, Ioo (a i) (a i+m*h i)) := by
  classical
  let B : Finset ι → Set ℝ := fun s => ⋃ i ∈ s, Ioo (a i-h i) (a i)
  have hB : Monotone B := by
    intro s t hst x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i, hst hi, hxi⟩
  have heq : (⋃ s, B s) = ⋃ i, Ioo (a i-h i) (a i) := by
    ext x
    simp only [B, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨s, i, _, hx⟩
      exact ⟨i, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨{i}, i, Finset.mem_singleton_self i, hx⟩
  rw [← heq, hB.measure_iUnion]
  apply iSup_le
  intro s
  calc
    volume (B s) ≤ ENNReal.ofReal ((m+1)/m) *
        volume (⋃ i ∈ s, Ioo (a i) (a i+m*h i)) :=
      interval_delay_finset a h s hm (fun i _ => hh i)
    _ ≤ ENNReal.ofReal ((m+1)/m) * volume (⋃ i, Ioo (a i) (a i+m*h i)) := by
      apply mul_le_mul_right
      apply measure_mono
      intro x hx
      obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨i, hxi⟩



/-- Transport coordinates ordered as velocity, transported position, time. -/
def transportChart {d : ℕ} (z : PDE.Vec d × (PDE.Vec d × ℝ)) : KineticPoint d :=
  ⟨z.2.2, z.2.1+z.2.2 • z.1, z.1⟩


/-- At fixed velocity, time-dependent position translation preserves product volume. -/
theorem measurePreserving_transport_fiber {d : ℕ} (v : PDE.Vec d) :
    MeasurePreserving (fun z : PDE.Vec d × ℝ => (z.2, z.1+z.2 • v)) volume volume := by
  have h : MeasurePreserving (fun z : ℝ × PDE.Vec d => (z.1, z.2+z.1 • v))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) := by
    refine (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun t x => x+t • v) ?_ ?_
    · exact (continuous_snd.add (continuous_fst.smul continuous_const)).measurable
    · exact Filter.Eventually.of_forall fun t =>
        (measurePreserving_add_right (volume : Measure (PDE.Vec d)) (t • v)).map_eq
  simpa only [Measure.volume_eq_prod, Function.comp_def, Prod.swap,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply] using
    h.comp (Measure.measurePreserving_swap (μ := (volume : Measure (PDE.Vec d)))
      (ν := (volume : Measure ℝ)))


/-- Backward transport slices fit in a fixed transported position ball of radius 2r³. -/
theorem cylinder_transport_slice {d : ℕ} (P : KineticPoint d) {r : ℝ} (hr : 0 < r)
    (v y : PDE.Vec d) (t : ℝ)
    (h : transportChart (v, y, t) ∈ backwardCylinder P r) :
    t ∈ Ioo (P.time-r^2) P.time ∧ v ∈ PDE.euclideanBall P.velocity r ∧
      y ∈ PDE.euclideanBall (P.position-P.time • v) (2*r^3) := by
  refine ⟨⟨h.1, h.2.1⟩, h.2.2.1, ?_⟩
  have hv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp h.2.2.1
  have hx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3)).mp h.2.2.2
  rw [sub_zero] at hx
  change PDE.vecEuclideanNorm (v-P.velocity) < r at hv
  have htime₁ : P.time-r^2 < t := h.1
  have htime₂ : t < P.time := h.2.1
  have ht : |t-P.time| < r^2 := by
    rw [abs_lt]
    constructor <;> linarith only [htime₁, htime₂]
  have heq : y-(P.position-P.time • v) = relativePosition P (transportChart (v,y,t))-
      (t-P.time) • (v-P.velocity) := by
    ext i
    simp only [relativePosition, transportChart, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity : 0 < 2*r^3), heq]
  have hn := PDE.vecEuclideanNorm_add_le (relativePosition P (transportChart (v,y,t)))
    (-((t-P.time) • (v-P.velocity)))
  rw [PDE.vecEuclideanNorm_neg, PDE.vecEuclideanNorm_smul] at hn
  rw [sub_eq_add_neg]
  have hm := mul_le_mul ht.le hv.le (PDE.vecEuclideanNorm_nonneg _) (sq_nonneg r)
  nlinarith

/-- The delayed transport product is contained in the forward stack. -/
theorem delayed_transport_slice {d : ℕ} (P : KineticPoint d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (v y : PDE.Vec d) (t : ℝ)
    (ht : t ∈ Ioo P.time (P.time+(m : ℝ)*r^2))
    (hv : v ∈ PDE.euclideanBall P.velocity r)
    (hy : y ∈ PDE.euclideanBall (P.position-P.time • v) (2*r^3)) :
    transportChart (v,y,t) ∈ forwardStack P r m := by
  refine ⟨by change 0 < t-P.time; linarith only [ht.1],
    by change t-P.time ≤ (m : ℝ)*r^2; linarith only [ht.2], hv, ?_⟩
  have hvn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hv
  have hyn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by positivity : 0 < 2*r^3)).mp hy
  have heq : relativePosition P (transportChart (v,y,t)) =
      (y-(P.position-P.time • v))+(t-P.time) • (v-P.velocity) := by
    ext i
    simp only [relativePosition, transportChart, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hrad : 0 < ((m+2 : ℕ) : ℝ)*r^3 := by positivity
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hrad, sub_zero, heq]
  have hn := PDE.vecEuclideanNorm_add_le (y-(P.position-P.time • v))
    ((t-P.time) • (v-P.velocity))
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (sub_pos.mpr ht.1)] at hn
  have hm := mul_le_mul (by linarith only [ht.2] : t-P.time ≤ (m : ℝ)*r^2)
    hvn.le (PDE.vecEuclideanNorm_nonneg _) (by positivity : 0 ≤ (m : ℝ)*r^2)
  push_cast
  nlinarith



/-- Open stack interiors avoid any uncountable union of terminal faces. -/
def openForwardStack {d : ℕ} (P : KineticPoint d) (r : ℝ) (m : ℕ) :
    Set (KineticPoint d) :=
  forwardStack P r m ∩ {X | X.time < P.time+(m : ℝ)*r^2}

/-- Open forward stack interiors are open. -/
theorem isOpen_openForwardStack {d : ℕ} (P : KineticPoint d) (r : ℝ) (m : ℕ) :
    IsOpen (openForwardStack P r m) := by
  have hx : Continuous (relativePosition P) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  have heq : openForwardStack P r m =
      {X | P.time < X.time ∧ X.time < P.time+(m : ℝ)*r^2 ∧
        X.velocity ∈ PDE.euclideanBall P.velocity r ∧
        relativePosition P X ∈ PDE.euclideanBall 0 (((m+2 : ℕ) : ℝ)*r^3)} := by
    ext X
    change (0 < X.time-P.time ∧ X.time-P.time ≤ (m : ℝ)*r^2 ∧ _ ∧ _) ∧ _ ↔ _
    constructor
    · rintro ⟨⟨ht, _, hv, hx⟩, htop⟩
      exact ⟨by linarith, htop, hv, hx⟩
    · rintro ⟨ht, htop, hv, hx⟩
      exact ⟨⟨by linarith, by linarith, hv, hx⟩, htop⟩
  rw [heq]
  exact (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      (((PDE.isOpen_euclideanBall _ _).preimage continuous_velocity).inter
        ((PDE.isOpen_euclideanBall _ _).preimage hx)))


/-- Each transport slice satisfies the sharp one-dimensional delayed-union inequality. -/
theorem delayed_union_slice {d : ℕ} {ι : Type*} [Countable ι]
    (P : ι → KineticPoint d) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (m : ℕ) (hm : 0 < m) (v y : PDE.Vec d) :
    volume {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, backwardCylinder (P i) (r i)} ≤
      ENNReal.ofReal (((m : ℝ)+1)/(m : ℝ)) *
        volume {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, openForwardStack (P i) (r i) m} := by
  let A : Set ι := {i | v ∈ PDE.euclideanBall (P i).velocity (r i) ∧
    y ∈ PDE.euclideanBall ((P i).position-(P i).time • v) (2*(r i)^3)}
  have hback : {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, backwardCylinder (P i) (r i)} ⊆
      ⋃ i : A, Ioo ((P i).time-(r i)^2) (P i).time := by
    intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    obtain ⟨htime, hv, hy⟩ := cylinder_transport_slice (P i) (hr i) v y t hi
    exact mem_iUnion.mpr ⟨⟨i, hv, hy⟩, htime⟩
  have hforward : (⋃ i : A, Ioo (P i).time ((P i).time+(m : ℝ)*(r i)^2)) ⊆
      {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, openForwardStack (P i) (r i) m} := by
    intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    apply mem_iUnion.mpr
    exact ⟨i, delayed_transport_slice (P i) (hr i) m v y t hi i.2.1 i.2.2, hi.2⟩
  calc
    _ ≤ volume (⋃ i : A, Ioo ((P i).time-(r i)^2) (P i).time) := measure_mono hback
    _ ≤ ENNReal.ofReal (((m : ℝ)+1)/(m : ℝ)) *
        volume (⋃ i : A, Ioo (P i).time ((P i).time+(m : ℝ)*(r i)^2)) :=
      interval_delay_countable (fun i : A => (P i).time) (fun i : A => (r i)^2)
        (by exact_mod_cast hm) (fun i => sq_pos_of_pos (hr i))
    _ ≤ _ := mul_le_mul_right (measure_mono hforward) _

/-- Countable kinetic cylinder families satisfy the sharp delayed-union estimate. -/
theorem delayed_union_countable {d : ℕ} {ι : Type*} [Countable ι]
    (P : ι → KineticPoint d) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (m : ℕ) (hm : 0 < m) :
    volume (⋃ i, backwardCylinder (P i) (r i)) ≤
      ENNReal.ofReal (((m : ℝ)+1)/(m : ℝ)) *
        volume (⋃ i, openForwardStack (P i) (r i) m)  := by
  have volume_transport_slices {S : Set (KineticPoint d)} (hS : MeasurableSet S) :
      volume S = ∫⁻ v : PDE.Vec d, ∫⁻ y : PDE.Vec d,
      volume {t : ℝ | transportChart (v,y,t) ∈ S} := by
    have measurePreserving_transportChart :
        MeasurePreserving (@transportChart d) volume volume := by
      have hshear : MeasurePreserving
          (fun z : PDE.Vec d × (PDE.Vec d × ℝ) => (z.1, z.2.2, z.2.1+z.2.2 • z.1))
          ((volume : Measure (PDE.Vec d)).prod volume)
          ((volume : Measure (PDE.Vec d)).prod volume) := by
        refine (MeasurePreserving.id (volume : Measure (PDE.Vec d))).skew_product
          (g := fun (v : PDE.Vec d) (z : PDE.Vec d × ℝ) => (z.2, z.1+z.2 • v)) ?_ ?_
        · exact (continuous_snd.snd.prodMk
            (continuous_snd.fst.add (continuous_snd.snd.smul continuous_fst))).measurable
        · exact Filter.Eventually.of_forall fun v => (measurePreserving_transport_fiber v).map_eq
      have hperm : MeasurePreserving
          (fun z : PDE.Vec d × (ℝ × PDE.Vec d) => (z.2.1, z.2.2, z.1)) volume volume := by
        simpa only [Measure.volume_eq_prod, Function.comp_def, Prod.swap,
        MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply] using
          (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure (PDE.Vec d))
            (volume : Measure (PDE.Vec d))).comp
            (Measure.measurePreserving_swap (μ := (volume : Measure (PDE.Vec d)))
              (ν := (volume : Measure (ℝ × PDE.Vec d))))
      have hinv : MeasurePreserving (KineticPoint.equivProd d).symm volume volume :=
        ⟨KineticPoint.measurable_equivProd_symm d, rfl⟩
      change MeasurePreserving
        (fun z : PDE.Vec d × (PDE.Vec d × ℝ) =>
          KineticPoint.mk z.2.2 (z.2.1+z.2.2 • z.1) z.1) _ _
      simpa only [Measure.volume_eq_prod, Function.comp_def, transportChart,
        KineticPoint.equivProd, Equiv.coe_fn_symm_mk] using hinv.comp (hperm.comp hshear)
    have continuous_transportChart :
        Continuous (@transportChart d) := by
      apply KineticPoint.continuous_mk <;> fun_prop
    have hs : MeasurableSet (transportChart ⁻¹' S) :=
      hS.preimage (continuous_transportChart).measurable
    rw [← (measurePreserving_transportChart).measure_preimage hS.nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_apply hs]
    apply lintegral_congr
    intro v
    rw [Measure.volume_eq_prod, Measure.prod_apply (measurable_prodMk_left hs)]
    rfl
  rw [volume_transport_slices (isOpen_iUnion (fun i => isOpen_cylinder (P i) (r i))).measurableSet,
    volume_transport_slices
      (isOpen_iUnion (fun i => isOpen_openForwardStack (P i) (r i) m)).measurableSet,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun y => delayed_union_slice P r hr m hm v y



/-- Round product boxes use native Euclidean spatial and velocity balls. -/
def roundBox (d : ℕ) (a b R : ℝ) : Set (KineticPoint d) :=
  {X | a < X.time ∧ X.time < b ∧
    X.position ∈ PDE.euclideanBall 0 R ∧ X.velocity ∈ PDE.euclideanBall 0 1}

/-- The top center with any interior velocity belongs to the cylinder closure. -/
theorem top_mem_closure_cylinder {d : ℕ} (P : KineticPoint d) {r : ℝ} (hr : 0 < r)
    {v : PDE.Vec d} (hv : v ∈ PDE.euclideanBall P.velocity r) :
    (⟨P.time, P.position, v⟩ : KineticPoint d) ∈ closure (backwardCylinder P r) := by
  let f : ℝ → KineticPoint d := fun t =>
    ⟨t, P.position+(t-P.time) • P.velocity, v⟩
  have hf : Continuous f := KineticPoint.continuous_mk continuous_id
    (continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const))
    continuous_const
  have hsub : f '' Ioo (P.time-r^2) P.time ⊆ backwardCylinder P r := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨ht.1, ht.2, hv, ?_⟩
    have heq : relativePosition P (f t) = 0 := by
      ext i
      simp only [relativePosition, f, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul]
      ring
    rw [heq]
    exact PDE.center_mem_euclideanBall 0 (pow_pos hr 3)
  have ht : P.time ∈ closure (Ioo (P.time-r^2) P.time) := by
    rw [closure_Ioo (sub_lt_self _ (sq_pos_of_pos hr)).ne]
    exact ⟨by linarith [sq_nonneg r], le_rfl⟩
  have h := closure_mono hsub
    (hf.continuousOn.image_closure (mem_image_of_mem f ht))
  simpa only [f, sub_self, zero_smul, add_zero] using h


/-- Every velocity in the source velocity ball of a subcylinder lies in the unit ball. -/
theorem velocity_ball_subset_unit {d : ℕ} {P : KineticPoint d} {r : ℝ}
    (hr : 0 < r) (hsub : backwardCylinder P r ⊆ unitCylinder d)
    {v : PDE.Vec d} (hv : v ∈ PDE.euclideanBall P.velocity r) :
    PDE.vecEuclideanNorm v < 1 := by
  obtain ⟨Y, hY⟩ := cylinder_nonempty P hr
  let Z : KineticPoint d := ⟨Y.time, Y.position, v⟩
  have hZ : Z ∈ backwardCylinder P r := ⟨hY.1, hY.2.1, hv, hY.2.2.2⟩
  exact ((mem_unitCylinder_iff Z).mp (hsub hZ)).2.2.1

/-- A delayed stack lies in the time-spatial leakage envelope. -/
theorem forwardStack_subset_roundBox {d : ℕ} {P : KineticPoint d} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R ≤ 1)
    (hsub : backwardCylinder P r ⊆ unitCylinder d) (m : ℕ) (hm : 0 < m) :
    forwardStack P r m ⊆ roundBox d (-1) ((m : ℝ)*R^2) (1+4*(m : ℝ)*R^2)  := by
  have cylinder_subset_unit_center_bounds :
      -1 ≤ P.time ∧ P.time ≤ 0 ∧ PDE.vecEuclideanNorm P.position ≤ 1 ∧
      PDE.vecEuclideanNorm P.velocity < 1 := by
    have htop := closure_mono hsub
      (top_mem_closure_cylinder P hr (PDE.center_mem_euclideanBall _ hr))
    have hb := closure_cylinder_bounds (⟨0,0,0⟩ : KineticPoint d) 1 htop
    have hp : PDE.vecNormSq P.position ≤ 1 := by
      simpa only [relativePosition, sub_zero, smul_zero, one_pow] using hb.2.2.2
    have hpn := PDE.vecEuclideanNorm_nonneg P.position
    have hs := PDE.vecEuclideanNorm_sq P.position
    obtain ⟨Y, hY⟩ := cylinder_nonempty P hr
    let Z : KineticPoint d := ⟨Y.time, Y.position, P.velocity⟩
    have hZ : Z ∈ backwardCylinder P r :=
      ⟨hY.1, hY.2.1, PDE.center_mem_euclideanBall _ hr, hY.2.2.2⟩
    have hv := ((mem_unitCylinder_iff Z).mp (hsub hZ)).2.2.1
    refine ⟨?_, ?_, by nlinarith, hv⟩
    · simpa only [one_pow, zero_sub] using hb.1
    · exact hb.2.1
  obtain ⟨htlo, hthi, hx, hv⟩ := cylinder_subset_unit_center_bounds
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hr1 := hrR.le.trans hR
  intro Z hZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hz : 0 < Z.time-P.time := hZ.1
    linarith
  · have hz := hZ.2.1
    have hs : r^2 < R^2 := by nlinarith
    nlinarith
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero]
    have hy := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by positivity : 0 < ((m+2 : ℕ) : ℝ)*r^3)).mp hZ.2.2.2
    rw [sub_zero] at hy
    have heq : Z.position = P.position+relativePosition P Z+(Z.time-P.time) • P.velocity := by
      ext i
      simp only [relativePosition, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      ring
    have hn₁ := PDE.vecEuclideanNorm_add_le P.position (relativePosition P Z)
    have hn₂ := PDE.vecEuclideanNorm_add_le (P.position+relativePosition P Z)
      ((Z.time-P.time) • P.velocity)
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos hZ.1] at hn₂
    have hprod : (Z.time-P.time)*PDE.vecEuclideanNorm P.velocity ≤ (m : ℝ)*r^2 := by
      nlinarith only [hZ.2.1, hv, hZ.1, PDE.vecEuclideanNorm_nonneg P.velocity]
    have hc : r^3 ≤ r^2 := by nlinarith [sq_nonneg r]
    have hs : r^2 ≤ R^2 := by nlinarith
    have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
    push_cast at hy
    rw [heq]
    nlinarith
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one, sub_zero]
    exact velocity_ball_subset_unit hr hsub hZ.2.2.1

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

