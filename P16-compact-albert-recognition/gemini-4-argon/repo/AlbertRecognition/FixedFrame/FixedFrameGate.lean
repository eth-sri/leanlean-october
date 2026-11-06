module

public import AlbertRecognition.FixedFrame.ScalarBlocks
public import Glennie.Automorphism
public import Glennie.Native.RealConjugation

@[expose] public section
namespace AlbertRecognition
noncomputable section
open Glennie

/-- Restrict an actual native trace-preserving automorphism to the real trace kernel. -/
def automorphismV (g : CompactAutomorphism) : V ≃ₗ[ℝ] V where
  toFun x := ⟨g.equiv (x : Albert), by
    change trace (g.equiv (x : Albert)) = 0
    rw [g.map_trace]; exact trace_V x⟩
  invFun x := ⟨g.symm.equiv (x : Albert), by
    change trace (g.symm.equiv (x : Albert)) = 0
    rw [g.symm.map_trace]; exact trace_V x⟩
  left_inv x := Subtype.ext (g.equiv.symm_apply_apply (x : Albert))
  right_inv x := Subtype.ext (g.equiv.apply_symm_apply (x : Albert))
  map_add' x y := Subtype.ext (map_add g.equiv _ _)
  map_smul' r x := Subtype.ext (by
    change g.equiv (r • (x : Albert)) = r • g.equiv (x : Albert)
    simpa only [RingHom.id_apply] using map_smul g.equiv r (x : Albert))

theorem automorphismV_gA (g : CompactAutomorphism) (x y : V) :
    gA (automorphismV g x) (automorphismV g y) = gA x y :=
  congrArg (fun r : ℝ => r / 3) (g.inner_map (x : Albert) (y : Albert))

theorem automorphismV_KA (g : CompactAutomorphism) (x y : V) :
    automorphismV g (KA x y) = KA (automorphismV g x) (automorphismV g y) := by
  apply Subtype.ext
  change g.equiv (traceless (jordan (x : Albert) (y : Albert))) =
    traceless (jordan (g.equiv (x : Albert)) (g.equiv (y : Albert)))
  rw [g.map_traceless, g.map_jordan]

/-- Pullback of an arbitrary genuine symmetric trilinear form by a real equivalence. -/
def pullbackCubic (T : V ≃ₗ[ℝ] V) (B : SymmetricCubic) : SymmetricCubic where
  form :=
    { toFun := fun x =>
        { toFun := fun y => (B.form (T x) (T y)).comp T.toLinearMap
          map_add' y z := LinearMap.ext fun v => by
            change B.form (T x) (T (y + z)) (T v) =
              B.form (T x) (T y) (T v) + B.form (T x) (T z) (T v)
            rw [map_add, map_add, LinearMap.add_apply]
          map_smul' r y := LinearMap.ext fun v => by
            change B.form (T x) (T (r • y)) (T v) = r * B.form (T x) (T y) (T v)
            rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul] }
      map_add' x y := LinearMap.ext fun z => LinearMap.ext fun v => by
        change B.form (T (x + y)) (T z) (T v) =
          B.form (T x) (T z) (T v) + B.form (T y) (T z) (T v)
        rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
      map_smul' r x := LinearMap.ext fun y => LinearMap.ext fun z => by
        change B.form (T (r • x)) (T y) (T z) = r * B.form (T x) (T y) (T z)
        rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] }
  swap12 x y z := B.swap12 (T x) (T y) (T z)
  swap23 x y z := B.swap23 (T x) (T y) (T z)

@[simp] theorem pullbackCubic_form (T : V ≃ₗ[ℝ] V) (B : SymmetricCubic)
    (x y z : V) : (pullbackCubic T B).form x y z = B.form (T x) (T y) (T z) := rfl

theorem automorphismV_KB_pullback (g : CompactAutomorphism) (B : SymmetricCubic)
    (x y : V) :
    automorphismV g (KB (pullbackCubic (automorphismV g) B) x y) =
      KB B (automorphismV g x) (automorphismV g y) := by
  apply metricDual.injective; apply LinearMap.ext; intro z
  obtain ⟨w, rfl⟩ := (automorphismV g).surjective z
  change gA (automorphismV g (KB (pullbackCubic (automorphismV g) B) x y)) (automorphismV g w) =
    gA (KB B (automorphismV g x) (automorphismV g y)) (automorphismV g w)
  rw [automorphismV_gA, KB_pairing, KB_pairing, pullbackCubic_form]

theorem scalar_action_of_pullback (g : CompactAutomorphism) (B : SymmetricCubic)
    (x y : V) (r : ℝ)
    (hxy : KB (pullbackCubic (automorphismV g) B) x y = r • y) :
    KB B (automorphismV g x) (automorphismV g y) = r • automorphismV g y := by
  rw [← automorphismV_KB_pullback, hxy, map_smul]

private theorem intertwines_operatorComm (T : V ≃ₗ[ℝ] V)
    (P Q R S : V →ₗ[ℝ] V)
    (hP : ∀ v, T (P v) = R (T v)) (hQ : ∀ v, T (Q v) = S (T v))
    (v : V) : T (operatorComm P Q v) = operatorComm R S (T v) := by
  change T (P (Q v) - Q (P v)) = R (S (T v)) - S (R (T v))
  simp only [map_sub, hP, hQ]

theorem automorphismV_q_reference (g : CompactAutomorphism) (x y v : V) :
    automorphismV g (q referenceCubic x y v) =
      q referenceCubic (automorphismV g x) (automorphismV g y) (automorphismV g v) := by
  simp only [q, KB_referenceCubic]
  exact intertwines_operatorComm (automorphismV g)
    (KA x) (KA y) (KA (automorphismV g x)) (KA (automorphismV g y))
    (automorphismV_KA g x) (automorphismV_KA g y) v

theorem automorphismV_A_q_pullback (g : CompactAutomorphism) (B : SymmetricCubic)
    (x y z v : V) :
    automorphismV g (A (q referenceCubic) (pullbackCubic (automorphismV g) B) x y z v) =
      A (q referenceCubic) B (automorphismV g x) (automorphismV g y)
        (automorphismV g z) (automorphismV g v) := by
  have hterm (u w s : V) :=
    intertwines_operatorComm (automorphismV g)
      (KB (pullbackCubic (automorphismV g) B) u) (q referenceCubic w s)
      (KB B (automorphismV g u))
      (q referenceCubic (automorphismV g w) (automorphismV g s))
      (automorphismV_KB_pullback g B u) (automorphismV_q_reference g w s) v
  change automorphismV g
      (operatorComm (KB (pullbackCubic (automorphismV g) B) x) (q referenceCubic y z) v +
        operatorComm (KB (pullbackCubic (automorphismV g) B) y) (q referenceCubic z x) v +
        operatorComm (KB (pullbackCubic (automorphismV g) B) z) (q referenceCubic x y) v) = _
  rw [map_add, map_add, hterm x y z, hterm y z x, hterm z x y]; rfl

theorem A_q_pullback_zero (g : CompactAutomorphism) (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    A (q referenceCubic) (pullbackCubic (automorphismV g) B) = 0 := by
  funext x y z; apply LinearMap.ext; intro v
  apply (automorphismV g).injective
  change automorphismV g (A (q referenceCubic) (pullbackCubic (automorphismV g) B) x y z v) =
    automorphismV g 0
  rw [automorphismV_A_q_pullback, hB]
  simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero]

namespace FixedFrame

def cyclicAutomorphism : CompactAutomorphism :=
  realSwap02Automorphism.comp realSwap01Automorphism

def cyclicV : V ≃ₗ[ℝ] V := automorphismV cyclicAutomorphism

theorem cyclicV_coordinates (x : V) :
    (cyclicV x : Albert) =
      ⟨(x : Albert).d2,(x : Albert).d0,(x : Albert).d1,
        octConj (x : Albert).o02,octConj (x : Albert).o12,(x : Albert).o01⟩ := by
  change realConjugateAlbert realSwap02 (realConjugateAlbert realSwap01 (x : Albert)) = _
  rw [realSwap01_coordinates, realSwap02_coordinates, octConj_conj]

@[simp] theorem cyclicV_h0 : cyclicV (h 0) = h 1 := by
  apply Subtype.ext; rw [cyclicV_coordinates]; apply Albert.ext <;> norm_num [h, e, unit, octConj]

@[simp] theorem cyclicV_h1 : cyclicV (h 1) = h 2 := by
  apply Subtype.ext; rw [cyclicV_coordinates]; apply Albert.ext <;> norm_num [h, e, unit, octConj]

@[simp] theorem cyclicV_h2 : cyclicV (h 2) = h 0 := by
  apply Subtype.ext; rw [cyclicV_coordinates]; apply Albert.ext <;> norm_num [h, e, unit, octConj]

@[simp] theorem cyclicV_X01 (u : Octonion) : cyclicV (X01 u) = X12 u := by
  apply Subtype.ext; rw [cyclicV_coordinates]; apply Albert.ext <;> simp [X01, X12, octConj]

@[simp] theorem cyclicV_X02 (u : Octonion) : cyclicV (X02 u) = X01 (octConj u) := by
  apply Subtype.ext; rw [cyclicV_coordinates]; apply Albert.ext <;> simp [X01, X02, octConj]

@[simp] theorem cyclicV_X12 (u : Octonion) : cyclicV (X12 u) = X02 (octConj u) := by
  apply Subtype.ext; rw [cyclicV_coordinates]; apply Albert.ext <;> simp [X02, X12, octConj]

structure ThreeFrameScalarData (B : SymmetricCubic) where
  a : Fin 3 → ℝ
  b : Fin 3 → ℝ
  c : Fin 3 → ℝ
  on_h_self : ∀ i, KB B (h i) (h i) = a i • h i
  on_complementary_diagonal : ∀ (i j : Fin 3), i ≠ j →
    KB B (h i) (h j + (1/2 : ℝ) • h i) = b i • (h j + (1/2 : ℝ) • h i)
  on_X01 : ∀ u : Octonion,
    KB B (h 0) (X01 u) = c 0 • X01 u ∧
    KB B (h 1) (X01 u) = c 1 • X01 u ∧
    KB B (h 2) (X01 u) = b 2 • X01 u
  on_X02 : ∀ u : Octonion,
    KB B (h 0) (X02 u) = c 0 • X02 u ∧
    KB B (h 1) (X02 u) = b 1 • X02 u ∧
    KB B (h 2) (X02 u) = c 2 • X02 u
  on_X12 : ∀ u : Octonion,
    KB B (h 0) (X12 u) = b 0 • X12 u ∧
    KB B (h 1) (X12 u) = c 1 • X12 u ∧
    KB B (h 2) (X12 u) = c 2 • X12 u

theorem h_pair_coefficients (i j : Fin 3) (hij : i ≠ j)
    (u v r s : ℝ) (heq : u • h i + v • h j = r • h i + s • h j) :
    u = r ∧ v = s := by
  have h0 := congrArg (fun x : V => (x : Albert).d0) heq
  have h1 := congrArg (fun x : V => (x : Albert).d1) heq
  have h2 := congrArg (fun x : V => (x : Albert).d2) heq
  fin_cases i <;> fin_cases j
  all_goals first | exact False.elim (hij rfl) | skip
  all_goals norm_num [h, e, unit] at h0 h1 h2
  all_goals constructor <;> linarith

theorem ThreeFrameScalarData.cross_h {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) (i j : Fin 3) (hij : i ≠ j) :
    KB B (h i) (h j) = data.b i • h j + ((data.b i - data.a i)/2) • h i := by
  calc KB B (h i) (h j)
    _ = KB B (h i) (h j + (1/2 : ℝ) • h i) - (1/2 : ℝ) • KB B (h i) (h i) := by
      rw [map_add, map_smul]; module
    _ = data.b i • (h j + (1/2 : ℝ) • h i) - (1/2 : ℝ) • (data.a i • h i) := by
      rw [data.on_complementary_diagonal i j hij, data.on_h_self]
    _ = _ := by module

theorem ThreeFrameScalarData.a_eq_b_sub_two_b {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) (i j : Fin 3) (hij : i ≠ j) :
    data.a i = data.b i - 2 * data.b j := by
  have hcross : ((data.b i - data.a i)/2) • h i + data.b i • h j =
      data.b j • h i + ((data.b j - data.a j)/2) • h j := by
    calc ((data.b i - data.a i)/2) • h i + data.b i • h j
      _ = KB B (h i) (h j) := by rw [data.cross_h i j hij]; module
      _ = KB B (h j) (h i) := KB_comm B (h i) (h j)
      _ = _ := data.cross_h j i hij.symm
  linarith [(h_pair_coefficients i j hij _ _ _ _ hcross).1]

theorem KB_h_sum_zero (B : SymmetricCubic) (v : V) :
    KB B (h 0) v + KB B (h 1) v + KB B (h 2) v = 0 := by
  simpa only [map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply] using
    congrArg (fun x : V => KB B x v) h_sum_zero

theorem ThreeFrameScalarData.slot_relations {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) :
    data.c 0 + data.c 1 + data.b 2 = 0 ∧
      data.c 0 + data.b 1 + data.c 2 = 0 ∧
      data.b 0 + data.c 1 + data.c 2 = 0 := by
  have h01 := KB_h_sum_zero B (X01 (octScalar 1))
  obtain ⟨hx0,hx1,hx2⟩ := data.on_X01 (octScalar 1)
  rw [hx0,hx1,hx2] at h01
  have r01 := congrArg (fun x : V => (x : Albert).o01.1.re) h01
  have h02 := KB_h_sum_zero B (X02 (octScalar 1))
  obtain ⟨hy0,hy1,hy2⟩ := data.on_X02 (octScalar 1)
  rw [hy0,hy1,hy2] at h02
  have r02 := congrArg (fun x : V => (x : Albert).o02.1.re) h02
  have h12 := KB_h_sum_zero B (X12 (octScalar 1))
  obtain ⟨hz0,hz1,hz2⟩ := data.on_X12 (octScalar 1)
  rw [hz0,hz1,hz2] at h12
  have r12 := congrArg (fun x : V => (x : Albert).o12.1.re) h12
  norm_num [X01, X02, X12, octScalar] at r01 r02 r12
  exact ⟨r01,r02,r12⟩

theorem ThreeFrameScalarData.common_coefficients {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) :
    ∃ b : ℝ, data.a 0 = -b ∧ data.b 0 = b ∧ data.c 0 = -b/2 := by
  have h01 := data.a_eq_b_sub_two_b 0 1 (by decide)
  have h02 := data.a_eq_b_sub_two_b 0 2 (by decide)
  have h10 := data.a_eq_b_sub_two_b 1 0 (by decide)
  have h12 := data.a_eq_b_sub_two_b 1 2 (by decide)
  obtain ⟨hc01,hc02,hc12⟩ := data.slot_relations
  exact ⟨data.b 0, by linarith, rfl, by linarith⟩

theorem h1_coarse_actions_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ a b c : ℝ, KB B (h 1) (h 1) = a • h 1 ∧
      (∀ j : Fin 3, j ≠ 1 →
        KB B (h 1) (h j + (1/2 : ℝ) • h 1) = b • (h j + (1/2 : ℝ) • h 1)) ∧
      (∀ u : Octonion, KB B (h 1) (X01 u) = c • X01 u) ∧
      (∀ u : Octonion, KB B (h 1) (X02 u) = b • X02 u) ∧
      (∀ u : Octonion, KB B (h 1) (X12 u) = c • X12 u) := by
  let BT := pullbackCubic cyclicV B
  obtain ⟨a,b,c,ha,hd,h01,h02,h12⟩ :=
    h0_coarse_actions_of_A_q_zero BT (A_q_pullback_zero cyclicAutomorphism B hB)
  have transfer (x y : V) (r : ℝ) (hh : KB BT x y = r • y) :
      KB B (cyclicV x) (cyclicV y) = r • cyclicV y :=
    scalar_action_of_pullback cyclicAutomorphism B x y r hh
  refine ⟨a,b,c,by simpa only [cyclicV_h0] using transfer (h 0) (h 0) a ha,
    fun j hj => ?_,
    fun u => by simpa only [cyclicV_h0, cyclicV_X02, octConj_conj] using transfer (h 0) (X02 (octConj u)) c (h02 (octConj u)),
    fun u => by simpa only [cyclicV_h0, cyclicV_X12, octConj_conj] using transfer (h 0) (X12 (octConj u)) b (h12 (octConj u)),
    fun u => by simpa only [cyclicV_h0, cyclicV_X01] using transfer (h 0) (X01 u) c (h01 u)⟩
  fin_cases j
  · change KB B (h 1) (h 0 + (1/2 : ℝ) • h 1) = b • (h 0 + (1/2 : ℝ) • h 1)
    simpa only [map_add, map_smul, cyclicV_h0, cyclicV_h2] using
      transfer (h 0) (h 2 + (1/2 : ℝ) • h 0) b (hd 2 (by decide))
  · exact False.elim (hj rfl)
  · change KB B (h 1) (h 2 + (1/2 : ℝ) • h 1) = b • (h 2 + (1/2 : ℝ) • h 1)
    simpa only [map_add, map_smul, cyclicV_h0, cyclicV_h1] using
      transfer (h 0) (h 1 + (1/2 : ℝ) • h 0) b (hd 1 (by decide))

theorem h2_coarse_actions_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ a b c : ℝ, KB B (h 2) (h 2) = a • h 2 ∧
      (∀ j : Fin 3, j ≠ 2 →
        KB B (h 2) (h j + (1/2 : ℝ) • h 2) = b • (h j + (1/2 : ℝ) • h 2)) ∧
      (∀ u : Octonion, KB B (h 2) (X01 u) = b • X01 u) ∧
      (∀ u : Octonion, KB B (h 2) (X02 u) = c • X02 u) ∧
      (∀ u : Octonion, KB B (h 2) (X12 u) = c • X12 u) := by
  let BT := pullbackCubic cyclicV B
  obtain ⟨a,b,c,ha,hd,h01,h02,h12⟩ :=
    h1_coarse_actions_of_A_q_zero BT (A_q_pullback_zero cyclicAutomorphism B hB)
  have transfer (x y : V) (r : ℝ) (hh : KB BT x y = r • y) :
      KB B (cyclicV x) (cyclicV y) = r • cyclicV y :=
    scalar_action_of_pullback cyclicAutomorphism B x y r hh
  refine ⟨a,b,c,by simpa only [cyclicV_h1] using transfer (h 1) (h 1) a ha,
    fun j hj => ?_,
    fun u => by simpa only [cyclicV_h1, cyclicV_X02, octConj_conj] using transfer (h 1) (X02 (octConj u)) b (h02 (octConj u)),
    fun u => by simpa only [cyclicV_h1, cyclicV_X12, octConj_conj] using transfer (h 1) (X12 (octConj u)) c (h12 (octConj u)),
    fun u => by simpa only [cyclicV_h1, cyclicV_X01] using transfer (h 1) (X01 u) c (h01 u)⟩
  fin_cases j
  · change KB B (h 2) (h 0 + (1/2 : ℝ) • h 2) = b • (h 0 + (1/2 : ℝ) • h 2)
    simpa only [map_add, map_smul, cyclicV_h1, cyclicV_h2] using
      transfer (h 1) (h 2 + (1/2 : ℝ) • h 1) b (hd 2 (by decide))
  · change KB B (h 2) (h 1 + (1/2 : ℝ) • h 2) = b • (h 1 + (1/2 : ℝ) • h 2)
    simpa only [map_add, map_smul, cyclicV_h1, cyclicV_h0] using
      transfer (h 1) (h 0 + (1/2 : ℝ) • h 1) b (hd 0 (by decide))
  · exact False.elim (hj rfl)

theorem threeFrameScalarData_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) : Nonempty (ThreeFrameScalarData B) := by
  obtain ⟨a0,b0,c0,ha0,hd0,h010,h020,h120⟩ := h0_coarse_actions_of_A_q_zero B hB
  obtain ⟨a1,b1,c1,ha1,hd1,h011,h021,h121⟩ := h1_coarse_actions_of_A_q_zero B hB
  obtain ⟨a2,b2,c2,ha2,hd2,h012,h022,h122⟩ := h2_coarse_actions_of_A_q_zero B hB
  refine ⟨{
    a := ![a0,a1,a2], b := ![b0,b1,b2], c := ![c0,c1,c2]
    on_h_self := fun i => by fin_cases i <;> [simpa using ha0; simpa using ha1; simpa using ha2]
    on_complementary_diagonal := fun i j hij => by
      fin_cases i <;> [simpa using hd0 j hij.symm; simpa using hd1 j hij.symm; simpa using hd2 j hij.symm]
    on_X01 := fun u => ⟨h010 u, h011 u, h012 u⟩
    on_X02 := fun u => ⟨h020 u, h021 u, h022 u⟩
    on_X12 := fun u => ⟨h120 u, h121 u, h122 u⟩ }⟩

theorem KA_h_self (i : Fin 3) : KA (h i) (h i) = (-1 : ℝ) • h i := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  fin_cases i <;> apply Subtype.ext <;> apply Albert.ext <;>
    norm_num [KA_apply, project_coe, traceless, trace, h, e, unit,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul, octConj, hnorm]

theorem KA_h_cross (i j : Fin 3) (hij : i ≠ j) :
    KA (h i) (h j) = h i + h j := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  fin_cases i <;> fin_cases j
  all_goals first | exact False.elim (hij rfl) | skip
  all_goals apply Subtype.ext; apply Albert.ext <;>
    norm_num [KA_apply, project_coe, traceless, trace, h, e, unit,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul, octConj, hnorm]

theorem KA_h0_X01 (u : Octonion) :
    KA (h 0) (X01 u) = -(1/2 : ℝ) • X01 u := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  have hneg (x : Albert) : -x = ⟨-x.d0,-x.d1,-x.d2,-x.o01,-x.o02,-x.o12⟩ := rfl
  have hconj : octConj (0 : Octonion) = 0 := by simp [octConj]
  apply Subtype.ext; apply Albert.ext <;>
    simp [KA_apply, project_coe, traceless, trace, h, e, X01,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul_zero_right, hconj, hnorm, hneg, smul_smul] <;> norm_num

theorem KA_h0_X02 (u : Octonion) :
    KA (h 0) (X02 u) = -(1/2 : ℝ) • X02 u := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  have hneg (x : Albert) : -x = ⟨-x.d0,-x.d1,-x.d2,-x.o01,-x.o02,-x.o12⟩ := rfl
  have hconj : octConj (0 : Octonion) = 0 := by simp [octConj]
  apply Subtype.ext; apply Albert.ext <;>
    simp [KA_apply, project_coe, traceless, trace, h, e, X02,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul_zero_left, octMul_zero_right, hconj, hnorm, hneg, smul_smul] <;> norm_num

theorem KA_h0_X12 (u : Octonion) :
    KA (h 0) (X12 u) = X12 u := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  have hconj : octConj (0 : Octonion) = 0 := by simp [octConj]
  apply Subtype.ext; apply Albert.ext <;>
    simp [KA_apply, project_coe, traceless, trace, h, e, X12,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul_zero_left, octMul_zero_right, hconj, hnorm, smul_smul] <;> norm_num

theorem frameD_eq_h01 :
    frameD = (-1/3 : ℝ) • h 0 + (-2/3 : ℝ) • h 1 := by
  have hneg (x : Albert) : -x = ⟨-x.d0,-x.d1,-x.d2,-x.o01,-x.o02,-x.o12⟩ := rfl
  apply Subtype.ext; apply Albert.ext <;> norm_num [frameD, h, e, unit, hneg]

theorem KA_h0_frameD : KA (h 0) frameD = frameD := by
  rw [frameD_eq_h01, map_add, map_smul, map_smul, KA_h_self, KA_h_cross 0 1 (by decide)]
  module

theorem fixedFrame_gate_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ b : ℝ, KB B (h 0) = b • KA (h 0) := by
  obtain ⟨data⟩ := threeFrameScalarData_of_A_q_zero B hB
  obtain ⟨b,ha0,hb0,hc0⟩ := data.common_coefficients
  refine ⟨b, LinearMap.ext fun x => ?_⟩
  change KB B (h 0) x = b • KA (h 0) x
  have hh0 : KB B (h 0) (h 0) = b • KA (h 0) (h 0) := by
    rw [data.on_h_self 0, ha0, KA_h_self, smul_smul]; congr 1; ring
  have hd : KB B (h 0) frameD = b • KA (h 0) frameD := by
    have h1 := data.on_complementary_diagonal 0 1 (by decide)
    rw [h1_half_h0_eq_frameD, map_smul, hb0] at h1
    have h1' := congrArg (fun v : V => (-2/3 : ℝ) • v) h1
    rw [KA_h0_frameD]
    simpa only [smul_smul, show (-2/3 : ℝ)*-(3/2) = 1 by norm_num,
      show (-2/3 : ℝ)*(b*-(3/2)) = b by ring, one_smul] using h1'
  have h01 (u : Octonion) : KB B (h 0) (X01 u) = b • KA (h 0) (X01 u) := by
    rw [(data.on_X01 u).1, hc0, KA_h0_X01, smul_smul]; congr 1; ring
  have h02 (u : Octonion) : KB B (h 0) (X02 u) = b • KA (h 0) (X02 u) := by
    rw [(data.on_X02 u).1, hc0, KA_h0_X02, smul_smul]; congr 1; ring
  have h12 (u : Octonion) : KB B (h 0) (X12 u) = b • KA (h 0) (X12 u) := by
    rw [(data.on_X12 u).1, hb0, KA_h0_X12]
  rcases hs : (frameCoordinates x).2.2.2 with ⟨u,v⟩
  rw [frame_decompose x, hs, frameSpin_apply]
  simp only [map_add, map_smul, hh0, hd, h01, h02, h12, smul_add, smul_smul]
  module

end FixedFrame
end
end AlbertRecognition
