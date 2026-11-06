module

public import Glennie.Automorphism
public import Glennie.Theorems.Frames
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module

@[expose] public section

namespace Glennie.Compact.Affine20

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev Triple := Fin 3 → Fin 3 → Albert

abbrev Ledger54 :=
  (Fin 3 → Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) ×
    (Fin 3 → Fin 3 → ℝ)

def ledger54 (T : Triple) : Ledger54 :=
  (ledger (T 0) (T 1) (T 2), fun i j => inner (T 0 i) (T 1 j),
    fun j k => inner (T 1 j) (T 2 k), fun k i => inner (T 2 k) (T 0 i))

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have hb : (List.finRange 3).all (fun i => decide (i = 0 ∨ i = 1 ∨ i = 2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hb i (List.mem_finRange i))

def mapAtoms (g : CompactAutomorphism) (T : Triple) : Triple :=
  fun a i => g.equiv (T a i)

theorem mapAtoms_apply (g : CompactAutomorphism) (T : Triple) (a i : Fin 3) :
    mapAtoms g T a i = g.equiv (T a i) := rfl

theorem mapAtoms_slot (g : CompactAutomorphism) (T : Triple) (a : Fin 3) :
    mapAtoms g T a = fun i => g.equiv (T a i) := rfl

theorem ledger54_C (T : Triple) (i j k : Fin 3) :
    (ledger54 T).1 i j k = ledger (T 0) (T 1) (T 2) i j k := rfl

theorem ledger54_P (T : Triple) (i j : Fin 3) :
    (ledger54 T).2.1 i j = inner (T 0 i) (T 1 j) := rfl

theorem ledger54_Q (T : Triple) (j k : Fin 3) :
    (ledger54 T).2.2.1 j k = inner (T 1 j) (T 2 k) := rfl

theorem ledger54_R (T : Triple) (k i : Fin 3) :
    (ledger54 T).2.2.2 k i = inner (T 2 k) (T 0 i) := rfl

theorem ledger54_map (g : CompactAutomorphism) (T : Triple) :
    ledger54 (mapAtoms g T) = ledger54 T := by
  refine Prod.ext (funext fun i => funext fun j => funext fun k => g.ledger_map (T 0) (T 1) (T 2) i j k)
    (Prod.ext (funext fun i => funext fun j => g.inner_map (T 0 i) (T 1 j))
      (Prod.ext (funext fun j => funext fun k => g.inner_map (T 1 j) (T 2 k))
        (funext fun k => funext fun i => g.inner_map (T 2 k) (T 0 i))))

structure InDomain (L : Ledger54) : Prop where
  P_row : ∀ i, L.2.1 i 0 + L.2.1 i 1 + L.2.1 i 2 = 1
  P_col : ∀ j, L.2.1 0 j + L.2.1 1 j + L.2.1 2 j = 1
  Q_row : ∀ j, L.2.2.1 j 0 + L.2.2.1 j 1 + L.2.2.1 j 2 = 1
  Q_col : ∀ k, L.2.2.1 0 k + L.2.2.1 1 k + L.2.2.1 2 k = 1
  R_row : ∀ k, L.2.2.2 k 0 + L.2.2.2 k 1 + L.2.2.2 k 2 = 1
  R_col : ∀ i, L.2.2.2 0 i + L.2.2.2 1 i + L.2.2.2 2 i = 1
  C_k : ∀ i j, L.1 i j 0 + L.1 i j 1 + L.1 i j 2 = L.2.1 i j
  C_i : ∀ j k, L.1 0 j k + L.1 1 j k + L.1 2 j k = L.2.2.1 j k
  C_j : ∀ k i, L.1 i 0 k + L.1 i 1 k + L.1 i 2 k = L.2.2.2 k i

theorem pair_row (p q : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (i : Fin 3) :
    inner (p i) (q 0) + inner (p i) (q 1) + inner (p i) (q 2) = 1 := by
  rw [← inner_add_right, ← inner_add_right, hq.sum_unit, inner_unit_right, hp.trace_one]

theorem pair_col (p q : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (j : Fin 3) :
    inner (p 0) (q j) + inner (p 1) (q j) + inner (p 2) (q j) = 1 := by
  rw [inner_comm (p 0), inner_comm (p 1), inner_comm (p 2)]
  exact pair_row q p hq hp j

theorem ledger_margin3 (p q r : Fin 3 → Albert) (hr : Frame r) (i j : Fin 3) :
    ledger p q r i j 0 + ledger p q r i j 1 + ledger p q r i j 2 = inner (p i) (q j) := by
  simp only [ledger]
  rw [← trace_add, ← trace_add, ← jordan_add_right, ← jordan_add_right, hr.sum_unit,
    jordan_unit_right]
  rfl

theorem ledger54_inDomain (T : Triple) (hT : ∀ a, Frame (T a)) : InDomain (ledger54 T) where
  P_row i := by simp only [ledger54_P]; exact pair_row (T 0) (T 1) (hT 0) (hT 1) i
  P_col j := by simp only [ledger54_P]; exact pair_col (T 0) (T 1) (hT 0) (hT 1) j
  Q_row j := by simp only [ledger54_Q]; exact pair_row (T 1) (T 2) (hT 1) (hT 2) j
  Q_col k := by simp only [ledger54_Q]; exact pair_col (T 1) (T 2) (hT 1) (hT 2) k
  R_row k := by simp only [ledger54_R]; exact pair_row (T 2) (T 0) (hT 2) (hT 0) k
  R_col i := by simp only [ledger54_R]; exact pair_col (T 2) (T 0) (hT 2) (hT 0) i
  C_k i j := by simp only [ledger54_C, ledger54_P]; exact ledger_margin3 (T 0) (T 1) (T 2) (hT 2) i j
  C_i j k := by
    simp only [ledger54_C, ledger54_Q]
    rw [ledger_cyclic (T 0) (T 1) (T 2) 0 j k, ledger_cyclic (T 0) (T 1) (T 2) 1 j k,
      ledger_cyclic (T 0) (T 1) (T 2) 2 j k]
    exact ledger_margin3 (T 1) (T 2) (T 0) (hT 0) j k
  C_j k i := by
    simp only [ledger54_C, ledger54_R]
    rw [ledger_cyclic (T 0) (T 1) (T 2) i 0 k, ledger_cyclic (T 0) (T 1) (T 2) i 1 k,
      ledger_cyclic (T 0) (T 1) (T 2) i 2 k, ledger_cyclic (T 1) (T 2) (T 0) 0 k i,
      ledger_cyclic (T 1) (T 2) (T 0) 1 k i, ledger_cyclic (T 1) (T 2) (T 0) 2 k i]
    exact ledger_margin3 (T 2) (T 0) (T 1) (hT 1) k i

def ext3 (x y : ℝ) : Fin 3 → ℝ := ![x, y, -(x + y)]

def lift4 (a b c d : ℝ) (i j : Fin 3) : ℝ := ext3 (ext3 a b j) (ext3 c d j) i

def lift8 (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (i j k : Fin 3) : ℝ :=
  ext3 (ext3 (ext3 h000 h001 k) (ext3 h010 h011 k) j)
    (ext3 (ext3 h100 h101 k) (ext3 h110 h111 k) j) i

theorem ext3_zero (x y : ℝ) : ext3 x y 0 = x := rfl
theorem ext3_one (x y : ℝ) : ext3 x y 1 = y := rfl
theorem ext3_two (x y : ℝ) : ext3 x y 2 = -(x + y) := rfl

theorem ext3_reconstruct (v : Fin 3 → ℝ) (h : v 0 + v 1 + v 2 = 0) (i : Fin 3) :
    ext3 (v 0) (v 1) i = v i := by
  rcases fin3_cases i with rfl | rfl | rfl
  · rfl
  · rfl
  · rw [ext3_two]; linarith

theorem lift4_reconstruct (M : Fin 3 → Fin 3 → ℝ) (hr : ∀ i, M i 0 + M i 1 + M i 2 = 0)
    (hc : ∀ j, M 0 j + M 1 j + M 2 j = 0) (i j : Fin 3) :
    lift4 (M 0 0) (M 0 1) (M 1 0) (M 1 1) i j = M i j := by
  unfold lift4
  rw [ext3_reconstruct (M 0) (hr 0) j, ext3_reconstruct (M 1) (hr 1) j]
  exact ext3_reconstruct (fun l => M l j) (hc j) i

theorem lift8_reconstruct (H : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hx : ∀ j k, H 0 j k + H 1 j k + H 2 j k = 0)
    (hy : ∀ i k, H i 0 k + H i 1 k + H i 2 k = 0)
    (hz : ∀ i j, H i j 0 + H i j 1 + H i j 2 = 0) (i j k : Fin 3) :
    lift8 (H 0 0 0) (H 0 0 1) (H 0 1 0) (H 0 1 1) (H 1 0 0) (H 1 0 1) (H 1 1 0) (H 1 1 1)
      i j k = H i j k := by
  unfold lift8
  rw [ext3_reconstruct (H 0 0) (hz 0 0) k, ext3_reconstruct (H 0 1) (hz 0 1) k,
    ext3_reconstruct (H 1 0) (hz 1 0) k, ext3_reconstruct (H 1 1) (hz 1 1) k,
    ext3_reconstruct (fun l => H 0 l k) (hy 0 k) j, ext3_reconstruct (fun l => H 1 l k) (hy 1 k) j]
  exact ext3_reconstruct (fun l => H l j k) (hx j k) i

def centred (L : Ledger54) (i j k : Fin 3) : ℝ :=
  L.1 i j k - (L.2.1 i j + L.2.2.1 j k + L.2.2.2 k i) / 3 + 2 / 9

def encode20 (L : Ledger54) : Fin 20 → ℝ :=
  ![L.2.1 0 0 - 1 / 3, L.2.1 0 1 - 1 / 3, L.2.1 1 0 - 1 / 3, L.2.1 1 1 - 1 / 3,
    L.2.2.1 0 0 - 1 / 3, L.2.2.1 0 1 - 1 / 3, L.2.2.1 1 0 - 1 / 3, L.2.2.1 1 1 - 1 / 3,
    L.2.2.2 0 0 - 1 / 3, L.2.2.2 0 1 - 1 / 3, L.2.2.2 1 0 - 1 / 3, L.2.2.2 1 1 - 1 / 3,
    centred L 0 0 0, centred L 0 0 1, centred L 0 1 0, centred L 0 1 1,
    centred L 1 0 0, centred L 1 0 1, centred L 1 1 0, centred L 1 1 1]

def decP (v : Fin 20 → ℝ) (i j : Fin 3) : ℝ := 1 / 3 + lift4 (v 0) (v 1) (v 2) (v 3) i j
def decQ (v : Fin 20 → ℝ) (j k : Fin 3) : ℝ := 1 / 3 + lift4 (v 4) (v 5) (v 6) (v 7) j k
def decR (v : Fin 20 → ℝ) (k i : Fin 3) : ℝ := 1 / 3 + lift4 (v 8) (v 9) (v 10) (v 11) k i

def decC (v : Fin 20 → ℝ) (i j k : Fin 3) : ℝ :=
  lift8 (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) i j k +
    (decP v i j + decQ v j k + decR v k i) / 3 - 2 / 9

def decode20 (v : Fin 20 → ℝ) : Ledger54 := (decC v, decP v, decQ v, decR v)

theorem decode20_C (v : Fin 20 → ℝ) : (decode20 v).1 = decC v := rfl
theorem decode20_P (v : Fin 20 → ℝ) : (decode20 v).2.1 = decP v := rfl
theorem decode20_Q (v : Fin 20 → ℝ) : (decode20 v).2.2.1 = decQ v := rfl
theorem decode20_R (v : Fin 20 → ℝ) : (decode20 v).2.2.2 = decR v := rfl

theorem decP_encode (L : Ledger54) (h : InDomain L) (i j : Fin 3) :
    decP (encode20 L) i j = L.2.1 i j := by
  have key : lift4 (encode20 L 0) (encode20 L 1) (encode20 L 2) (encode20 L 3) i j =
      L.2.1 i j - 1 / 3 :=
    lift4_reconstruct (fun i j => L.2.1 i j - 1 / 3)
      (fun i => by linarith [h.P_row i]) (fun j => by linarith [h.P_col j]) i j
  change 1 / 3 + lift4 (encode20 L 0) (encode20 L 1) (encode20 L 2) (encode20 L 3) i j = L.2.1 i j
  rw [key]; ring

theorem decQ_encode (L : Ledger54) (h : InDomain L) (j k : Fin 3) :
    decQ (encode20 L) j k = L.2.2.1 j k := by
  have key : lift4 (encode20 L 4) (encode20 L 5) (encode20 L 6) (encode20 L 7) j k =
      L.2.2.1 j k - 1 / 3 :=
    lift4_reconstruct (fun j k => L.2.2.1 j k - 1 / 3)
      (fun j => by linarith [h.Q_row j]) (fun k => by linarith [h.Q_col k]) j k
  change 1 / 3 + lift4 (encode20 L 4) (encode20 L 5) (encode20 L 6) (encode20 L 7) j k = L.2.2.1 j k
  rw [key]; ring

theorem decR_encode (L : Ledger54) (h : InDomain L) (k i : Fin 3) :
    decR (encode20 L) k i = L.2.2.2 k i := by
  have key : lift4 (encode20 L 8) (encode20 L 9) (encode20 L 10) (encode20 L 11) k i =
      L.2.2.2 k i - 1 / 3 :=
    lift4_reconstruct (fun k i => L.2.2.2 k i - 1 / 3)
      (fun k => by linarith [h.R_row k]) (fun i => by linarith [h.R_col i]) k i
  change 1 / 3 + lift4 (encode20 L 8) (encode20 L 9) (encode20 L 10) (encode20 L 11) k i = L.2.2.2 k i
  rw [key]; ring

theorem decC_encode (L : Ledger54) (h : InDomain L) (i j k : Fin 3) :
    decC (encode20 L) i j k = L.1 i j k := by
  have key : lift8 (encode20 L 12) (encode20 L 13) (encode20 L 14) (encode20 L 15)
      (encode20 L 16) (encode20 L 17) (encode20 L 18) (encode20 L 19) i j k = centred L i j k :=
    lift8_reconstruct (centred L)
      (fun j k => by simp only [centred]; linarith [h.C_i j k, h.P_col j, h.R_row k])
      (fun i k => by simp only [centred]; linarith [h.C_j k i, h.P_row i, h.Q_col k])
      (fun i j => by simp only [centred]; linarith [h.C_k i j, h.Q_row j, h.R_col i]) i j k
  show lift8 (encode20 L 12) (encode20 L 13) (encode20 L 14) (encode20 L 15)
      (encode20 L 16) (encode20 L 17) (encode20 L 18) (encode20 L 19) i j k +
      (decP (encode20 L) i j + decQ (encode20 L) j k + decR (encode20 L) k i) / 3 - 2 / 9 =
    L.1 i j k
  rw [key, decP_encode L h, decQ_encode L h, decR_encode L h]
  simp only [centred]; ring

theorem decode_encode (L : Ledger54) (h : InDomain L) : decode20 (encode20 L) = L := by
  refine Prod.ext (funext fun i => funext fun j => funext fun k => decC_encode L h i j k)
    (Prod.ext (funext fun i => funext fun j => decP_encode L h i j)
      (Prod.ext (funext fun j => funext fun k => decQ_encode L h j k)
        (funext fun k => funext fun i => decR_encode L h k i)))

theorem decode_encode_frames (T : Triple) (hT : ∀ a, Frame (T a)) :
    decode20 (encode20 (ledger54 T)) = ledger54 T :=
  decode_encode _ (ledger54_inDomain T hT)

def AffineComb {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E → F) : Prop :=
  ∀ (x y : E) (t : ℝ), f (x + t • (y - x)) = f x + t • (f y - f x)

theorem AffineComb.comp {E F G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] [AddCommGroup G] [Module ℝ G] {f : E → F} {g : F → G}
    (hg : AffineComb g) (hf : AffineComb f) : AffineComb (fun x => g (f x)) := fun x y t => by
  show g (f (x + t • (y - x))) = g (f x) + t • (g (f y) - g (f x))
  rw [hf x y t]; exact hg (f x) (f y) t

theorem fin20_cases (n : Fin 20) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
      n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨
        n = 19 := by
  have hb : (List.finRange 20).all (fun n => decide (n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
      n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨
        n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hb n (List.mem_finRange n))

theorem encode20_affine : AffineComb encode20 := fun x y t => by
  funext n
  rcases fin20_cases n with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (dsimp [encode20, centred]; ring)

theorem decode20_affine : AffineComb decode20 := fun x y t => by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
      rcases fin3_cases k with rfl | rfl | rfl <;>
      (dsimp [decode20, decC, decP, decQ, decR, lift8, lift4, ext3]; ring)
  · funext i j
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
      (dsimp [decode20, decP, lift4, ext3]; ring)
  · funext j k
    rcases fin3_cases j with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      (dsimp [decode20, decQ, lift4, ext3]; ring)
  · funext k i
    rcases fin3_cases k with rfl | rfl | rfl <;> rcases fin3_cases i with rfl | rfl | rfl <;>
      (dsimp [decode20, decR, lift4, ext3]; ring)

theorem AffineComb.continuous20 {f : (Fin 20 → ℝ) → (Fin 20 → ℝ)} (hf : AffineComb f) :
    Continuous f := by
  have hsmul (t : ℝ) (y : Fin 20 → ℝ) : f (t • y) - f 0 = t • (f y - f 0) := by
    have h := hf 0 y t; rw [sub_zero, zero_add] at h; rw [h]; abel
  have hadd (x y : Fin 20 → ℝ) : f (x + y) - f 0 = (f x - f 0) + (f y - f 0) := by
    have h := hf ((2 : ℝ) • x) ((2 : ℝ) • y) (1 / 2)
    have e : (2 : ℝ) • x + (1 / 2 : ℝ) • ((2 : ℝ) • y - (2 : ℝ) • x) = x + y := by module
    have h2x : f ((2 : ℝ) • x) = f 0 + (2 : ℝ) • (f x - f 0) := by rw [← hsmul]; abel
    have h2y : f ((2 : ℝ) • y) = f 0 + (2 : ℝ) • (f y - f 0) := by rw [← hsmul]; abel
    rw [e, h2x, h2y] at h; rw [h]; module
  have hG : Continuous (fun x => f x - f 0) :=
    LinearMap.continuous_of_finiteDimensional
      ({ toFun := fun x => f x - f 0, map_add' := hadd, map_smul' := hsmul } :
        (Fin 20 → ℝ) →ₗ[ℝ] (Fin 20 → ℝ))
  have hf' : f = fun x => (f x - f 0) + f 0 := funext fun x => by abel
  rw [hf']
  exact hG.fun_add continuous_const

end
end Glennie.Compact.Affine20
