module

public import RequestProject.MirrorContraction
public import RequestProject.CombPi1

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb

universe u

variable (P : Type u) [Preorder P]

def OrdEdge : Type u := {p : P × P // p.1 ≤ p.2}

def OrdTri : Type u := {t : P × P × P // t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2}

def orderCx : Complex2.{u} where
  V := P
  E := OrdEdge P
  F := OrdTri P
  src e := e.1.1
  tgt e := e.1.2
  base t := t.1.1
  att t :=
    [((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true),
     ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true),
     ((⟨(t.1.1, t.1.2.2), le_trans t.2.1 t.2.2⟩ : OrdEdge P), false)]
  att_isLoop _ := ⟨rfl, rfl, rfl, rfl⟩

variable {P}

def ordPos {a b : P} (h : a ≤ b) : (orderCx P).E × Bool := ((⟨(a, b), h⟩ : OrdEdge P), true)
def ordNeg {a b : P} (h : a ≤ b) : (orderCx P).E × Bool := ((⟨(a, b), h⟩ : OrdEdge P), false)

theorem isPath_ordPos {a b : P} (h : a ≤ b) :
    IsPath (orderCx P).src (orderCx P).tgt [ordPos h] a b := ⟨rfl, rfl⟩

theorem isPath_ordNeg {a b : P} (h : a ≤ b) :
    IsPath (orderCx P).src (orderCx P).tgt [ordNeg h] b a := ⟨rfl, rfl⟩

theorem htpy_ordPos_ordNeg {a b : P} (h : a ≤ b) :
    Htpy (orderCx P) a a [ordPos h, ordNeg h] [] := by
  simpa [revPath, revGerm, ordPos, ordNeg, germSrc, germTgt, orderCx] using
    htpy_append_revPath (X := orderCx P) (isPath_single (X := orderCx P) (ordPos h))

theorem htpy_ordNeg_ordPos {a b : P} (h : a ≤ b) :
    Htpy (orderCx P) b b [ordNeg h, ordPos h] [] := by
  simpa [revPath, revGerm, ordPos, ordNeg, germSrc, germTgt, orderCx] using
    htpy_append_revPath (X := orderCx P) (isPath_single (X := orderCx P) (ordNeg h))

theorem htpy_orderCx_tri {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    Htpy (orderCx P) a c [ordPos hab, ordPos hbc] [ordPos (hab.trans hbc)] := by
  have hac := hab.trans hbc
  have h1 := Htpy.append_congr (X := orderCx P) (a := a) (b := c) (c := c)
    (p := [ordPos hab, ordPos hbc]) (q := []) ⟨rfl, rfl, rfl⟩ rfl (Htpy.refl _)
    (htpy_ordNeg_ordPos hac).symm
  have h2 : Htpy (orderCx P) a c [ordPos hab, ordPos hbc, ordNeg hac, ordPos hac] [ordPos hac] :=
    Htpy.of_step ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, isPath_ordPos hac,
      Or.inr ⟨[], [ordPos hac], (⟨(a, b, c), hab, hbc⟩ : OrdTri P), rfl, rfl⟩⟩
  simpa using h1.trans h2

def ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x) (htop : ∀ x, rho x ≤ d) (x : P) :
    List ((orderCx P).E × Bool) := [ordNeg (hle x), ordPos (htop x)]

theorem isPath_ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x) (htop : ∀ x, rho x ≤ d)
    (x : P) :
    IsPath (orderCx P).src (orderCx P).tgt (ordPth d rho hle htop x) x d := ⟨rfl, rfl, rfl⟩

theorem isPath_nil' (a : P) :
    IsPath (orderCx P).src (orderCx P).tgt ([] : List ((orderCx P).E × Bool)) a a := rfl

theorem htpy_ordPos_ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y) {a b : P}
    (hab : a ≤ b) :
    Htpy (orderCx P) a d (ordPos hab :: ordPth d rho hle htop b) (ordPth d rho hle htop a) := by
  have hrs := hmono hab
  have pb2 := isPath_ordPth d rho hle htop b
  have s1 := Htpy.append_congr (isPath_ordNeg (hle a)) (isPath_ordPos (htop a)) (Htpy.refl _)
    (htpy_orderCx_tri hrs (htop b)).symm
  have s2 := (htpy_ordPos_ordNeg (hle b)).symm.congr_append (c := a) (d := d)
    (r := [ordNeg (hle a), ordPos hrs]) ⟨rfl, rfl, rfl⟩ (isPath_ordPos (htop b))
  have s3 := (htpy_orderCx_tri hrs (hle b)).congr_append (c := a) (d := d)
    (isPath_ordNeg (hle a)) pb2
  have s4 := (htpy_orderCx_tri (hle a) hab).symm.congr_append (c := a) (d := d)
    (isPath_ordNeg (hle a)) pb2
  have s5 := (htpy_ordNeg_ordPos (hle a)).congr_append (c := a) (d := d) (isPath_nil' a)
    ((isPath_ordPos hab).append pb2)
  simp only [ordPth, List.nil_append, List.cons_append] at s1 s2 s3 s4 s5 ⊢
  exact ((((s1.trans s2).trans s3).trans s4).trans s5).symm

theorem htpy_path_ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y) :
    ∀ (p : List ((orderCx P).E × Bool)) {x y : P},
      IsPath (orderCx P).src (orderCx P).tgt p x y →
      Htpy (orderCx P) x d (p ++ ordPth d rho hle htop y) (ordPth d rho hle htop x)
  | [], _, _, rfl => Htpy.refl _
  | ⟨⟨⟨a, b⟩, hab⟩, false⟩ :: p, _, y, ⟨rfl, hrest⟩ => by
      have h1 := Htpy.append_congr (isPath_ordNeg hab)
        (isPath_append_iff.mpr ⟨y, hrest, isPath_ordPth d rho hle htop y⟩)
        (Htpy.refl _) (htpy_path_ordPth d rho hle htop hmono p hrest)
      have h2 := Htpy.append_congr (isPath_ordNeg hab) (isPath_ordPth d rho hle htop a) (Htpy.refl _)
        (htpy_ordPos_ordPth d rho hle htop hmono hab).symm
      have h3 := (htpy_ordNeg_ordPos hab).congr_append (c := b) (d := d) (isPath_nil' b)
        (isPath_ordPth d rho hle htop b)
      simp only [List.nil_append, List.cons_append] at h1 h2 h3 ⊢
      exact (h1.trans h2).trans h3
  | ⟨⟨⟨a, b⟩, hab⟩, true⟩ :: p, _, y, ⟨rfl, hrest⟩ => by
      have h1 := Htpy.append_congr (isPath_ordPos hab)
        (isPath_append_iff.mpr ⟨y, hrest, isPath_ordPth d rho hle htop y⟩)
        (Htpy.refl _) (htpy_path_ordPth d rho hle htop hmono p hrest)
      have h2 := htpy_ordPos_ordPth d rho hle htop hmono hab
      simp only [List.cons_append] at h1 ⊢
      exact h1.trans h2

theorem simplyConnected_orderCx (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y) :
    SimplyConnected (orderCx P) := by
  intro a p hp
  set q := ordPth d rho hle htop (a : P)
  have hq := isPath_ordPth d rho hle htop (a : P)
  have h3 := htpy_append_revPath hq
  have h1 := Htpy.append_congr hp (isPath_append_iff.mpr ⟨d, hq, isPath_revPath hq⟩) (Htpy.refl _) h3
  have h2 := Htpy.append_congr (isPath_append_iff.mpr ⟨a, hp, hq⟩) (isPath_revPath hq)
    (htpy_path_ordPth d rho hle htop hmono p hp) (Htpy.refl _)
  exact ((by simpa [List.append_assoc] using h1.symm : Htpy (orderCx P) a a p ((p ++ q) ++ revPath q)).trans h2).trans h3

theorem isConnected_orderCx (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) : IsConnected (orderCx P) :=
  fun a b => ⟨ordPth d rho hle htop (a : P) ++ revPath (ordPth d rho hle htop (b : P)),
    isPath_append_iff.mpr ⟨d, isPath_ordPth d rho hle htop (a : P),
      isPath_revPath (isPath_ordPth d rho hle htop (b : P))⟩⟩
