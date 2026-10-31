import Erdos272.Arithmetic.BatchSourceBlocks208

/-! For physical sizes beyond twice the defect range, every nonzero
multiplicity is simply the defect. The checker below is proved equal to the
original checker before it is used for any numerical certificate. -/
namespace JSP233.BatchSourceLinear208
open BatchSource208 FastSource208
set_option maxHeartbeats 0

theorem fastMultiplicity_near {s d : Nat} (hd : d ≤ s) (hs : 2 * d < s) :
    fastMultiplicity s (s - d) = d := by
  have hq : s - d ≠ 0 := by omega
  have hdiv : s / (s - d) = 1 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  simp only [fastMultiplicity, if_neg hq, hdiv]
  omega

def checkRowFrom (a : Nat → Nat) (s e mass : Nat) : List Nat → Bool
  | [] => true
  | b :: bs => decide (b ≤ mass) &&
      checkRowFrom a s (e + 1) (mass + a (s - (e + 1)) * (e + 1)) bs

theorem checkRowFrom_eq {a : Nat → Nat} {s e mass : Nat} (targets : List Nat)
    (hs : 2 * (e + targets.length) < s) :
    checkRowFrom a s e mass targets = BatchSource208.checkRowFrom a s e mass targets := by
  induction targets generalizing e mass with
  | nil => rfl
  | cons b bs ih =>
    have hd : e + 1 ≤ s := by simp only [List.length_cons] at hs; omega
    have hhalf : 2 * (e + 1) < s := by simp only [List.length_cons] at hs; omega
    have htail : 2 * (e + 1 + bs.length) < s := by
      simp only [List.length_cons] at hs
      omega
    simp only [checkRowFrom, BatchSource208.checkRowFrom, fastMultiplicity_near hd hhalf]
    rw [ih htail]

def checkBlock (a : Nat → Nat) (T H : Nat) (targets : List Nat) : Bool :=
  if 2 * targets.length < T then
    (List.range (H + 1 - T)).all fun j => checkRowFrom a (T + j) 0 0 targets
  else BatchSource208.checkBlock a T H targets

theorem checkBlock_eq (a : Nat → Nat) (T H : Nat) (targets : List Nat) :
    checkBlock a T H targets = BatchSource208.checkBlock a T H targets := by
  unfold checkBlock
  split_ifs with h
  · apply congrArg (List.all (List.range (H + 1 - T)))
    funext j
    exact checkRowFrom_eq targets (by omega)
  · rfl

theorem checked {a : Nat → Nat} {T H : Nat} {targets : List Nat}
    (hc : checkBlock a T H targets = true) :
    BatchSource208.checkBlock a T H targets = true := by
  rwa [checkBlock_eq] at hc

#print axioms fastMultiplicity_near
#print axioms checkRowFrom_eq
#print axioms checkBlock_eq
#print axioms checked
end JSP233.BatchSourceLinear208
