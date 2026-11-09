module

public import Erdos272.Arithmetic.FastSource208
public import Erdos272.Arithmetic.TotientSieve208

@[expose] public section

/-! # One-pass kernel checks of finite source rectangles

Each physical row is accumulated once along the defect coordinate. The
checker does not recompute every prefix sum for every target. Physical sizes
can be split into independent adjacent blocks by `lower_bound_of_split`.
-/
namespace JSP233.BatchSource208
open PureSource208 FastSource208

def checkRowFrom (a : ℕ → ℕ) (s e mass : ℕ) : List ℕ → Bool
  | [] => true
  | b :: bs => decide (b ≤ mass) &&
      checkRowFrom a s (e + 1)
        (mass + a (s - (e + 1)) * fastMultiplicity s (s - (e + 1))) bs

theorem checkRowFrom_sound {a : ℕ → ℕ} {H s : ℕ}
    (ha : ∀ q, q ≤ H → a q = Nat.totient q) (hs : s ≤ H)
    (targets : List ℕ) (e mass : ℕ)
    (hlen : e + targets.length ≤ s) (hmass : mass = physicalK s e)
    (hc : checkRowFrom a s e mass targets = true) :
    ∀ j (hj : j < targets.length), targets[j] ≤ physicalK s (e + j) := by
  induction targets generalizing e mass with
  | nil =>
    intro j hj
    simp only [List.length_nil] at hj
    omega
  | cons b bs ih =>
    have hp : decide (b ≤ mass) = true ∧
        checkRowFrom a s (e + 1)
          (mass + a (s - (e + 1)) * fastMultiplicity s (s - (e + 1))) bs = true := by
      simpa only [checkRowFrom, Bool.and_eq_true_iff] using hc
    obtain ⟨hb, htail⟩ := hp
    have he : e < s := by simp only [List.length_cons] at hlen; omega
    have hnext : mass + a (s - (e + 1)) * fastMultiplicity s (s - (e + 1)) =
        physicalK s (e + 1) := by
      rw [hmass, ha _ ((Nat.sub_le _ _).trans hs), fastMultiplicity_eq]
      exact (physicalK_succ he).symm
    intro j hj
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero]
      rw [← hmass]
      exact of_decide_eq_true hb
    | succ j =>
      have hj' : j < bs.length := by
        simp only [List.length_cons] at hj
        omega
      have hlen' : e + 1 + bs.length ≤ s := by
        simp only [List.length_cons] at hlen
        omega
      have hh := ih (e + 1) _ hlen' hnext htail j hj'
      simpa only [List.getElem_cons_succ, Nat.succ_eq_add_one,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh

def checkBlock (a : ℕ → ℕ) (T H : ℕ) (targets : List ℕ) : Bool :=
  (List.range (H + 1 - T)).all fun j => checkRowFrom a (T + j) 0 0 targets

theorem checkBlock_sound {a : ℕ → ℕ} {T H : ℕ} {targets : List ℕ}
    (ha : ∀ q, q ≤ H → a q = Nat.totient q) (hTH : T ≤ H)
    (hlen : targets.length ≤ T) (hc : checkBlock a T H targets = true) :
    ∀ e (he : e < targets.length), targets[e] ≤ finiteMinimum T H e hTH := by
  intro e he
  apply (le_finiteMinimum_iff hTH).mpr
  intro s hTs hsH
  have hj : s - T ∈ List.range (H + 1 - T) := by
    simp only [List.mem_range]
    omega
  have hh := (List.all_eq_true.mp hc) (s - T) hj
  have hsize : T + (s - T) = s := by omega
  rw [hsize] at hh
  have hrow := checkRowFrom_sound ha hsH targets 0 0 (by omega)
    (physicalK_zero s).symm hh e he
  simpa only [Nat.zero_add] using hrow

theorem checked_sieve_block {a factor : ℕ → ℕ} {T H : ℕ} {targets : List ℕ}
    (ha : TotientSieve208.check a factor H = true) (hTH : T ≤ H)
    (hlen : targets.length ≤ T) (hc : checkBlock a T H targets = true) :
    ∀ e (he : e < targets.length), targets[e] ≤ finiteMinimum T H e hTH :=
  checkBlock_sound (TotientSieve208.check_sound ha) hTH hlen hc

#print axioms checkRowFrom_sound
#print axioms checkBlock_sound
#print axioms checked_sieve_block
end JSP233.BatchSource208
