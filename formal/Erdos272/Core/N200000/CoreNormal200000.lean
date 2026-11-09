module

public import Erdos272.Core.N200000.PairPool200000
public import Mathlib.RingTheory.Coprime.Basic

@[expose] public section

/-! Normalize an actual step and outside-point offset by their gcd.
Primitive index pairs then have exactly this actual primitive hull step. -/
namespace JSP233.CoreNormal200000
open StarCompletion APGeometry SourceBridge208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

structure Normalization (d y : ℤ) where
  g : ℤ
  h : ℕ
  ell : ℤ
  g_pos : 0 < g
  h_pos : 0 < h
  step_eq : d = (h : ℤ) * g
  point_eq : y = ell * g
  coprime : Int.gcd (h : ℤ) ell = 1

theorem coprime_of_gcd_one {u v : ℤ} (h : Int.gcd u v = 1) : IsCoprime u v := by
  have hb := Int.gcd_eq_gcd_ab u v
  rw [h, Nat.cast_one] at hb
  refine ⟨Int.gcdA u v, Int.gcdB u v, ?_⟩
  nlinarith only [hb]

theorem gcd_one_of_coprime {u v : ℤ} (h : IsCoprime u v) : Int.gcd u v = 1 := by
  obtain ⟨a, b, hab⟩ := h
  have hdiv : (Int.gcd u v : ℤ) ∣ 1 := by
    rw [← hab]
    exact dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left u v) a)
      (dvd_mul_of_dvd_right (Int.gcd_dvd_right u v) b)
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hdiv)

theorem actual_normalization {d : ℤ} (hd : 0 < d) (y : ℤ) : Nonempty (Normalization d y) := by
  have hgN : 0 < Int.gcd d y := Int.gcd_pos_of_ne_zero_left y hd.ne'
  have hg : 0 < (Int.gcd d y : ℤ) := by exact_mod_cast hgN
  obtain ⟨h, ell, hcop, hstep, hpoint⟩ := Int.exists_gcd_one hgN
  have hh : 0 < h := by nlinarith only [hd, hg, hstep]
  have hcast : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh.le
  have hhN : 0 < h.toNat := by omega
  refine ⟨{
    g := (Int.gcd d y : ℤ)
    h := h.toNat
    ell := ell
    g_pos := hg
    h_pos := hhN
    step_eq := ?_
    point_eq := hpoint
    coprime := ?_ }⟩
  · simpa only [hcast] using hstep
  · simpa only [hcast] using hcop

theorem normalized_pair_gcd {d p x : ℤ} (n : Normalization d (x - p)) (i j : ℤ)
    (hpair : Int.gcd (j - i) (n.ell - (n.h : ℤ) * i) = 1) :
    (Int.gcd ((p + d * j) - (p + d * i)) (x - (p + d * i)) : ℤ) = n.g := by
  have hhc : IsCoprime (n.h : ℤ) (n.ell - (n.h : ℤ) * i) :=
    IsCoprime.sub_mul_left_right_iff.mpr (coprime_of_gcd_one n.coprime)
  have hmc := coprime_of_gcd_one hpair
  have hprod := gcd_one_of_coprime (hhc.mul_left hmc)
  have hA : (p + d * j) - (p + d * i) = n.g * ((n.h : ℤ) * (j - i)) := by
    have hj := congrArg (fun z : ℤ => z * j) n.step_eq
    have hi := congrArg (fun z : ℤ => z * i) n.step_eq
    nlinarith only [hj, hi]
  have hB : x - (p + d * i) = n.g * (n.ell - (n.h : ℤ) * i) := by
    have hp := n.point_eq
    have hi := congrArg (fun z : ℤ => z * i) n.step_eq
    nlinarith only [hp, hi]
  simp only [hA, hB, Int.gcd_mul_left, hprod, Nat.mul_one, Int.natCast_natAbs, abs_of_pos n.g_pos]

theorem bad_factor_not_in_step {d y : ℤ} (n : Normalization d y) {q : ℕ} (hq : 2 ≤ q) (i : ℤ)
    (hbad : (q : ℤ) ∣ n.ell - (n.h : ℤ) * i) : ¬ (q : ℤ) ∣ (n.h : ℤ) := by
  intro hstep
  have hell : (q : ℤ) ∣ n.ell := by
    have hh := dvd_add hbad (dvd_mul_of_dvd_left hstep i)
    simpa only [sub_add_cancel] using hh
  have hdiv := Int.dvd_coe_gcd hstep hell
  rw [n.coprime, Nat.cast_one] at hdiv
  have hqone : q = 1 := Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hdiv)
  omega

#print axioms coprime_of_gcd_one
#print axioms gcd_one_of_coprime
#print axioms actual_normalization
#print axioms normalized_pair_gcd
#print axioms bad_factor_not_in_step
end
end JSP233.CoreNormal200000
