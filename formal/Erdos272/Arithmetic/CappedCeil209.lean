import Erdos272.Resources.NearCapped209
import Erdos272.Arithmetic.ResidualCeil208

namespace JSP233.CappedCeil209
open scoped BigOperators
open ResidualCeil208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Upper (M e c : ℕ) : ℕ :=
  (∑b∈Finset.Icc 2 c,
    (InvUpper ((M-b)*b*(b-1))+InvUpper ((2*M-3*b)*b*(b-1))))+
    2*InvUpper ((M-e)*c)

theorem term_factor {M b : ℕ} (hb : 1≤b) :
    (1/((M-b : ℕ) : ℝ)+1/((2*M-3*b : ℕ) : ℝ))/((b : ℝ)*(b-1))=
      1/(((M-b)*b*(b-1) : ℕ) : ℝ)+1/(((2*M-3*b)*b*(b-1) : ℕ) : ℝ) := by
  simp only [Nat.cast_mul,Nat.cast_sub hb,Nat.cast_one,
    div_eq_mul_inv,mul_inv_rev]
  ring

theorem upper_sound {M e c : ℕ} (hc : 1≤c) (hce : c<e)
    (heM : e<M) (hshort : 3*c<2*M) :
    NearCapped209.Price M e c≤(Upper M e c : ℝ)/(Scale : ℝ) := by
  have hid : NearCapped209.Price M e c=
      (∑b∈Finset.Icc 2 c,
        (1/(((M-b)*b*(b-1) : ℕ) : ℝ)+1/(((2*M-3*b)*b*(b-1) : ℕ) : ℝ)))+
        2/(((M-e)*c : ℕ) : ℝ) := by
    unfold NearCapped209.Price
    congr 1
    · apply Finset.sum_congr rfl
      intro b hb
      exact term_factor (by have := (Finset.mem_Icc.mp hb).1;omega)
    · simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
      ring
  rw [hid]
  have hs : (∑b∈Finset.Icc 2 c,
        (1/(((M-b)*b*(b-1) : ℕ) : ℝ)+1/(((2*M-3*b)*b*(b-1) : ℕ) : ℝ)))≤
      ∑b∈Finset.Icc 2 c,
        ((InvUpper ((M-b)*b*(b-1)) : ℝ)/Scale+
          (InvUpper ((2*M-3*b)*b*(b-1)) : ℝ)/Scale) := by
    apply Finset.sum_le_sum
    intro b hb
    have hb2 := (Finset.mem_Icc.mp hb).1
    have hbc := (Finset.mem_Icc.mp hb).2
    have hp : 0<b := by omega
    have hm : 0<M-b := by omega
    have ht : 0<2*M-3*b := by omega
    have hb1 : 0<b-1 := by omega
    exact add_le_add (inv_upper (Nat.mul_pos (Nat.mul_pos hm hp) hb1))
      (inv_upper (Nat.mul_pos (Nat.mul_pos ht hp) hb1))
  have ht := mul_le_mul_of_nonneg_left
    (inv_upper (Nat.mul_pos (by omega : 0<M-e) (by omega : 0<c)))
    (show (0 : ℝ)≤2 by norm_num)
  calc
    _≤(∑b∈Finset.Icc 2 c,
        ((InvUpper ((M-b)*b*(b-1)) : ℝ)/Scale+
          (InvUpper ((2*M-3*b)*b*(b-1)) : ℝ)/Scale))+
          2*((InvUpper ((M-e)*c) : ℝ)/Scale) := by
      simpa only [div_eq_mul_inv,one_mul] using add_le_add hs ht
    _=_ := by
      unfold Upper
      push_cast
      rw [add_div,Finset.sum_div]
      congr 1
      · apply Finset.sum_congr rfl
        intro b hb
        ring
      · ring

def Check (M e c u : ℕ) : Bool := decide
  (1≤c ∧ c<e ∧ e<M ∧ 3*c<2*M ∧ Grid*Upper M e c≤Scale*u)

theorem check_sound {M e c u : ℕ} (hcheck : Check M e c u=true) :
    NearCapped209.Price M e c≤(u : ℝ)/(Grid : ℝ) := by
  have hh : 1≤c ∧ c<e ∧ e<M ∧ 3*c<2*M ∧ Grid*Upper M e c≤Scale*u :=
    of_decide_eq_true hcheck
  apply (upper_sound hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1).trans
  have hR : (Grid : ℝ)*(Upper M e c : ℝ)≤(Scale : ℝ)*u := by
    exact_mod_cast hh.2.2.2.2
  apply (div_le_div_iff₀ (by norm_num [Scale] : (0 : ℝ)<(Scale : ℝ))
    (by norm_num [Grid] : (0 : ℝ)<(Grid : ℝ))).mpr
  nlinarith only [hR]

#print axioms upper_sound
#print axioms check_sound
end
end JSP233.CappedCeil209
