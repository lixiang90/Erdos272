import Erdos272.Global.DenseDeletion40
import Mathlib.Tactic

/-! Keep the actual floor in the dense-pair count before paying its remainder. -/
namespace JSP233.DenseSharper41
open StarCompletion DenseDeletion40
open scoped Classical
noncomputable section

theorem floor_remainder_lower {N r : ℕ} (hr : 0<r) :
    N-(2*r-1)≤2*r*(N/(2*r)) := by
  have he := Nat.mod_add_div N (2*r)
  have hm := Nat.mod_lt N (by omega : 0<2*r)
  omega

theorem actual_dense_floor_budget {N r : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hdense : ∀ S∈F,N<r*S.card) :
    F.card*(N-(2*r-1))≤4*r^2*N^2 := by
  have hc := actual_dense_pair_double_count hr hlegal hbad hdense
  have hs := Nat.mul_le_mul_left (2*r) hc
  have hf := Nat.mul_le_mul_left F.card (floor_remainder_lower (N:=N) hr)
  nlinarith only [hs,hf]

theorem floor_coefficient_payment {N r : ℕ} (hr : 0<r)
    (hN : (4*r^2+1)*(2*r-1)≤N) :
    0<N-(2*r-1) ∧ 4*r^2*N^2≤(4*r^2+1)*N*(N-(2*r-1)) := by
  have hr1 : 1≤r := hr
  have hr2 : 1≤r^2 := by nlinarith only [hr1]
  have hd : 0<2*r-1 := by omega
  have hlarge : 2*r-1<N := by nlinarith only [hN,hr2,hd]
  have he : N-(2*r-1)+(2*r-1)=N := Nat.sub_add_cancel (Nat.le_of_lt hlarge)
  have hh := Nat.mul_le_mul_right N hN
  have hpay := congrArg (fun x : ℕ => (4*r^2+1)*N*x) he
  constructor
  · omega
  · nlinarith only [hpay,hh]

theorem actual_dense_crooked_sharp {N r : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hN : (4*r^2+1)*(2*r-1)≤N)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F,¬IsAP S)
    (hdense : ∀ S∈F,N<r*S.card) : F.card≤(4*r^2+1)*N := by
  have hc := actual_dense_floor_budget hr hlegal hbad hdense
  obtain ⟨hp,hm⟩ := floor_coefficient_payment hr hN
  exact Nat.le_of_mul_le_mul_right (hc.trans hm) hp

theorem actual_deleted_sharp {N r : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hN : (4*r^2+1)*(2*r-1)≤N)
    (hlegal : Legal (Ground N) F) :
    (Deleted N r F).card≤(4*r^2+1)*N := by
  exact actual_dense_crooked_sharp hr hN (actual_deleted_legal hlegal)
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
    (fun S hS => (Finset.mem_filter.mp hS).2.2)

theorem actual_retained_sharp_lower {N r : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hN : (4*r^2+1)*(2*r-1)≤N)
    (hlegal : Legal (Ground N) F) :
    F.card≤(Retained N r F).card+(4*r^2+1)*N := by
  have hb := actual_deleted_sharp hr hN hlegal
  have he := actual_deletion_card_identity N r F
  omega

theorem actual_retained_sharp_density {N r : ℕ} {F : Finset (Finset ℤ)} {d : ℝ}
    (hr : 0<r) (hN : (4*r^2+1)*(2*r-1)≤N)
    (hlegal : Legal (Ground N) F) (hdense : d≤F.card) :
    d-(4*(r:ℝ)^2+1)*(N:ℝ)≤(Retained N r F).card := by
  have hb := actual_retained_sharp_lower hr hN hlegal
  have hreal : (F.card:ℝ)≤(Retained N r F).card+(4*(r:ℝ)^2+1)*(N:ℝ) := by
    exact_mod_cast hb
  linarith

theorem actual_deleted_sharp24 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 108335≤N) (hlegal : Legal (Ground N) F) :
    (Deleted N 24 F).card≤2305*N := by
  exact actual_deleted_sharp (by decide : 0<24) (by norm_num; omega) hlegal

#print axioms floor_remainder_lower
#print axioms actual_dense_floor_budget
#print axioms floor_coefficient_payment
#print axioms actual_dense_crooked_sharp
#print axioms actual_deleted_sharp
#print axioms actual_retained_sharp_lower
#print axioms actual_retained_sharp_density
#print axioms actual_deleted_sharp24
end
end JSP233.DenseSharper41
