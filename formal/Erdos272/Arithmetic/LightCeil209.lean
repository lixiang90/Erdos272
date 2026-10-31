import Erdos272.Arithmetic.LightAnalytic209
import Erdos272.Arithmetic.LightCoefficient209
import Erdos272.Arithmetic.ResidualCeil208

namespace JSP233.LightCeil209
open LightPhaseAnalytic209 LightAnalytic209 ResidualCeil208
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Numerator (V E k : ℕ) : ℕ := V*(V-E)-(V-E-k)^2
def Denominator (V E k : ℕ) : ℕ := 2*(V-E)*k^2
def TermUpper (V E k : ℕ) : ℕ := Numerator V E k*InvUpper (Denominator V E k)
def TailDenominator (A B L : ℕ) : ℕ := 2*B*(A+(L-1)*B)
def Upper (A B V E L : ℕ) : ℕ :=
  (∑r∈Finset.range L,TermUpper V E (A+r*B))+V*InvUpper (TailDenominator A B L)

theorem fraction_upper {n d : ℕ} (hd : 0<d) :
    (n : ℝ)/d≤((n*InvUpper d : ℕ) : ℝ)/(Scale : ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (inv_upper hd) (Nat.cast_nonneg (α := ℝ) n)
  simp only [Nat.cast_mul,div_eq_mul_inv,one_mul,mul_assoc] at hh ⊢
  exact hh

theorem term_sound {V E k : ℕ} (hEV : E<V) (hk : 0<k) :
    Coeff V E k≤(TermUpper V E k : ℝ)/(Scale : ℝ) := by
  have hd : 0<Denominator V E k := by
    dsimp only [Denominator]
    exact Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (Nat.pow_pos hk)
  have hid : Coeff V E k=(Numerator V E k : ℝ)/(Denominator V E k : ℝ) := by
    rw [LightCoefficient209.coeff_nat hEV hk]
    simp only [Numerator,Denominator,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
  rw [hid]
  exact fraction_upper hd

theorem upper_sound {A B V E L : ℕ} (hA : 0<A) (hB : 0<B) (hEV : E<V) :
    Alpha A B V E L≤(Upper A B V E L : ℝ)/(Scale : ℝ) := by
  have hs : (∑r∈Finset.range L,Coeff (V : ℝ) E ((A : ℝ)+(r : ℝ)*B))≤
      ∑r∈Finset.range L,(TermUpper V E (A+r*B) : ℝ)/(Scale : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    simpa only [Nat.cast_add,Nat.cast_mul] using term_sound hEV (by omega : 0<A+r*B)
  have htd : 0<TailDenominator A B L := by
    dsimp only [TailDenominator]
    exact Nat.mul_pos (Nat.mul_pos (by decide) hB) (by omega)
  have ht := fraction_upper (n := V) htd
  have he : (V : ℝ)/(TailDenominator A B L : ℝ)=
      (V : ℝ)/(2*(B : ℝ)*((A : ℝ)+((L-1 : ℕ) : ℝ)*B)) := by
    simp only [TailDenominator,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  rw [he] at ht
  have hh := add_le_add hs ht
  simpa only [Alpha,Upper,Nat.cast_add,Nat.cast_sum,add_div,Finset.sum_div] using hh

def Check (A B V E L u : ℕ) : Bool := decide
  (0<A ∧ 0<B ∧ E<V ∧ 1≤L ∧ Grid*Upper A B V E L≤Scale*u)

theorem check_sound {A B V E L u : ℕ} (hcheck : Check A B V E L u=true) :
    Alpha A B V E L≤(u : ℝ)/(Grid : ℝ) := by
  have hh : 0<A ∧ 0<B ∧ E<V ∧ 1≤L ∧ Grid*Upper A B V E L≤Scale*u := of_decide_eq_true hcheck
  apply (upper_sound hh.1 hh.2.1 hh.2.2.1).trans
  have hr : (Grid : ℝ)*(Upper A B V E L : ℝ)≤(Scale : ℝ)*u := by exact_mod_cast hh.2.2.2.2
  apply (div_le_div_iff₀ (by norm_num [Scale] : (0 : ℝ)<(Scale : ℝ))
    (by norm_num [Grid] : (0 : ℝ)<(Grid : ℝ))).mpr
  nlinarith only [hr]

#print axioms term_sound
#print axioms upper_sound
#print axioms check_sound
end
end JSP233.LightCeil209

