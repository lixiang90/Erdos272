module

public import Erdos272.Arithmetic.PrimePrefix35
public import Erdos272.Traces.TraceAntichain35

@[expose] public section

/-! Actual AP-prefix unions and minimal-trace arithmetic, with the prime
parameter tied to the actual prefix length. Dyadic growth is explicit. -/
namespace JSP233.DyadicTraceSupply36
open scoped Classical BigOperators
noncomputable section

def Prefix (c : ℤ) (d k : ℕ) : Finset ℤ :=
  (Finset.range (k+1)).image (fun i : ℕ => c+(i:ℤ)*(d:ℤ))

theorem prefix_card_le (c : ℤ) (d k : ℕ) : (Prefix c d k).card≤k+1 := by
  simpa only [Prefix,Finset.card_range] using Finset.card_image_le
    (s:=Finset.range (k+1)) (f:=fun i : ℕ => c+(i:ℤ)*(d:ℤ))

theorem prefix_union_card (c : ℤ) (I : Finset ℕ) (k : ℕ→ℕ) :
    (I.biUnion (fun d => Prefix c d (k d))).card≤(∑ d∈I,k d)+I.card := by
  have hh := Finset.card_biUnion_le (s:=I) (t:=fun d => Prefix c d (k d))
  have hs := Finset.sum_le_sum (fun d (_hd : d∈I) => prefix_card_le c d (k d))
  have he : (∑ d∈I,(k d+1))=(∑ d∈I,k d)+I.card := by
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]
  exact hh.trans (hs.trans_eq he)

theorem endpoint_quotient_le {c : ℤ} {m d k : ℕ} (hd : 0<d)
    (hend : c+(m:ℤ)∈Prefix c d k) : m/d≤k := by
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hend
  have hi' : i≤k := by have hh := Finset.mem_range.mp hi; omega
  have hm : m=i*d := by exact_mod_cast (show (m:ℤ)=(i:ℤ)*(d:ℤ) by omega)
  rw [hm,Nat.mul_div_cancel _ hd]
  exact hi'

theorem actual_minimal_trace_supply (c : ℤ) (M m K ell w : ℕ)
    (I : Finset ℕ) (P : ℕ→Prop) (k : ℕ→ℕ)
    (hM : 0<M) (hm : 0<m) (hdiv : ∀ d∈I,d∣M) (htrace : ∀ d∈I,P d)
    (hminimal : ∀ d∈I,∀ e,0<e → e∣d → P e → d≤e)
    (hend : ∀ d∈I,c+(M:ℤ)∈Prefix c d (k d))
    (hfinite : ∀ d∈I,k d<2^ell) (homega : m.primeFactors.card≤w)
    (hunion : K≤(I.biUnion (fun d => Prefix c d (k d))).card)
    (hell : 1≤ell) (hK : (2*ell*(w+1))^2≤K) :
    K≤2*(∑ d∈I,k d) ∧ (∑ d∈I,k d)≤
      2*ell*(∑ d∈I,(PrimePrefix35.CoprimePrefix m (k d)).card) := by
  have hsquare := TraceAntichain35.minimal_trace_index_square hM I P k hdiv htrace hminimal
    (fun d hd => endpoint_quotient_le (Nat.pos_of_dvd_of_pos (hdiv d hd) hM) (hend d hd))
  have hB : 1≤2*ell*(w+1) := by nlinarith
  have hpay := PrimePrefix35.square_trace_payment (2*ell*(w+1)) K I.card
    (∑ d∈I,k d) (I.biUnion (fun d => Prefix c d (k d))).card hB hsquare
    (prefix_union_card c I k) hunion hK
  refine ⟨hpay.2,?_⟩
  have hs := Finset.sum_le_sum (fun d hd => PrimePrefix35.actual_prime_prefix_row_omega
    m (k d) ell w hm (hfinite d hd) homega)
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hs
  have hrow : (∑ d∈I,k d)≤ell*((∑ d∈I,
      (PrimePrefix35.CoprimePrefix m (k d)).card)+I.card*(w+1)) := by nlinarith only [hs]
  exact PrimePrefix35.trace_row_payment_omega ell w I.card _ _ hrow hpay.1

theorem dyadic_square_growth (ell j : ℕ) (hell : 3≤ell) :
    (ell+j)^2≤2^j*ell^2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hbase : 3≤ell+j := by omega
    have hstep : (ell+j+1)^2≤2*(ell+j)^2 := by nlinarith
    have hm := Nat.mul_le_mul_left 2 ih
    have he : 2*(2^j*ell^2)=2^(j+1)*ell^2 := by rw [pow_succ (2:ℕ) j]; ring
    simpa only [Nat.add_assoc] using (hstep.trans hm).trans_eq he

theorem dyadic_short_threshold (ell w K j : ℕ) (hell : 3≤ell)
    (hK : (2*ell*(w+1))^2≤K) :
    (2*(ell+j)*(w+1))^2≤2^j*K := by
  have hp := Nat.mul_le_mul_left (4*(w+1)^2) (dyadic_square_growth ell j hell)
  have hk := Nat.mul_le_mul_left (2^j) hK
  nlinarith only [hp,hk]

theorem dyadic_prefix_finite (K ell j k : ℕ) (hK : K≤2^ell)
    (hk : k<2^j*K) : k<2^(ell+j) := by
  apply hk.trans_le
  calc
    2^j*K≤2^j*2^ell := Nat.mul_le_mul_left _ hK
    _=2^(ell+j) := by rw [←pow_add]; congr 1; omega

theorem row_constant_transfer (ell J C W : ℕ) (hell : ell≤2*J)
    (hrow : C≤2*ell*W) : C≤4*J*W := by
  have hh := Nat.mul_le_mul_right (2*W) hell
  nlinarith

#print axioms prefix_card_le
#print axioms prefix_union_card
#print axioms endpoint_quotient_le
#print axioms actual_minimal_trace_supply
#print axioms dyadic_square_growth
#print axioms dyadic_short_threshold
#print axioms dyadic_prefix_finite
#print axioms row_constant_transfer
end
end JSP233.DyadicTraceSupply36
