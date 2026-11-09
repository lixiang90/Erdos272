module

public import Erdos272.Counting.ResidualTwoCensus208
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.CoarseCensus209
open ResidualSpan208 ResidualCensus208 ResidualPrice208 ResidualTwoCensus208 StepClass208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem gate_antitone (N d a b : ℕ) (hab : a≤b) :
    (if d*b≤N then 1 else 0 : ℕ)≤(if d*a≤N then 1 else 0) := by
  have hm := Nat.mul_le_mul_left d hab
  split_ifs <;> omega

theorem gate_sum_bound (N D A : ℕ) (hA : 0<A) :
    ((∑d∈Finset.Icc 1 D,if d*A≤N then 1 else 0 : ℕ) : ℝ)≤(N : ℝ)/A := by
  have hsub : (Finset.Icc 1 D).filter (fun d=>d*A≤N)⊆Finset.Icc 1 (N/A) := by
    intro d hd
    obtain ⟨hd,hprod⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Nat.le_div_iff_mul_le hA).mpr hprod⟩
  have hn : (∑d∈Finset.Icc 1 D,if d*A≤N then 1 else 0 : ℕ)≤N/A := by
    rw [Finset.sum_boole]
    simpa using Finset.card_le_card hsub
  have hr : ((∑d∈Finset.Icc 1 D,if d*A≤N then 1 else 0 : ℕ) : ℝ)≤((N/A : ℕ) : ℝ) := by exact_mod_cast hn
  exact hr.trans (Nat.cast_div_le (α:=ℝ) (m:=N) (n:=A))

theorem span_coarse {M b p : ℕ} (hb : b≤M) (hp : 2≤p) :
    2*M-3*b≤Span (M-b) b p := by
  have hdiv : (b-1)/(p-1)≤b := (Nat.div_le_self _ _).trans (Nat.sub_le b 1)
  have hm : min ((b-1)/(p-1)) ((M-b)/p)≤b := (min_le_left _ _).trans hdiv
  unfold Span
  omega

theorem occupancy_sum_of_span_lower {N D M b C : ℕ} (hb : b<M) (hC : 0<C)
    (hspan : ∀d,C≤Span (M-b) b (PrimeGate d)) :
    ((∑d∈Finset.Icc 1 D,Occupancy N M d b : ℕ) : ℝ)≤
      (N : ℝ)*(1/((M-b : ℕ) : ℝ)+1/(C : ℝ)) := by
  have ha : 0<M-b := by omega
  have hterm : ∀d∈Finset.Icc 1 D,Occupancy N M d b≤
      (if d*(M-b)≤N then 1 else 0)+(if d*C≤N then 1 else 0) := by
    intro d _hd
    exact Nat.add_le_add (integer_gate_upper N d (M-b))
      ((integer_gate_upper N d (Span (M-b) b (PrimeGate d))).trans
        (gate_antitone N d C _ (hspan d)))
  have hs := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hs
  have hr : ((∑d∈Finset.Icc 1 D,Occupancy N M d b : ℕ) : ℝ)≤
      ((∑d∈Finset.Icc 1 D,if d*(M-b)≤N then 1 else 0 : ℕ) : ℝ)+
      ((∑d∈Finset.Icc 1 D,if d*C≤N then 1 else 0 : ℕ) : ℝ) := by exact_mod_cast hs
  have h1 := gate_sum_bound N D (M-b) ha
  have h2 := gate_sum_bound N D C hC
  calc
    _≤(N : ℝ)/((M-b : ℕ) : ℝ)+(N : ℝ)/C := hr.trans (add_le_add h1 h2)
    _=_ := by ring

theorem occupancy_short {N D M b : ℕ} (hb : b<M) (hsmall : 3*b<2*M) :
    ((∑d∈Finset.Icc 1 D,Occupancy N M d b : ℕ) : ℝ)≤
      (N : ℝ)*(1/((M-b : ℕ) : ℝ)+1/((2*M-3*b : ℕ) : ℝ)) := by
  apply occupancy_sum_of_span_lower hb (by omega : 0<2*M-3*b)
  intro d
  have hp := primeGate_range d
  simp only [Finset.mem_insert,Finset.mem_singleton] at hp
  exact span_coarse hb.le (by omega)

theorem occupancy_tail {N D M b e : ℕ} (hbe : b≤e) (heM : e<M) :
    ((∑d∈Finset.Icc 1 D,Occupancy N M d b : ℕ) : ℝ)≤2*(N : ℝ)/((M-e : ℕ) : ℝ) := by
  have hb : b<M := hbe.trans_lt heM
  have hh := occupancy_sum_of_span_lower (N:=N) (D:=D) hb (by omega : 0<M-b)
    (fun d=>span_ge (M-b) b (PrimeGate d))
  have hpos : (0 : ℝ)<((M-e : ℕ) : ℝ) := by exact_mod_cast (show 0<M-e by omega)
  have hi : 1/((M-b : ℕ) : ℝ)≤1/((M-e : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hpos (by exact_mod_cast (show M-e≤M-b by omega))
  have hm := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (α:=ℝ) N)
  calc
    _≤(N : ℝ)*(1/((M-b : ℕ) : ℝ)+1/((M-b : ℕ) : ℝ)) := hh
    _≤(N : ℝ)*(1/((M-e : ℕ) : ℝ)+1/((M-e : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hi hi) (Nat.cast_nonneg N)
    _=_ := by ring

#print axioms gate_sum_bound
#print axioms occupancy_short
#print axioms occupancy_tail
end
end JSP233.CoarseCensus209
