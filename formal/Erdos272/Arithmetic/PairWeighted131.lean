import Erdos272.Arithmetic.PairHyperbolaExact131
import Erdos272.Arithmetic.D1Analytic131
import Erdos272.Arithmetic.D1Sharper131
import Erdos272.Arithmetic.PrefixSuper127

namespace JSP233.PairWeighted131
open SimplexMoment57 PairHyperbola131 PairHyperbolaExact131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def A (M : ℕ) : ℝ := ∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)/(a:ℝ)
def J (M : ℕ) : ℝ := ∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*Real.log a/(a:ℝ)
def S (M : ℕ) : ℝ := ∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)/Real.sqrt a

def Lower (x : ℝ) (M : ℕ) (β C D : ℝ) : ℝ :=
  2*x*((Real.log x+β)*A M-J M)-2*C*Real.sqrt x*S M-
    2*D*(DivCount 1 M:ℝ)-(DivCount 1 M:ℝ)^2

def Upper (x : ℝ) (K M : ℕ) (β C D : ℝ) : ℝ :=
  2*x*((Real.log x+β)*A M-J M)+2*C*Real.sqrt x*S M+
    2*D*(DivCount 1 M:ℝ)-(DivCount 1 K:ℝ)^2

theorem tau_sum (M : ℕ) :
    (∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ))=(DivCount 1 M:ℝ) := by
  have h : (∑a∈Finset.Icc 1 M,a.divisors.card)=DivCount 1 M := by
    simpa only [DivCount] using PrefixSuper127.actual_first_moment_common M M le_rfl
  exact_mod_cast h

theorem weighted_model_sum {x : ℝ} (hx : 0<x) (M : ℕ) (β C D : ℝ) :
    (∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*
      ((x/(a:ℝ))*(Real.log (x/(a:ℝ))+β)+C*Real.sqrt (x/(a:ℝ))+D))=
    x*((Real.log x+β)*A M-J M)+C*Real.sqrt x*S M+D*(DivCount 1 M:ℝ) := by
  calc
    _=∑a∈Finset.Icc 1 M,
        ((x*(Real.log x+β))*((a.divisors.card:ℝ)/(a:ℝ))-
          x*((a.divisors.card:ℝ)*Real.log a/(a:ℝ))+
          (C*Real.sqrt x)*((a.divisors.card:ℝ)/Real.sqrt a)+D*(a.divisors.card:ℝ)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha0 : (0:ℝ)<a := Nat.cast_pos.mpr (Finset.mem_Icc.mp ha).1
      rw [Real.log_div hx.ne' ha0.ne',Real.sqrt_div hx.le]
      ring
    _=_ := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_sub_distrib,
        ←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum,tau_sum]
      dsimp only [A,J,S]
      ring

theorem weighted_lower {β C D : ℝ}
    (hd1 : ∀q:ℝ,0≤q→q*(Real.log q+β)-C*Real.sqrt q-D≤(DivCount 1 (Nat.floor q):ℝ))
    {x : ℝ} (hx : 0<x) (M : ℕ) : Lower x M β C D≤(DivCount 3 (Nat.floor x):ℝ) := by
  have hs : (∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*
      ((x/(a:ℝ))*(Real.log (x/(a:ℝ))+β)-C*Real.sqrt (x/(a:ℝ))-D))≤
      ∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*(DivCount 1 (Nat.floor (x/(a:ℝ))):ℝ) := by
    apply Finset.sum_le_sum
    intro a _ha
    exact mul_le_mul_of_nonneg_left (hd1 (x/a) (div_nonneg hx.le (Nat.cast_nonneg a))) (Nat.cast_nonneg _)
  have he := weighted_model_sum hx M β (-C) (-D)
  simp only [neg_mul,←sub_eq_add_neg] at he
  rw [he] at hs
  have hp := actual_pair_hyperbola_lower_floor x M
  calc
    Lower x M β C D=
        2*(x*((Real.log x+β)*A M-J M)-C*Real.sqrt x*S M-D*(DivCount 1 M:ℝ))-
          (DivCount 1 M:ℝ)^2 := by dsimp only [Lower];ring
    _≤2*(∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*(DivCount 1 (Nat.floor (x/(a:ℝ))):ℝ))-
        (DivCount 1 M:ℝ)^2 := sub_le_sub_right (mul_le_mul_of_nonneg_left hs (by norm_num)) _
    _≤_ := hp

theorem weighted_upper {β C D : ℝ}
    (hd1 : ∀q:ℝ,0≤q→(DivCount 1 (Nat.floor q):ℝ)≤q*(Real.log q+β)+C*Real.sqrt q+D)
    {x : ℝ} (hx : 0<x) {M K : ℕ}
    (hKM : K≤M) (hK : (K:ℝ)^2≤x) (hN : x≤(M:ℝ)^2) :
    (DivCount 3 (Nat.floor x):ℝ)≤Upper x K M β C D := by
  have hs : (∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*(DivCount 1 (Nat.floor (x/(a:ℝ))):ℝ))≤
      ∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*
        ((x/(a:ℝ))*(Real.log (x/(a:ℝ))+β)+C*Real.sqrt (x/(a:ℝ))+D) := by
    apply Finset.sum_le_sum
    intro a _ha
    exact mul_le_mul_of_nonneg_left (hd1 (x/a) (div_nonneg hx.le (Nat.cast_nonneg a))) (Nat.cast_nonneg _)
  rw [weighted_model_sum hx M β C D] at hs
  calc
    _≤2*(∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*(DivCount 1 (Nat.floor (x/(a:ℝ))):ℝ))-
        (DivCount 1 K:ℝ)^2 := actual_pair_hyperbola_upper_floor hx.le hKM hK hN
    _≤2*(x*((Real.log x+β)*A M-J M)+C*Real.sqrt x*S M+D*(DivCount 1 M:ℝ))-
        (DivCount 1 K:ℝ)^2 := sub_le_sub_right (mul_le_mul_of_nonneg_left hs (by norm_num)) _
    _=Upper x K M β C D := by dsimp only [Upper];ring

theorem actual_weighted_lower_C7 {x : ℝ} (hx : 0<x) (M : ℕ) :
    Lower x M (3/20) 7 0≤(DivCount 3 (Nat.floor x):ℝ) := by
  apply weighted_lower (β:=3/20) (C:=7) (D:=0) _ hx M
  intro q hq
  simpa only [sub_zero] using D1Analytic131.actual_d1_lower hq

theorem actual_weighted_upper_C7 {x : ℝ} (hx : 0<x) {M K : ℕ}
    (hKM : K≤M) (hK : (K:ℝ)^2≤x) (hN : x≤(M:ℝ)^2) :
    (DivCount 3 (Nat.floor x):ℝ)≤Upper x K M (4/25) 7 0 := by
  apply weighted_upper (β:=4/25) (C:=7) (D:=0) _ hx hKM hK hN
  intro q hq
  simpa only [add_zero] using D1Analytic131.actual_d1_upper hq

theorem actual_weighted_lower_sharp {x : ℝ} (hx : 0<x) (M : ℕ) :
    Lower x M (77/500) 2 (9/2)≤(DivCount 3 (Nat.floor x):ℝ) := by
  exact weighted_lower (fun q hq=>D1Sharper131.actual_d1_lower hq) hx M

theorem actual_weighted_upper_sharp {x : ℝ} (hx : 0<x) {M K : ℕ}
    (hKM : K≤M) (hK : (K:ℝ)^2≤x) (hN : x≤(M:ℝ)^2) :
    (DivCount 3 (Nat.floor x):ℝ)≤Upper x K M (39/250) 2 0 := by
  apply weighted_upper (β:=39/250) (C:=2) (D:=0) _ hx hKM hK hN
  intro q hq
  simpa only [add_zero] using D1Sharper131.actual_d1_upper hq

#print axioms tau_sum
#print axioms weighted_model_sum
#print axioms weighted_lower
#print axioms weighted_upper
#print axioms actual_weighted_lower_C7
#print axioms actual_weighted_upper_C7
#print axioms actual_weighted_lower_sharp
#print axioms actual_weighted_upper_sharp
end
end JSP233.PairWeighted131
