import Erdos272.Arithmetic.ExtraCertificate132
import Erdos272.Arithmetic.PairWindow131

namespace JSP233.ScaleWindow132
open PoolExtension132 ExtraCertificate132 PairWindow131 SimplexMoment57
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def pairScales : List ℕ → List ℕ
  | [] => []
  | p::P => P.map (p*·) ++ pairScales P

def upperScales (P : List ℕ) : List ℕ :=
  [1,6,10,14,15,21,35,210] ++ P.flatMap (fun p => [p*2,p*3,p*5,p*7]) ++ pairScales P

def lowerScales (P : List ℕ) : List ℕ := [2,3,5,7,30,42,70,105] ++ P

def countSum (N : ℕ) (R : List ℕ) : ℕ := (R.map (fun r => DivCount 3 (N/(r*r)))).sum

theorem count_pair_scales (N : ℕ) (P : List ℕ) : countSum N (pairScales P)=PairTerms N P := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [countSum,pairScales,PairTerms,List.map_map,←ih,Function.comp_def]

theorem count_cross_scales (N : ℕ) (P : List ℕ) :
    countSum N (P.flatMap (fun p => [p*2,p*3,p*5,p*7]))=CrossTerms N P := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    simp only [List.flatMap_cons,countSum,List.map_append,List.sum_append,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil,CrossTerms]
    dsimp only [CrossTerm]
    change _ + countSum N (P.flatMap (fun p => [p*2,p*3,p*5,p*7])) = _
    rw [ih]
    simp only [CrossTerms]
    omega

theorem count_upper_scales (N : ℕ) (P : List ℕ) :
    countSum N (upperScales P)=OldUpper N+CrossTerms N P+PairTerms N P := by
  have hc := count_cross_scales N P
  have hp := count_pair_scales N P
  simp only [upperScales,countSum,List.map_append,List.sum_append] at hc hp ⊢
  rw [hc,hp]
  simp [OldUpper,OldPenalty]
  omega

theorem count_lower_scales (N : ℕ) (P : List ℕ) :
    countSum N (lowerScales P)=OldLower N+ExtraTerms N P := by
  simp [countSum,lowerScales,OldLower,ExtraTerms]
  omega

theorem div_count_zero : DivCount 3 0=0 := by simp [DivCount]

theorem count_filter_scales (N hi : ℕ) (R : List ℕ) (hN : N≤hi) :
    countSum N (R.filter (fun r => r*r≤hi))=countSum N R := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    by_cases hr : r*r≤hi
    · simp only [List.filter_cons,hr,decide_true,ite_true,countSum,List.map_cons,List.sum_cons] at ih ⊢
      exact congrArg (_+·) ih
    · have hz : DivCount 3 (N/(r*r))=0 := by
        rw [Nat.div_eq_of_lt (by omega),div_count_zero]
      simp [hr,countSum,hz] at ih ⊢
      exact ih

theorem actual_second_moment_scales (N hi : ℕ) (P : List ℕ)
    (h : extrasCheck P=true) (hN : N≤hi) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+
      ((lowerScales P).map (fun r => (DivCount 3 (N/(r*r)):ℝ))).sum ≤
      (((upperScales P).filter (fun r => r*r≤hi)).map
        (fun r => (DivCount 3 (N/(r*r)):ℝ))).sum := by
  have hh := actual_second_moment_extras_of_check_nat N P h
  rw [Nat.add_assoc] at hh
  rw [←count_lower_scales N P,←count_upper_scales N P,
    ←count_filter_scales N hi (upperScales P) hN] at hh
  have hcast (R : List ℕ) : (countSum N R:ℝ)=
      (R.map (fun r => (DivCount 3 (N/(r*r)):ℝ))).sum := by
    simp [countSum,Nat.cast_list_sum,List.map_map,Function.comp_def]
  have hr : ((∑n∈Finset.Icc 1 N,n.divisors.card^2):ℝ)+
      (countSum N (lowerScales P):ℝ)≤
      (countSum N ((upperScales P).filter (fun r => r*r≤hi)):ℝ) := by exact_mod_cast hh
  simpa only [Nat.cast_sum,Nat.cast_pow,hcast] using hr

def zeroCoeff : Coeff := ⟨0,0,0,0⟩
def addCoeff (x y : Coeff) : Coeff := ⟨x.a+y.a,x.b+y.b,x.s+y.s,x.f+y.f⟩
def subCoeff (x y : Coeff) : Coeff := ⟨x.a-y.a,x.b-y.b,x.s-y.s,x.f-y.f⟩
def sumCoeff : List Coeff → Coeff
  | [] => zeroCoeff
  | c::C => addCoeff c (sumCoeff C)
def combined (U L : List Coeff) : Coeff := subCoeff (sumCoeff U) (sumCoeff L)

theorem eval_zero (N : ℕ) : eval zeroCoeff N=0 := by simp [eval,zeroCoeff]
theorem eval_add (N : ℕ) (x y : Coeff) : eval (addCoeff x y) N=eval x N+eval y N := by
  dsimp only [eval,addCoeff]; ring
theorem eval_sub (N : ℕ) (x y : Coeff) : eval (subCoeff x y) N=eval x N-eval y N := by
  dsimp only [eval,subCoeff]; ring
theorem eval_sum (N : ℕ) (C : List Coeff) : eval (sumCoeff C) N=(C.map (eval · N)).sum := by
  induction C with
  | nil => exact eval_zero N
  | cons c C ih => simpa only [sumCoeff,List.map_cons,List.sum_cons,eval_add] using congrArg (eval c N+·) ih

theorem upper_list_bound (N : ℕ) {R : List ℕ} {C : List Coeff}
    (h : List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) R C) :
    (R.map (fun r => (DivCount 3 (N/(r*r)):ℝ))).sum≤(C.map (eval · N)).sum := by
  induction h with
  | nil => exact le_rfl
  | cons h _ ih => exact add_le_add h ih

theorem lower_list_bound (N : ℕ) {R : List ℕ} {C : List Coeff}
    (h : List.Forall₂ (fun r c => eval c N≤(DivCount 3 (N/(r*r)):ℝ)) R C) :
    (C.map (eval · N)).sum≤(R.map (fun r => (DivCount 3 (N/(r*r)):ℝ))).sum := by
  induction h with
  | nil => exact le_rfl
  | cons h _ ih => exact add_le_add h ih

theorem actual_m2_lists (N hi : ℕ) (P : List ℕ) (U L : List Coeff)
    (h : extrasCheck P=true) (hN : N≤hi)
    (hu : List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N)
      ((upperScales P).filter (fun r => r*r≤hi)) U)
    (hl : List.Forall₂ (fun r c => eval c N≤(DivCount 3 (N/(r*r)):ℝ)) (lowerScales P) L) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤eval (combined U L) N := by
  have hm := actual_second_moment_scales N hi P h hN
  have hu' := upper_list_bound N hu
  have hl' := lower_list_bound N hl
  rw [combined,eval_sub,eval_sum,eval_sum]
  linarith only [hm,hu',hl']

#print axioms count_pair_scales
#print axioms count_cross_scales
#print axioms count_upper_scales
#print axioms count_lower_scales
#print axioms div_count_zero
#print axioms count_filter_scales
#print axioms actual_second_moment_scales
#print axioms eval_zero
#print axioms eval_add
#print axioms eval_sub
#print axioms eval_sum
#print axioms upper_list_bound
#print axioms lower_list_bound
#print axioms actual_m2_lists
end
end JSP233.ScaleWindow132
