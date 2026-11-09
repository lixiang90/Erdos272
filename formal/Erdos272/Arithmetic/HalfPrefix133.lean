module

public import Erdos272.Traces.HalfBad133
public import Erdos272.Arithmetic.PrefixSuper127
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.HalfPrefix133
open StarCompletion RestrictedWitness44 HalfBad133 TwoSidedMoment62
open PrefixSuper127 SimplexMoment57 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_half_witness_expansion (Ω : Finset ℤ) (c : ℤ) :
    (HalfWitnessException Ω c:ℝ)=
      (1/2:ℝ)*(∑q∈Ω,(Distance c q).divisors.card^2)+
      (3/2:ℝ)*(∑q∈Ω,(Distance c q).divisors.card) := by
  calc
    (HalfWitnessException Ω c:ℝ)=
        (∑q∈Ω,(((Distance c q).divisors.card).choose 2:ℝ))+
          2*∑q∈Ω,((Distance c q).divisors.card:ℝ) := by
      simp only [HalfWitnessException,Nat.cast_add,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat]
    _=∑q∈Ω,((((Distance c q).divisors.card).choose 2:ℝ)+
        2*((Distance c q).divisors.card:ℝ)) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
    _=∑q∈Ω,((1/2:ℝ)*((Distance c q).divisors.card:ℝ)^2+
        (3/2:ℝ)*((Distance c q).divisors.card:ℝ)) := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Nat.cast_choose_two]
      ring
    _=_ := by simp only [Finset.sum_add_distrib,Finset.mul_sum,Nat.cast_sum,Nat.cast_pow]

theorem actual_distance_superadditive_prefix {N : ℕ} {c : ℤ}
    (hc : c∈Ground N) (f : ℕ→ℕ) (hf0 : f 0=0)
    (hsuper : ∀a b:ℕ,(∑n∈Finset.Icc 1 a,f n)+(∑n∈Finset.Icc 1 b,f n)≤
      ∑n∈Finset.Icc 1 (a+b),f n) :
    (∑q∈Ground N,(f (Distance c q):ℝ))≤∑n∈Finset.Icc 1 N,(f n:ℝ) := by
  have hcg := (mem_ground N c).mp hc
  have hlen : c.toNat-1+(N-c.toNat)=N-1 := by omega
  rw [actual_distance_sum_split hc (fun d=>(f d:ℝ)) (by simp [hf0])]
  have hs := hsuper (c.toNat-1) (N-c.toNat)
  rw [hlen] at hs
  have hsR : (∑n∈Finset.Icc 1 (c.toNat-1),(f n:ℝ))+
      (∑n∈Finset.Icc 1 (N-c.toNat),(f n:ℝ))≤
        ∑n∈Finset.Icc 1 (N-1),(f n:ℝ) := by exact_mod_cast hs
  apply hsR.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.sub_le N 1))
  intro n _hn _hnot
  exact Nat.cast_nonneg (f n)

theorem actual_half_witness_prefix {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (HalfWitnessException (Ground N) c:ℝ)≤
      (1/2:ℝ)*(∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+
      (3/2:ℝ)*(∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)) := by
  have h2 := actual_distance_superadditive_prefix hc (fun n=>n.divisors.card^2)
    (by simp) actual_second_moment_superadditive
  have h1 := actual_distance_superadditive_prefix hc (fun n=>n.divisors.card)
    (by simp) actual_first_moment_superadditive
  have he := actual_half_witness_expansion (Ground N) c
  push_cast at h2 he
  linarith only [he,h2,h1]

theorem actual_bad_family_half_prefix {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hc : c∈Ground N) (P : Finset ℤ) (hF : Legal (Ground N) F) :
    ((BadMembers F c P).card:ℝ)≤
      (1/2:ℝ)*(∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+
      (3/2:ℝ)*(∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)) := by
  have hb : ((BadMembers F c P).card:ℝ)≤HalfWitnessException (Ground N) c := by
    exact_mod_cast actual_restricted_bad_family_bound_half c P hF
  exact hb.trans (actual_half_witness_prefix hc)

theorem actual_half_witness_moment {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (HalfWitnessException (Ground N) c:ℝ)≤
      (1/2:ℝ)*(∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+
      (3/2:ℝ)*(N:ℝ)*Harmonic N := by
  have hw := actual_half_witness_prefix hc
  have hf := actual_divisor_first_moment N
  nlinarith only [hw,hf]

#print axioms actual_half_witness_expansion
#print axioms actual_distance_superadditive_prefix
#print axioms actual_half_witness_prefix
#print axioms actual_bad_family_half_prefix
#print axioms actual_half_witness_moment
end
end JSP233.HalfPrefix133
