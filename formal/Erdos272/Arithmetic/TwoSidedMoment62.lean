module

public import Erdos272.Arithmetic.SimplexMoment57

@[expose] public section

/-! Exact left/right distance prefixes and the one-copy simplex exception.
The root is an actual member of Ground N.  No supplied exception bound,
family capacity, finite numerical window or global low-startup claim occurs.
-/
namespace JSP233.TwoSidedMoment62
open scoped Classical BigOperators
open StarCompletion APGeometry RestrictedWitness44 DivisorMoment45
open HarmonicAbel29 SimplexMoment57
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_left_distance_sum {N : ℕ} {c : ℤ} (hc : c∈Ground N)
    (f : ℕ→ℝ) :
    (∑q∈(Ground N).filter (fun q=>q<c),f (Distance c q))=
      ∑d∈Finset.Icc 1 (c.toNat-1),f d := by
  have hcG := (mem_ground N c).mp hc
  refine Finset.sum_bij (fun q _=>Distance c q) ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨hqG,hqc⟩ := Finset.mem_filter.mp hq
    have hqG' := (mem_ground N q).mp hqG
    have hd : (Distance c q:ℤ)=c-q := by
      dsimp only [Distance]
      rw [Int.ofNat_natAbs_of_nonpos (by omega : q-c≤0)]
      omega
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro q hq z hz heq
    have hq' := (Finset.mem_filter.mp hq).2
    have hz' := (Finset.mem_filter.mp hz).2
    exact DivisorMoment45.distance_side_injective heq (by simp [show ¬c≤q by omega,show ¬c≤z by omega])
  · intro d hd
    obtain ⟨hd0,hdc⟩ := Finset.mem_Icc.mp hd
    refine ⟨c-(d:ℤ),Finset.mem_filter.mpr ⟨(mem_ground N _).mpr ?_,?_⟩,?_⟩
    · constructor <;> omega
    · omega
    · dsimp only [Distance]
      have he : c-(d:ℤ)-c=-(d:ℤ) := by ring
      rw [he,Int.natAbs_neg,Int.natAbs_natCast]
  · intro q hq
    rfl

theorem actual_right_distance_sum {N : ℕ} {c : ℤ} (hc : c∈Ground N)
    (f : ℕ→ℝ) :
    (∑q∈(Ground N).filter (fun q=>c<q),f (Distance c q))=
      ∑d∈Finset.Icc 1 (N-c.toNat),f d := by
  have hcG := (mem_ground N c).mp hc
  refine Finset.sum_bij (fun q _=>Distance c q) ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨hqG,hcq⟩ := Finset.mem_filter.mp hq
    have hqG' := (mem_ground N q).mp hqG
    have hd : (Distance c q:ℤ)=q-c := by
      dsimp only [Distance]
      rw [Int.natAbs_of_nonneg (by omega : 0≤q-c)]
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro q hq z hz heq
    have hq' := (Finset.mem_filter.mp hq).2
    have hz' := (Finset.mem_filter.mp hz).2
    exact DivisorMoment45.distance_side_injective heq (by simp [show c≤q by omega,show c≤z by omega])
  · intro d hd
    obtain ⟨hd0,hdc⟩ := Finset.mem_Icc.mp hd
    refine ⟨c+(d:ℤ),Finset.mem_filter.mpr ⟨(mem_ground N _).mpr ?_,?_⟩,?_⟩
    · constructor <;> omega
    · omega
    · simp only [Distance,add_sub_cancel_left,Int.natAbs_natCast]
  · intro q hq
    rfl

theorem actual_distance_sum_split {N : ℕ} {c : ℤ} (hc : c∈Ground N)
    (f : ℕ→ℝ) (hf : f 0=0) :
    (∑q∈Ground N,f (Distance c q))=
      (∑d∈Finset.Icc 1 (c.toNat-1),f d)+
      ∑d∈Finset.Icc 1 (N-c.toNat),f d := by
  rw [←actual_left_distance_sum hc f,←actual_right_distance_sum hc f]
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqc : q<c
  · simp [hqc,show ¬c<q by omega]
  · by_cases hcq : c<q
    · simp [hqc,hcq]
    · have heq : q=c := by omega
      simp [heq,Distance,hf]

def PrefixException (X : ℕ) : ℝ :=
  (∑d∈Finset.Icc 1 X,(d.divisors.card:ℝ)^2)+
    2*∑d∈Finset.Icc 1 X,(d.divisors.card:ℝ)

theorem actual_exception_split {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)=
      PrefixException (c.toNat-1)+PrefixException (N-c.toNat) := by
  have hs := actual_distance_sum_split hc (fun d=>(d.divisors.card:ℝ)^2) (by simp)
  have hf := actual_distance_sum_split hc (fun d=>(d.divisors.card:ℝ)) (by simp)
  simp only [WitnessException,Nat.cast_add,Nat.cast_mul,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat]
  rw [hs,hf]
  dsimp only [PrefixException]
  ring

theorem actual_prefix_exception_bound {X N : ℕ} (hXN : X≤N) (hN : 1≤N) :
    PrefixException X≤(X:ℝ)*(P3 (Real.log N)+2*Harmonic N) := by
  by_cases hX : X=0
  · simp [hX,PrefixException]
  have hX1 : 1≤X := by omega
  have hlogX : 0≤Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast hX1)
  have hlogN : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlog : Real.log (X:ℝ)≤Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0<X by omega)) (by exact_mod_cast hXN)
  have hp : P3 (Real.log (X:ℝ))≤P3 (Real.log N) := by
    dsimp only [P3]
    gcongr
  have hm := actual_divisor_second_moment_simplex hX1
  have hf := actual_divisor_first_moment X
  have hh := harmonic_mono hXN
  dsimp only [PrefixException]
  calc
    _≤(X:ℝ)*P3 (Real.log (X:ℝ))+2*((X:ℝ)*Harmonic X) := by linarith only [hm,hf]
    _≤(X:ℝ)*P3 (Real.log N)+2*((X:ℝ)*Harmonic N) := by gcongr
    _=_ := by ring

theorem actual_two_sided_exception {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      ((N-1:ℕ):ℝ)*(P3 (Real.log N)+2*Harmonic N) := by
  have hcG := (mem_ground N c).mp hc
  have hN : 1≤N := by omega
  have hl := actual_prefix_exception_bound (show c.toNat-1≤N by omega) hN
  have hr := actual_prefix_exception_bound (show N-c.toNat≤N by omega) hN
  have hlen : c.toNat-1+(N-c.toNat)=N-1 := by omega
  rw [actual_exception_split hc]
  calc
    _≤((c.toNat-1:ℕ):ℝ)*(P3 (Real.log N)+2*Harmonic N)+
        ((N-c.toNat:ℕ):ℝ)*(P3 (Real.log N)+2*Harmonic N) := add_le_add hl hr
    _=((c.toNat-1+(N-c.toNat):ℕ):ℝ)*(P3 (Real.log N)+2*Harmonic N) := by push_cast;ring
    _=_ := by rw [hlen]

theorem actual_half_simplex_exception {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*(P3 (Real.log N)+2*Harmonic N) := by
  have hcG := (mem_ground N c).mp hc
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have hcoef : 0≤P3 (Real.log N)+2*Harmonic N := by
    have hh := harmonic_nonneg N
    dsimp only [P3]
    positivity
  exact (actual_two_sided_exception hc).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (show N-1≤N by omega)) hcoef)

theorem half_simplex_polynomial (L H : ℝ) :
    P3 L+2*H=HarmonicLog55.SimplexPolynomial L H/2 := by
  dsimp only [P3,HarmonicLog55.SimplexPolynomial]
  ring

theorem actual_simplex_exception_half {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*HarmonicLog55.SimplexPolynomial (Real.log N) (Harmonic N)/2 := by
  have hh := actual_half_simplex_exception hc
  rw [half_simplex_polynomial] at hh
  nlinarith only [hh]

#check @actual_left_distance_sum
#check @actual_right_distance_sum
#check @actual_distance_sum_split
#check @actual_exception_split
#check @actual_prefix_exception_bound
#check @actual_two_sided_exception
#check @actual_half_simplex_exception
#check @half_simplex_polynomial
#check @actual_simplex_exception_half
#print axioms actual_left_distance_sum
#print axioms actual_right_distance_sum
#print axioms actual_distance_sum_split
#print axioms actual_exception_split
#print axioms actual_prefix_exception_bound
#print axioms actual_two_sided_exception
#print axioms actual_half_simplex_exception
#print axioms half_simplex_polynomial
#print axioms actual_simplex_exception_half
end
end JSP233.TwoSidedMoment62
