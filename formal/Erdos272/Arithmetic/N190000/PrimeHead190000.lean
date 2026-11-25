module

public import Erdos272.Core.N200000.QuantitativeUnit200000

@[expose] public section

namespace JSP233.PrimeHead190000
open CoreUnionSource200000 PrimeQuadratic200000 DyadicReciprocal200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Head : Finset ℕ := {2, 3, 5, 7, 11}

def OddTail (a : ℕ) : Finset ℕ :=
  (Finset.range a).image (fun j : ℕ => 2*j+13)

theorem prime_cover (a : ℕ) : AllPrimes a ⊆ Head ∪ OddTail a := by
  intro q hq
  obtain ⟨hr, hp⟩ := Finset.mem_filter.mp hq
  by_cases hsmall : q < 13
  · have hc : ∀ q ∈ Finset.range 13, Nat.Prime q → q ∈ Head := by decide +kernel
    exact Finset.mem_union_left _ (hc q (Finset.mem_range.mpr hsmall) hp)
  · have hodd : q % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
    let j := (q-13)/2
    have he : 2*j+13 = q := by dsimp only [j]; omega
    have hj : j < a := by
      have hlt := Finset.mem_range.mp hr
      dsimp only [j]
      omega
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, he⟩)

theorem tail_step (j : ℕ) :
    (1 : ℝ)/(2*(j : ℝ)+13)^2 ≤
      1/(4*((j : ℝ)+6))-1/(4*((j : ℝ)+7)) := by
  convert odd_square_step (j+5) using 1 <;> push_cast <;> ring

theorem tail_sum (a : ℕ) :
    (∑ j ∈ Finset.range a, (1 : ℝ)/(2*(j : ℝ)+13)^2) ≤ 1/24 := by
  have hstrong : (∑ j ∈ Finset.range a, (1 : ℝ)/(2*(j : ℝ)+13)^2) ≤
      1/24-1/(4*((a : ℝ)+6)) := by
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [Finset.sum_range_succ]
      have hs := tail_step a
      have he : ((a+1 : ℕ) : ℝ)+6 = (a : ℝ)+7 := by push_cast; ring
      rw [he]
      linarith only [ih, hs]
  have hn : (0 : ℝ) ≤ 1/(4*((a : ℝ)+6)) := by positivity
  linarith only [hstrong, hn]

theorem prime_square_sum_sharp (a : ℕ) :
    (∑ q ∈ AllPrimes a, (1 : ℝ)/(q : ℝ)^2) ≤ 19/40 := by
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (prime_cover a)
    (fun q _ _ => by positivity : ∀ q ∈ Head ∪ OddTail a, q ∉ AllPrimes a →
      (0 : ℝ) ≤ 1/(q : ℝ)^2)
  have hdis : Disjoint Head (OddTail a) := by
    apply Finset.disjoint_left.mpr
    intro q hhead htail
    obtain ⟨j, _hj, he⟩ := Finset.mem_image.mp htail
    have hh : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 := by simpa [Head] using hhead
    omega
  have hu : (∑ q ∈ Head ∪ OddTail a, (1 : ℝ)/(q : ℝ)^2) =
      (∑ q ∈ Head, (1 : ℝ)/(q : ℝ)^2)+
      ∑ q ∈ OddTail a, (1 : ℝ)/(q : ℝ)^2 :=
    Finset.sum_union hdis
  have hinj : Function.Injective (fun j : ℕ => 2*j+13) := by
    intro i j he
    dsimp only at he
    omega
  have he : (∑ q ∈ OddTail a, (1 : ℝ)/(q : ℝ)^2) =
      ∑ j ∈ Finset.range a, (1 : ℝ)/(2*(j : ℝ)+13)^2 := by
    rw [OddTail, Finset.sum_image hinj.injOn]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [he] at hu
  have ht := tail_sum a
  have hhead : (∑ q ∈ Head, (1 : ℝ)/(q : ℝ)^2) = 2293369/5336100 := by norm_num [Head]
  rw [hhead] at hu
  linarith only [hs, hu, ht]

def SmallPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
   67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137,
   139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199,
   211, 223, 227, 229, 233, 239, 241, 251}

theorem small_primes_correct : AllPrimes 256 = SmallPrimes := by
  decide +kernel

theorem small_reciprocal {a : ℕ} (ha : a ≤ 256) :
    (∑ q ∈ AllPrimes a, (1 : ℝ)/(q : ℝ)) ≤ 2 := by
  have hsub : AllPrimes a ⊆ AllPrimes 256 := by
    intro q hq
    obtain ⟨hr, hp⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hr).trans_le ha), hp⟩
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => by positivity : ∀ q ∈ AllPrimes 256, q ∉ AllPrimes a →
      (0 : ℝ) ≤ 1/(q : ℝ))
  rw [small_primes_correct] at hs
  have hhead : (∑ q ∈ SmallPrimes, (1 : ℝ)/(q : ℝ)) ≤ 2 := by
    norm_num [SmallPrimes]
  exact hs.trans hhead

#print axioms prime_cover
#print axioms tail_step
#print axioms tail_sum
#print axioms prime_square_sum_sharp
#print axioms small_primes_correct
#print axioms small_reciprocal
end
end JSP233.PrimeHead190000
