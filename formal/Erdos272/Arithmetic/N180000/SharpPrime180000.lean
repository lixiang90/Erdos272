module

public import Erdos272.Core.N200000.QuantitativeUnit200000

@[expose] public section

namespace JSP233.SharpPrime180000
open CoreUnionSource200000 PrimeQuadratic200000 DyadicReciprocal200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Head : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41}

def OddTail (a : ℕ) : Finset ℕ :=
  (Finset.range a).image (fun j : ℕ => 2*j+43)

theorem prime_cover (a : ℕ) : AllPrimes a ⊆ Head ∪ OddTail a := by
  intro q hq
  obtain ⟨hr, hp⟩ := Finset.mem_filter.mp hq
  by_cases hsmall : q < 43
  · have hc : ∀ q ∈ Finset.range 43, Nat.Prime q → q ∈ Head := by decide +kernel
    exact Finset.mem_union_left _ (hc q (Finset.mem_range.mpr hsmall) hp)
  · have hodd : q % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
    let j := (q-43)/2
    have he : 2*j+43 = q := by dsimp only [j]; omega
    have hj : j < a := by
      have hlt := Finset.mem_range.mp hr
      dsimp only [j]
      omega
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, he⟩)

theorem tail_step (j : ℕ) :
    (1 : ℝ)/(2*(j : ℝ)+43)^2 ≤
      1/(4*((j : ℝ)+21))-1/(4*((j : ℝ)+22)) := by
  convert odd_square_step (j+20) using 1 <;> push_cast <;> ring

theorem tail_sum (a : ℕ) :
    (∑ j ∈ Finset.range a, (1 : ℝ)/(2*(j : ℝ)+43)^2) ≤ 1/84 := by
  have hstrong : (∑ j ∈ Finset.range a, (1 : ℝ)/(2*(j : ℝ)+43)^2) ≤
      1/84-1/(4*((a : ℝ)+21)) := by
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [Finset.sum_range_succ]
      have hs := tail_step a
      have he : ((a+1 : ℕ) : ℝ)+21 = (a : ℝ)+22 := by push_cast; ring
      rw [he]
      linarith only [ih, hs]
  have hn : (0 : ℝ) ≤ 1/(4*((a : ℝ)+21)) := by positivity
  linarith only [hstrong, hn]

theorem prime_square_sum_sharp (a : ℕ) :
    (∑ q ∈ AllPrimes a, (1 : ℝ)/(q : ℝ)^2) ≤ 23/50 := by
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (prime_cover a)
    (fun q _ _ => by positivity : ∀ q ∈ Head ∪ OddTail a, q ∉ AllPrimes a →
      (0 : ℝ) ≤ 1/(q : ℝ)^2)
  have hdis : Disjoint Head (OddTail a) := by
    apply Finset.disjoint_left.mpr
    intro q hhead htail
    obtain ⟨j, _hj, he⟩ := Finset.mem_image.mp htail
    have hh : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23 ∨ q = 29 ∨ q = 31 ∨ q = 37 ∨ q = 41 := by simpa [Head] using hhead
    omega
  have hu : (∑ q ∈ Head ∪ OddTail a, (1 : ℝ)/(q : ℝ)^2) =
      (∑ q ∈ Head, (1 : ℝ)/(q : ℝ)^2)+
      ∑ q ∈ OddTail a, (1 : ℝ)/(q : ℝ)^2 :=
    Finset.sum_union hdis
  have hinj : Function.Injective (fun j : ℕ => 2*j+43) := by
    intro i j he
    dsimp only at he
    omega
  have he : (∑ q ∈ OddTail a, (1 : ℝ)/(q : ℝ)^2) =
      ∑ j ∈ Finset.range a, (1 : ℝ)/(2*(j : ℝ)+43)^2 := by
    rw [OddTail, Finset.sum_image hinj.injOn]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [he] at hu
  have ht := tail_sum a
  have hhead : (∑ q ∈ Head, (1 : ℝ)/(q : ℝ)^2) = 41412850736015889039729489289/92568222856376731590410384100 := by norm_num [Head]
  rw [hhead] at hu
  linarith only [hs, hu, ht]

#print axioms prime_cover
#print axioms tail_step
#print axioms tail_sum
#print axioms prime_square_sum_sharp
end
end JSP233.SharpPrime180000
