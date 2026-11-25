module

public import Erdos272.Arithmetic.N88404.PrimeSquareTail88404
public import Erdos272.Arithmetic.PrimeCover208

@[expose] public section

namespace JSP233.PrimeSquare88404
open CoreUnionSource200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Head : Finset ℕ := PrimeCover208.SmallPrimes.toFinset.filter (fun p => p<151)
def Starts : Finset ℕ := {151, 157, 161, 163, 167, 169, 173, 179}
def Tail (a r : ℕ) : Finset ℕ := (Finset.range a).image (fun j => 30*j+r)

theorem starts_range {r : ℕ} (hr : r∈Starts) : 151≤r ∧ r<181 := by
  simp only [Starts, Finset.mem_insert, Finset.mem_singleton] at hr
  omega

theorem residue_checked :
    ∀ r∈Finset.range 30, Nat.Coprime r 30 → 150+r∈Starts := by decide +kernel

theorem prime_cover (a : ℕ) : AllPrimes a ⊆ Head ∪ Starts.biUnion (Tail a) := by
  intro q hq
  obtain ⟨hqa, hp⟩ := Finset.mem_filter.mp hq
  by_cases hsmall : q<151
  · have hh := PrimeCover208.small_prime_cover (by omega : q≤181) hp
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨by simpa only [List.mem_toFinset] using hh, hsmall⟩)
  · have hc : Nat.Coprime q 30 := hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide : 0<30) (by omega : 30<q))
    have hmod : Nat.Coprime (q%30) 30 := by
      change Nat.gcd (q%30) 30=1
      rw [←Nat.gcd_rec 30 q, Nat.gcd_comm]
      exact hc
    have hr := residue_checked (q%30) (Finset.mem_range.mpr (Nat.mod_lt q (by decide))) hmod
    let j := q/30-5
    have he : 30*j+(150+q%30)=q := by
      have hd := Nat.mod_add_div q 30
      dsimp only [j]
      omega
    have hj : j<a := by
      have hlt := Finset.mem_range.mp hqa
      dsimp only [j]
      omega
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨150+q%30, hr, Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, he⟩⟩)

theorem head_disjoint (a : ℕ) : Disjoint Head (Starts.biUnion (Tail a)) := by
  apply Finset.disjoint_left.mpr
  intro q hhead htail
  have hsmall := (Finset.mem_filter.mp hhead).2
  obtain ⟨r, hr, hj⟩ := Finset.mem_biUnion.mp htail
  obtain ⟨j, _hja, he⟩ := Finset.mem_image.mp hj
  have hb := starts_range hr
  omega

theorem tails_disjoint (a : ℕ) : Set.PairwiseDisjoint (↑Starts) (Tail a) := by
  intro r hr s hs hrs
  apply Finset.disjoint_left.mpr
  intro q hqr hqs
  obtain ⟨j, _hj, he⟩ := Finset.mem_image.mp hqr
  obtain ⟨k, _hk, hf⟩ := Finset.mem_image.mp hqs
  have hbr := starts_range hr
  have hbs := starts_range hs
  exact hrs (by omega)

theorem tail_sum_bound (a r : ℕ) (hr : 15<r) :
    (∑ q∈Tail a r, (1 : ℝ)/(q : ℝ)^2) ≤ 1/(30*((r : ℝ)-15)) := by
  have hinj : Function.Injective (fun j : ℕ => 30*j+r) := by
    intro i j he
    change 30*i+r=30*j+r at he
    omega
  have he : (∑ q∈Tail a r, (1 : ℝ)/(q : ℝ)^2) =
      ∑ j∈Finset.range a, (1 : ℝ)/(30*(j : ℝ)+r)^2 := by
    rw [Tail, Finset.sum_image hinj.injOn]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [he]
  exact PrimeSquareTail88404.sum_bound a r hr

theorem fixed_sum_bound :
    (∑ q∈Head, (1 : ℝ)/(q : ℝ)^2)+
      (∑ r∈Starts, (1 : ℝ)/(30*((r : ℝ)-15))) ≤ 453/1000 := by
  norm_num [Head, PrimeCover208.SmallPrimes, Starts, Finset.sum_filter]

theorem prime_square_sum (a : ℕ) :
    (∑ q∈AllPrimes a, (1 : ℝ)/(q : ℝ)^2) ≤ 453/1000 := by
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (prime_cover a)
    (fun q _ _ => by positivity : ∀ q∈Head ∪ Starts.biUnion (Tail a), q∉AllPrimes a →
      (0 : ℝ) ≤ 1/(q : ℝ)^2)
  rw [Finset.sum_union (head_disjoint a), Finset.sum_biUnion (tails_disjoint a)] at hs
  have ht := Finset.sum_le_sum (s := Starts) (fun r hr =>
    tail_sum_bound a r (by have hb := starts_range hr; omega))
  linarith only [hs, ht, fixed_sum_bound]

#print axioms starts_range
#print axioms residue_checked
#print axioms prime_cover
#print axioms head_disjoint
#print axioms tails_disjoint
#print axioms tail_sum_bound
#print axioms fixed_sum_bound
#print axioms prime_square_sum
end
end JSP233.PrimeSquare88404
