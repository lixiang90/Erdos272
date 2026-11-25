module

public import Erdos272.Counting.N20258.ProgressionPartition20258
public import Erdos272.Counting.EndpointDensity54
public import Erdos272.Arithmetic.HarmonicSharp39

@[expose] public section
namespace JSP233.LengthTailBound20258
open ProgressionLengths20258 HarmonicAbel29
open scoped BigOperators
noncomputable section
set_option autoImplicit false

private theorem double_triangle (n : ℕ) : 2*triangle n=n*(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [triangle_succ]; nlinarith only [ih]

private theorem median_count (q : ℕ) : 4*tail q 1 ≤ q^2+4*q := by
  let k := q/2
  have mid : (q+2)/2=k+1 := by dsimp [k]; omega
  have m : 1 ≤ k+1 := by omega
  have one : triangle 1=1 := rfl
  have pos : 1 ≤ triangle (k+1) := one ▸ triangle_mono m
  have sub := Nat.sub_add_cancel pos
  have tr := triangle_succ k
  have dt := double_triangle k
  simp only [tail,mid,Nat.min_eq_right m,Nat.max_eq_left m,one]
  by_cases even : q%2=0
  · have eq : q=2*k := by dsimp [k]; omega
    have right : q+1-(k+1)=k := by omega
    rw [right,eq]
    nlinarith only [tr,sub,dt]
  · have eq : q=2*k+1 := by dsimp [k]; omega
    have right : q+1-(k+1)=k+1 := by omega
    rw [right,eq]
    nlinarith only [tr,sub,dt]

def total (n k : ℕ) := ∑ d ∈ Finset.Icc 1 n, tail (n/d) k

private theorem all_lengths (n : ℕ) :
    (total n 1 : ℝ) ≤ (329/800 : ℝ)*(n : ℝ)^2+n*Harmonic n := by
  have each (d : ℕ) :
      (tail (n/d) 1 : ℝ) ≤ ((n : ℝ)^2/4)*(1/(d : ℝ)^2)+n*(1/(d : ℝ)) := by
    have raw : 4*(tail (n/d) 1 : ℝ) ≤ ((n/d : ℕ) : ℝ)^2+4*(n/d : ℕ) := by
      exact_mod_cast median_count (n/d)
    have h := Nat.cast_div_le (α := ℝ) (m := n) (n := d)
    have sq := pow_le_pow_left₀ (Nat.cast_nonneg (n/d)) h 2
    rw [div_pow] at sq
    simp only [div_eq_mul_inv,one_mul] at h sq ⊢
    linarith only [raw,h,sq]
  have sum := Finset.sum_le_sum (s := Finset.Icc 1 n) (fun d _ => each d)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at sum
  have sq := EndpointDensity54.reciprocal_square_upper n
  have w := mul_le_mul_of_nonneg_left sq (show 0 ≤ (n : ℝ)^2/4 by positivity)
  unfold CoprimeDensity52.reciprocalSquareSum at w
  dsimp only [total,Harmonic]
  push_cast
  simp only [one_div] at sum ⊢
  linarith only [sum,w]

/-- At length k+1 every spacing d ≤ n/(2k) has exactly k+1 starts through
the median. Summing this common lower bound removes a full linear term. -/
private theorem next_length (n k : ℕ) (hk : 1 ≤ k) :
    n+2*total n (k+1) ≤ 2*total n k+2*(k+1) := by
  let m := n/(2*k)
  let layer (d : ℕ) := starts (n/d) (k+1)
  have inside : Finset.Icc 1 m ⊆ Finset.Icc 1 n := by
    intro d hd
    obtain ⟨hd,top⟩ := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨hd,top.trans (Nat.div_le_self _ _)⟩
  have full (d : ℕ) (hd : d ∈ Finset.Icc 1 m) : layer d=k+1 := by
    obtain ⟨dp,top⟩ := Finset.mem_Icc.mp hd
    have w := Nat.mul_le_mul_right (2*k) top
    have a : d*(2*k) ≤ n := w.trans (Nat.div_mul_le_self _ _)
    have fits : 2*k ≤ n/d := (Nat.le_div_iff_mul_le dp).mpr (by simpa only [Nat.mul_comm] using a)
    dsimp [layer,starts]
    exact Nat.min_eq_left (by omega)
  have cover : m*(k+1) ≤ ∑ d ∈ Finset.Icc 1 n, layer d := calc
    _ = ∑ d ∈ Finset.Icc 1 m, (k+1) := by simp
    _ = ∑ d ∈ Finset.Icc 1 m, layer d := Finset.sum_congr rfl (fun d hd => (full d hd).symm)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg inside (fun _ _ _ => Nat.zero_le _)
  have split : total n k = (∑ d ∈ Finset.Icc 1 n, layer d)+total n (k+1) := by
    unfold total
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun d _ => tail_step (n/d) k)
  have rem : n < (m+1)*(2*k) := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2*k)).mp (Nat.lt_succ_self m)
  nlinarith only [cover,split,rem]

private theorem removed (n j : ℕ) :
    j*n+2*total n (j+1)+2 ≤ 2*total n 1+(j+1)*(j+2) := by
  induction j with
  | zero => simp
  | succ j ih => nlinarith only [ih,next_length n (j+1) (by omega)]

theorem forty {n : ℕ} (hi : n < 2^16) :
    ((ProgressionPartition20258.offTail n 40 ∅ : ℕ) : ℝ) ≤
      (329/800 : ℝ)*(n : ℝ)^2-(15/2 : ℝ)*n+819 := by
  have upper := all_lengths n
  have low := removed n 39
  have lowR : 39*(n : ℝ)+2*(total n 40 : ℝ)+2 ≤ 2*(total n 1 : ℝ)+40*41 := by
    exact_mod_cast low
  have harm : Harmonic n ≤ 12 :=
    (HarmonicSharp39.actual_harmonic_tight n 16 hi).trans (by norm_num)
  have paid := mul_le_mul_of_nonneg_left harm (Nat.cast_nonneg (α := ℝ) n)
  simp only [ProgressionPartition20258.offTail,Finset.sdiff_empty]
  change (total n 40 : ℝ) ≤ _
  linarith only [upper,lowR,paid]

#print axioms forty

/-- One more removed layer, with the harmonic estimate on the smaller ground. -/
theorem forty_one {n : ℕ} (hi : n < 2^15) :
    ((ProgressionPartition20258.offTail n 41 ∅ : ℕ) : ℝ) ≤
      (329/800 : ℝ)*(n : ℝ)^2-(89/10 : ℝ)*n+860 := by
  have upper := all_lengths n
  have low : 40*(n : ℝ)+2*(total n 41 : ℝ)+2 ≤ 2*(total n 1 : ℝ)+41*42 := by
    exact_mod_cast removed n 40
  have harm : Harmonic n ≤ (111/10 : ℝ) :=
    (HarmonicSharp39.actual_harmonic_tight n 15 hi).trans (by norm_num)
  have paid := mul_le_mul_of_nonneg_left harm (Nat.cast_nonneg (α := ℝ) n)
  simp only [ProgressionPartition20258.offTail,Finset.sdiff_empty]
  change (total n 41 : ℝ) ≤ _
  linarith only [low,upper,paid]

/-- A median grid retains its quadratic contribution after the first k
lengths are removed. This lower bound pays back the explicitly priced grids. -/
theorem grid_lower {n d k : ℕ} (hd : 0 < d) (fits : k ≤ (n/d+2)/2) :
    (n : ℝ)^2/(4*(d : ℝ)^2) ≤ (tail (n/d) k : ℝ)+triangle k := by
  let q := n/d
  let a := (q+2)/2
  let b := q+1-a
  have ha : k ≤ a := fits
  have half (j : ℕ) : (j+2)/2 ≤ j+1 := by omega
  have ab : a+b=q+1 := (Nat.add_comm a b).trans (Nat.sub_add_cancel (half q))
  have cuts : tail q k+triangle k=triangle a+triangle b := by
    change triangle a-triangle (min a k)+triangle (q+1-max a k)+triangle k=_
    rw [Nat.min_eq_right ha,Nat.max_eq_left ha]
    have := triangle_mono ha
    dsimp only [b]
    omega
  have tri (j : ℕ) : 2*(triangle j : ℝ)=(j : ℝ)*(j+1) := by exact_mod_cast double_triangle j
  have abR : (a : ℝ)+b=(q : ℝ)+1 := by exact_mod_cast ab
  have cutsR : (tail q k : ℝ)+triangle k=(triangle a : ℝ)+triangle b := by exact_mod_cast cuts
  have sq : ((q : ℝ)+1)^2 ≤ 4*((tail q k : ℝ)+triangle k) := by
    rw [←abR,cutsR]
    nlinarith only [tri a,tri b,sq_nonneg ((a : ℝ)-b),Nat.cast_nonneg (α := ℝ) a,Nat.cast_nonneg (α := ℝ) b]
  have rem : n < (q+1)*d := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self q)
  have hr : (n : ℝ) ≤ ((q : ℝ)+1)*d := by exact_mod_cast rem.le
  have dp : (0 : ℝ) < d := by exact_mod_cast hd
  have rat := (div_le_iff₀ dp).mpr hr
  have square := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg n) dp.le) rat 2
  rw [div_pow] at square
  linarith only [square,sq,show (n : ℝ)^2/(4*(d : ℝ)^2) = ((n : ℝ)^2/(d : ℝ)^2)/4 by ring]

#print axioms forty_one
end
end JSP233.LengthTailBound20258
