module

public import Std

@[expose] public section

/-! The length distribution in a grid with `q+1` sites. Its increasing
and decreasing pieces each have a triangular sum. -/
namespace JSP233.ProgressionLengths20258

def starts (q length : Nat) : Nat := min length (q+2-length)

def triangle (n : Nat) : Nat := n*(n+1)/2

theorem triangle_succ (n : Nat) : triangle (n+1) = triangle n + n+1 := by
  unfold triangle
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem triangle_mono {a b : Nat} (hab : a ≤ b) : triangle a ≤ triangle b := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hab
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih =>
    rw [Nat.add_succ, triangle_succ]
    omega

/-- Number of nonempty grid intervals through a median site whose length
is strictly greater than the cutoff. The callers use a cutoff of at least
one, so that singletons can be counted once for the entire family. -/
def tail (q cutoff : Nat) : Nat :=
  let mid := (q+2)/2
  triangle mid - triangle (min mid cutoff) + triangle (q+1-max mid cutoff)

theorem tail_after_last {q k : Nat} (h : q+1 ≤ k) : tail q k = 0 := by
  have hm : (q+2)/2 ≤ k := by omega
  simp only [tail, Nat.min_eq_left hm, Nat.max_eq_right hm, Nat.sub_eq_zero_of_le h,
    Nat.sub_self, Nat.zero_add]
  rfl

/-- Removing the next length subtracts exactly its number of starts. -/
theorem tail_step (q k : Nat) : tail q k = starts q (k+1) + tail q (k+1) := by
  by_cases hl : k < (q+2)/2
  · have hkm : k+1 ≤ (q+2)/2 := by omega
    have hshort : k+1 ≤ q+2-(k+1) := by omega
    have ht := triangle_mono hkm
    simp only [tail, starts, Nat.min_eq_left hshort, Nat.min_eq_right hkm,
      Nat.min_eq_right (Nat.le_of_lt hl), Nat.max_eq_left hkm,
      Nat.max_eq_left (Nat.le_of_lt hl), triangle_succ] at *
    omega
  · have hm : (q+2)/2 ≤ k := by omega
    have hm' : (q+2)/2 ≤ k+1 := by omega
    have hlong : q+2-(k+1) ≤ k+1 := by omega
    simp only [tail, starts, Nat.min_eq_right hlong, Nat.min_eq_left hm,
      Nat.min_eq_left hm', Nat.max_eq_right hm, Nat.max_eq_right hm',
      Nat.sub_self, Nat.zero_add]
    by_cases hk : k < q+1
    · have hsucc : q+1-k = (q+1-(k+1))+1 := by omega
      rw [hsucc,triangle_succ]
      omega
    · have hz : q+1-k = 0 := by omega
      have hz' : q+1-(k+1) = 0 := by omega
      have hz'' : q+2-(k+1) = 0 := by omega
      simp [hz,hz',hz'',triangle]

theorem tail_antitone (q : Nat) {i j : Nat} (h : i ≤ j) : tail q j ≤ tail q i := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    have hstep := tail_step q (i+k)
    change tail q (i+k+1) ≤ tail q i
    omega

/-- The legal left endpoints through site `z` are in the intersection of
two integer ranges. -/
theorem grid_start_cap (q z length : Nat) (hl : 1 ≤ length) (hf : length ≤ q+1) :
    min z (q+1-length) + 1 - (z+1-length) ≤ starts q length := by
  unfold starts
  omega

end JSP233.ProgressionLengths20258
