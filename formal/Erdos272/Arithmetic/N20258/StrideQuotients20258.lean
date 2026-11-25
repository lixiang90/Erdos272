module

public import Erdos272.Counting.N20258.ProgressionPartition20258

@[expose] public section
/-! Evaluate the tail using the small strides and the small quotients.
For example, at N=20258 a split at 142 uses only 283 summands. -/
namespace JSP233.StrideQuotients20258
open ProgressionLengths20258 ProgressionPartition20258
open scoped BigOperators
set_option autoImplicit false

def grouped (n a : ℕ) (f : ℕ → ℕ) : ℕ :=
  (∑ d ∈ Finset.Icc 1 a, f (n/d)) +
    ∑ q ∈ Finset.Icc 1 (n/(a+1)), (n/q-max a (n/(q+1)))*f q

def compactTail (n k a : ℕ) (kept : Finset ℕ) : ℕ :=
  grouped n a (fun q => tail q k) - ∑ d ∈ kept, tail (n/d) k

private theorem quotient_fiber (n a q : ℕ) (hq : 0 < q) :
    (Finset.Ioc a n).filter (fun d => n/d=q) = Finset.Ioc (max a (n/(q+1))) (n/q) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc, max_lt_iff]
  constructor
  · rintro ⟨⟨had,_⟩,hdq⟩
    have hd : 0 < d := by omega
    have lo := (Nat.div_lt_iff_lt_mul hd).mp (show n/d < q+1 by omega)
    have hi := (Nat.le_div_iff_mul_le hd).mp (show q ≤ n/d by omega)
    exact ⟨⟨had,(Nat.div_lt_iff_lt_mul (by omega : 0 < q+1)).mpr (by simpa [Nat.mul_comm] using lo)⟩,
      (Nat.le_div_iff_mul_le hq).mpr (by simpa [Nat.mul_comm] using hi)⟩
  · rintro ⟨⟨had,hlo⟩,hhi⟩
    have hd : 0 < d := by omega
    have lo := (Nat.div_lt_iff_lt_mul (by omega : 0 < q+1)).mp hlo
    have hi := (Nat.le_div_iff_mul_le hq).mp hhi
    have lower : q ≤ n/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hi)
    have upper : n/d < q+1 := (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using lo)
    exact ⟨⟨had,hhi.trans (Nat.div_le_self _ _)⟩,by omega⟩

theorem grouped_eq (n a : ℕ) (ha : a ≤ n) (f : ℕ → ℕ) :
    grouped n a f = ∑ d ∈ Finset.Icc 1 n, f (n/d) := by
  let D := Finset.Ioc a n
  let Q := Finset.Icc 1 (n/(a+1))
  have maps (d : ℕ) (hd : d ∈ D) : n/d ∈ Q := by
    obtain ⟨had,hdn⟩ := Finset.mem_Ioc.mp hd
    have hpos : 0 < d := by omega
    apply Finset.mem_Icc.mpr
    constructor
    · apply (Nat.le_div_iff_mul_le hpos).mpr
      simpa using hdn
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < a+1)).mpr
      exact (Nat.mul_le_mul_left (n/d) (by omega : a+1 ≤ d)).trans (Nat.div_mul_le_self n d)
  have fibers : (∑ d ∈ D, f (n/d)) =
      ∑ q ∈ Q, (n/q-max a (n/(q+1)))*f q := by
    calc
      _ = ∑ q ∈ Q, ∑ d ∈ D.filter (fun d => n/d=q), f (n/d) :=
        (Finset.sum_fiberwise_of_maps_to maps (fun d => f (n/d))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        have pos := (Finset.mem_Icc.mp hq).1
        calc
          _ = ∑ _d ∈ D.filter (fun d => n/d=q), f q := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [(Finset.mem_filter.mp hd).2]
          _ = _ := by simp [D,quotient_fiber n a q pos]
  have sub : Finset.Icc 1 a ⊆ Finset.Icc 1 n := by
    intro d hd
    obtain ⟨hd1,hda⟩ := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨hd1,hda.trans ha⟩
  have diff : Finset.Icc 1 n \ Finset.Icc 1 a = D := by
    ext d
    simp only [D, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have split := Finset.sum_sdiff (f := fun d => f (n/d)) sub
  rw [diff,fibers] at split
  unfold grouped
  change _ + (∑ q ∈ Q, _) = _
  omega

theorem compact_tail_eq {n k a : ℕ} (ha : a ≤ n) {kept : Finset ℕ}
    (hs : kept ⊆ Finset.Icc 1 n) : compactTail n k a kept = offTail n k kept := by
  unfold compactTail offTail
  rw [grouped_eq n a ha]
  have h := Finset.sum_sdiff (f := fun d => tail (n/d) k) hs
  omega

end JSP233.StrideQuotients20258
