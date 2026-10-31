import Erdos272.Arithmetic.LightClosed208
import Erdos272.Resources.RightWindows208

namespace JSP233.WindowCounts208
open LightClosed208
set_option maxHeartbeats 0

def RightLeft (q J B : ℕ) : ℕ := (q-J+B-1)/B
def rightIndexCount (q A J B : ℕ) : ℕ := Count q A B-RightLeft q J B
def Last (C B hi : ℕ) : ℕ := C+(hi-C)/B*B
def maximum (A J B lo hi : ℕ) : ℕ :=
  max (rightIndexCount lo A J B)
    (if A≤hi ∧ lo≤Last A B hi then min (Count J A B) (Count hi A B) else 0)

theorem rightLeft_le {q J B r : ℕ} (hB : 0<B) : RightLeft q J B≤r ↔ q≤J+r*B := by
  unfold RightLeft
  constructor
  · intro h
    have hd : (q-J+B-1)/B<r+1 := by omega
    have hm := (Nat.div_lt_iff_lt_mul hB).mp hd
    rw [Nat.add_mul] at hm
    omega
  · intro h
    have hm : q-J+B-1<(r+1)*B := by rw [Nat.add_mul];omega
    have hd := (Nat.div_lt_iff_lt_mul hB).mpr hm
    omega

theorem rightLeft_mono {q q' J B : ℕ} (hqq : q≤q') : RightLeft q J B≤RightLeft q' J B := by
  exact Nat.div_le_div_right (by omega : q-J+B-1≤q'-J+B-1)

theorem count_mono {q q' A B : ℕ} (hB : 0<B) (hqq : q≤q') : Count q A B≤Count q' A B := by
  by_contra! h
  have hh := (lt_count hB).mp h
  have hb : Count q' A B<Count q' A B := (lt_count hB).mpr (by omega)
  exact Nat.lt_irrefl _ hb

theorem grid_le_last {C B hi r : ℕ} (hB : 0<B) (hr : C+r*B≤hi) : C+r*B≤Last C B hi := by
  have hmul : r*B≤hi-C := by omega
  have hd := (Nat.le_div_iff_mul_le hB).mpr hmul
  have hm := Nat.mul_le_mul_right B hd
  unfold Last
  omega

theorem last_le {C B hi : ℕ} (hC : C≤hi) : Last C B hi≤hi := by
  have hm := Nat.div_mul_le_self (hi-C) B
  unfold Last
  omega

theorem count_eq_of_no_last {lo hi C B : ℕ} (hB : 0<B) (hlohi : lo≤hi)
    (hno : ¬(C≤hi ∧ lo≤Last C B hi)) : Count lo C B=Count hi C B := by
  have hle := count_mono (A:=C) hB hlohi
  apply Nat.le_antisymm hle
  by_contra! hh
  have hhi := (lt_count hB).mp hh
  have hlo : ¬(C+Count lo C B*B≤lo) := by
    intro h
    exact Nat.lt_irrefl _ ((lt_count hB).mpr h)
  have hlast := grid_le_last hB hhi
  exact hno ⟨by omega,by omega⟩

theorem rightLeft_eq_of_no_last {lo hi J B : ℕ} (hB : 0<B) (hlohi : lo≤hi)
    (hno : ¬(J≤hi ∧ lo≤Last J B hi)) : RightLeft lo J B=RightLeft hi J B := by
  have hle := rightLeft_mono (J:=J) (B:=B) hlohi
  apply Nat.le_antisymm hle
  by_contra! hh
  have hlo : lo≤J+RightLeft lo J B*B := (rightLeft_le hB).mp le_rfl
  have hhi : ¬(hi≤J+RightLeft lo J B*B) := by
    intro h
    have hx := (rightLeft_le hB).mpr h
    omega
  have hlast := grid_le_last hB (by omega : J+RightLeft lo J B*B≤hi)
  exact hno ⟨by omega,by omega⟩

theorem rightLeft_le_count {q A J B : ℕ} (hB : 0<B) (hAJ : A≤J) : RightLeft q J B≤Count q A B := by
  apply (rightLeft_le hB).mpr
  have hnot : ¬(A+Count q A B*B≤q) := by
    intro h
    exact Nat.lt_irrefl _ ((lt_count hB).mpr h)
  omega

theorem rightCount_le_period {q A J B : ℕ} (hB : 0<B) : rightIndexCount q A J B≤Count J A B := by
  let u:=RightLeft q J B
  let L:=Count q A B
  let H:=Count J A B
  change L-u≤H
  by_contra! hh
  have hu : u+H<L := by omega
  have hs : A+(u+H)*B≤q := (lt_count hB).mp hu
  have hc : q≤J+u*B := (rightLeft_le hB).mp le_rfl
  rw [Nat.add_mul] at hs
  have hH : A+H*B≤J := by omega
  exact Nat.lt_irrefl _ ((lt_count hB).mpr hH)

theorem rightCount_le_count (q A J B : ℕ) : rightIndexCount q A J B≤Count q A B := Nat.sub_le _ _

theorem maximum_bound {A J B lo hi q : ℕ} (hB : 0<B) (hlo : lo≤q) (hhi : q≤hi) :
    rightIndexCount q A J B≤maximum A J B lo hi := by
  unfold maximum
  by_cases hj : A≤hi ∧ lo≤Last A B hi
  · rw [if_pos hj]
    apply le_trans _ (le_max_right _ _)
    exact le_min (rightCount_le_period hB)
      ((rightCount_le_count q A J B).trans (count_mono hB hhi))
  · rw [if_neg hj]
    apply le_trans _ (le_max_left _ _)
    have heq := count_eq_of_no_last hB (hlo.trans hhi) hj
    have hlow := count_mono (A:=A) hB hlo
    have hhigh := count_mono (A:=A) hB hhi
    have hcounts : Count q A B=Count lo A B := by omega
    have hleft := rightLeft_mono (J:=J) (B:=B) hlo
    unfold rightIndexCount
    rw [hcounts]
    omega

theorem rightIndexCount_eq_Icc {q A J B : ℕ} (hq : A≤q) :
    rightIndexCount q A J B=(Finset.Icc (RightLeft q J B) ((q-A)/B)).card := by
  simp only [rightIndexCount,Count,if_pos hq,Nat.card_Icc]

#print axioms maximum_bound
#print axioms rightIndexCount_eq_Icc
end JSP233.WindowCounts208
