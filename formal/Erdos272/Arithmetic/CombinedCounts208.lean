import Erdos272.Arithmetic.WindowCounts208
import Erdos272.Resources.HeavyMenu208

namespace JSP233.CombinedCounts208
open LightClosed208 WindowCounts208
set_option maxHeartbeats 0

def Combined (q A K B h : ℕ) : ℕ := min h (Count q K B)+rightIndexCount q A (K-1) B
def Switch (K B h : ℕ) : ℕ := K+(h-1)*B
def maximum_combined (A K B h lo hi : ℕ) : ℕ :=
  max (if lo<Switch K B h then Count (min hi (Switch K B h-1)) A B else 0)
    (if Switch K B h≤hi then h+maximum A (K-1) B (max lo (Switch K B h)) hi else 0)

theorem rightLeft_eq_count {q K B : ℕ} (hB : 0<B) (hK : 0<K) : RightLeft q (K-1) B=Count q K B := by
  apply Nat.le_antisymm
  · apply (rightLeft_le hB).mpr
    have hh : ¬(K+Count q K B*B≤q) := by
      intro hh
      exact Nat.lt_irrefl _ ((lt_count hB).mpr hh)
    omega
  · by_contra! hh
    have hs := (lt_count hB).mp hh
    have hc : q≤K-1+RightLeft q (K-1) B*B := (rightLeft_le hB).mp le_rfl
    omega

theorem combined_before {q A K B h : ℕ} (hB : 0<B) (hK : 0<K) (hH : 0<h)
    (hAK : A≤K) (hq : q<Switch K B h) : Combined q A K B h=Count q A B := by
  have hnot : ¬h-1<Count q K B := by
    intro hh
    have hs := (lt_count hB).mp hh
    unfold Switch at hq
    omega
  have hsmall : Count q K B≤h := by omega
  have hle := count_antitone (q:=q) hB hAK
  unfold Combined rightIndexCount
  rw [min_eq_right hsmall,rightLeft_eq_count hB hK]
  omega

theorem combined_after {q A K B h : ℕ} (hB : 0<B) (hH : 0<h)
    (hq : Switch K B h≤q) : Combined q A K B h=h+rightIndexCount q A (K-1) B := by
  have hh : h-1<Count q K B := (lt_count hB).mpr hq
  have hlarge : h≤Count q K B := by omega
  unfold Combined
  rw [min_eq_left hlarge]

theorem maximum_combined_bound {q A K B h lo hi : ℕ} (hB : 0<B) (hK : 0<K) (hH : 0<h)
    (hAK : A≤K) (hlo : lo≤q) (hhi : q≤hi) : Combined q A K B h≤maximum_combined A K B h lo hi := by
  unfold maximum_combined
  by_cases hb : q<Switch K B h
  · have hlow : lo<Switch K B h := by omega
    rw [combined_before hB hK hH hAK hb,if_pos hlow]
    apply le_trans _ (le_max_left _ _)
    apply count_mono hB
    have hs : 0<Switch K B h := by unfold Switch;omega
    omega
  · have hafter : Switch K B h≤q := by omega
    have hhigh : Switch K B h≤hi := by omega
    rw [combined_after hB hH hafter,if_pos hhigh]
    apply le_trans _ (le_max_right _ _)
    have hq : max lo (Switch K B h)≤q := by omega
    exact Nat.add_le_add_left (maximum_bound hB hq hhi) h

theorem ordinary_eq (q B V K : ℕ) :
    HeavyMenu208.OrdinaryCount q B V K=min ((V-1)/B+1) (Count q K B) := by
  unfold HeavyMenu208.OrdinaryCount Count
  split_ifs <;> simp_all

#print axioms combined_before
#print axioms combined_after
#print axioms maximum_combined_bound
end JSP233.CombinedCounts208
