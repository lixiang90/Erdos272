import Erdos272.Arithmetic.CombinedCounts208
import Erdos272.Arithmetic.WindowSums208
import Erdos272.Resources.BandSystem208

namespace JSP233.CleanupWindowBounds208
open StarCompletion APGeometry NearAP36 LightClosed208 WindowCounts208 WindowSums208 CombinedCounts208
open scoped BigOperators
set_option maxHeartbeats 0

theorem actual_window_bounds {N d A B V E lo hi : ℕ} {H : Finset (ℕ × ℕ)}
    (hprop : BandSystem208.Properties N d A B V E H)
    (hd : 0<d) (hB : 0<B) (hV : 0<V) (hEV : E<V) (hAJ : A≤V-E-1)
    (hlo : lo≤N/d) (hhi : N/d≤hi) :
    H.card≤maximum_combined A (V-E) B ((V-1)/B+1) lo hi ∧
      (H.biUnion (ClippedWindows208.Window N d B V)).card≤
        HeavyMenu208.OrdinaryUnion (N/d) B V (V-E)+maximum_sum A (V-E-1) B lo hi := by
  by_cases hAq : A≤N/d
  · have hm := HeavyMenu208.actual_menu hd hB hV hEV hAq
      hprop.residue hprop.feasible hprop.injective hprop.ordinary_pair
    have hc : H.card≤Combined (N/d) A (V-E) B ((V-1)/B+1) := by
      have hh := hm.1
      change H.card≤HeavyMenu208.OrdinaryCount (N/d) B V (V-E)+
        ((N/d-A)/B+1-RightLeft (N/d) (V-E-1) B) at hh
      have he : ((N/d-A)/B+1-RightLeft (N/d) (V-E-1) B)=rightIndexCount (N/d) A (V-E-1) B := by
        simp only [rightIndexCount,Count,if_pos hAq]
      rw [he,ordinary_eq] at hh
      exact hh
    refine ⟨hc.trans (maximum_combined_bound hB (by omega : 0<V-E) (Nat.zero_lt_succ ((V-1)/B))
      (by omega : A≤V-E) hlo hhi),?_⟩
    have hu := hm.2
    have hs := actual_Icc_sum_bound (q:=N/d) (A:=A) (J:=V-E-1) (B:=B) (V:=V) hB hAJ hAq hlo hhi
    exact hu.trans (Nat.add_le_add_left hs _)
  · have he := HeavyMenu208.actual_extinction hprop.feasible (by omega : N/d<A)
    subst H
    simp

#print axioms actual_window_bounds
end JSP233.CleanupWindowBounds208
