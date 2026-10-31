import Erdos272.Resources.CleanupNet208
import Erdos272.Resources.CleanupWindowBounds208

namespace JSP233.WindowRatio208
open StarCompletion ClippedWindows208 CleanupNet208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

#check Nat.mul_div_cancel
theorem capped_ratio {N low grid w a : ℕ} (hlow : 0<low) (hgrid : 0<grid)
    (hlN : low≤N) (hwa : w≤a) (hwN : w≤N) :
    (w : ℝ)/N≤(Ceil (min a low*grid) low : ℝ)/grid := by
  have hN : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hG : (0 : ℝ)<grid := by exact_mod_cast hgrid
  apply (div_le_div_iff₀ hN hG).mpr
  have hc := le_ceil_mul (a := min a low*grid) hlow
  have hn : w*grid≤Ceil (min a low*grid) low*N := by
    by_cases ha : a≤low
    · rw [min_eq_left ha] at hc ⊢
      exact (Nat.mul_le_mul_right grid hwa).trans
        (hc.trans (Nat.mul_le_mul_left _ hlN))
    · have hm : min a low=low := min_eq_right (by omega)
      rw [hm] at hc ⊢
      have hg : grid≤Ceil (low*grid) low := by
        have hc' : grid*low≤Ceil (low*grid) low*low := by simpa only [Nat.mul_comm low grid] using hc
        have hh := Nat.div_le_div_right (c := low) hc'
        rw [Nat.mul_div_cancel grid hlow,Nat.mul_div_cancel (Ceil (low*grid) low) hlow] at hh
        exact hh
      calc
        w*grid≤N*grid := Nat.mul_le_mul_right grid hwN
        _≤N*Ceil (low*grid) low := Nat.mul_le_mul_left N hg
        _=Ceil (low*grid) low*N := Nat.mul_comm _ _
  exact_mod_cast hn

#print axioms capped_ratio
theorem reciprocal_ratio {N d low grid w count : ℕ} (hd : 0<d) (hlow : 0<low)
    (hgrid : 0<grid) (hlN : low≤N) (hw : w≤count*(N/d+1)) :
    (w : ℝ)/N≤(count*(Ceil grid d+Ceil grid low) : ℝ)/grid := by
  have hN : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hG : (0 : ℝ)<grid := by exact_mod_cast hgrid
  apply (div_le_div_iff₀ hN hG).mpr
  have hc1 := le_ceil_mul (a := grid) hd
  have hc2 := (le_ceil_mul (a := grid) hlow).trans (Nat.mul_le_mul_left (Ceil grid low) hlN)
  have hq := Nat.div_mul_le_self N d
  have hqG : (N/d)*grid≤Ceil grid d*N := by
    calc
      (N/d)*grid≤(N/d)*(Ceil grid d*d) := Nat.mul_le_mul_left (N/d) hc1
      _=Ceil grid d*((N/d)*d) := by ring
      _≤Ceil grid d*N := Nat.mul_le_mul_left (Ceil grid d) hq
  have hs : (N/d+1)*grid≤(Ceil grid d+Ceil grid low)*N := by
    calc
      (N/d+1)*grid=(N/d)*grid+grid := by ring
      _≤Ceil grid d*N+Ceil grid low*N := Nat.add_le_add hqG hc2
      _=(Ceil grid d+Ceil grid low)*N := by ring
  have hn : w*grid≤count*(Ceil grid d+Ceil grid low)*N := by
    calc
      w*grid≤(count*(N/d+1))*grid := Nat.mul_le_mul_right grid hw
      _=count*((N/d+1)*grid) := by ring
      _≤count*((Ceil grid d+Ceil grid low)*N) := Nat.mul_le_mul_left count hs
      _=count*(Ceil grid d+Ceil grid low)*N := by ring
  exact_mod_cast hn

#print axioms reciprocal_ratio
theorem min_ratio {N grid w a b : ℕ}
    (ha : (w : ℝ)/N≤(a : ℝ)/grid) (hb : (w : ℝ)/N≤(b : ℝ)/grid) :
    (w : ℝ)/N≤((min a b : ℕ) : ℝ)/grid := by
  by_cases hab : a≤b
  · simpa only [min_eq_left hab] using ha
  · simpa only [min_eq_right (by omega : b≤a)] using hb

#print axioms min_ratio
theorem window_union_ground {N d B V : ℕ} (H : Finset (ℕ×ℕ)) :
    (H.biUnion (Window N d B V)).card≤N := by
  have hsub : H.biUnion (Window N d B V)⊆Ground N := by
    intro x hx
    obtain ⟨q,hq,hxq⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxq).2
  simpa only [ground_card] using Finset.card_le_card hsub

theorem window_union_count {N d B V : ℕ} (hd : 0<d) (H : Finset (ℕ×ℕ)) :
    (H.biUnion (Window N d B V)).card≤H.card*(N/d+1) := by
  calc
    _≤∑q∈H,(Window N d B V q).card := Finset.card_biUnion_le
    _≤∑_q∈H,(N/d+1) := by
      apply Finset.sum_le_sum
      intro q hq
      have hc := actual_clipped_card (N := N) (B := B) (V := V) hd q
      have hm : min V (N/d-q.2*B+1)≤N/d-q.2*B+1 := min_le_right _ _
      have hh : N/d-q.2*B+1≤N/d+1 := Nat.add_le_add_right (Nat.sub_le (N/d) (q.2*B)) 1
      exact hc.trans (hm.trans hh)
    _=_ := by simp

#print axioms capped_ratio
#print axioms reciprocal_ratio
#print axioms window_union_ground
#print axioms window_union_count
end
end JSP233.WindowRatio208
