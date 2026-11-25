module

public import Erdos272.Geometry.N82427.PhaseDefs82427

@[expose] public section

namespace JSP233.PhaseGeometry82427
open StarCompletion APGeometry NearAP36 ShiftedBlocks208 PotentialPhases208
open PhaseDefs82427 BandLabels208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem phase_floor_bounds {N d x : ℕ} (hd : 0 < d) (hx : x ≤ d) :
    N/d-1 ≤ (N-x)/d ∧ (N-x)/d ≤ N/d := by
  refine ⟨?_, Nat.div_le_div_right (Nat.sub_le N x)⟩
  by_cases hq : N/d=0
  · simp only [hq, Nat.zero_sub, Nat.zero_le]
  · have hcancel : N/d-1+1=N/d :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)
    have hp : (N/d-1)*d+x ≤ N := by
      calc
        _ ≤ (N/d-1)*d+d := Nat.add_le_add_left hx _
        _ = (N/d-1)*d+1*d := by rw [Nat.one_mul]
        _ = (N/d-1+1)*d := (Nat.add_mul _ _ _).symm
        _ = N/d*d := by rw [hcancel]
        _ ≤ N := Nat.div_mul_le_self N d
    exact (Nat.le_div_iff_mul_le hd).mpr (Nat.le_sub_of_add_le hp)

theorem actual_source_cap {N a d m e E B : ℕ} {S : Finset ℤ}
    (hd : 0 < d) (hB : 0 < B) (hm : 0 < m) (he : e < E)
    (hcard : S.card=m+e) (hsub : Grid a d m ⊆ S) (hground : S ⊆ Ground N) :
    (Code d B a).2*B ≤ (N-((Code d B a).1+1))/d ∧
      S.card ≤ (N-((Code d B a).1+1))/d-(Code d B a).2*B+E := by
  have haS : (a : ℤ) ∈ S := hsub ((mem_grid _ _ _ _).mpr ⟨0, hm, by simp⟩)
  have ha0 : 1 ≤ a := by exact_mod_cast ((mem_ground N (a : ℤ)).mp (hground haS)).1
  obtain ⟨i, hi, ha⟩ := code_decomposition (d := d) ha0 hB
  have hxS := hsub ((mem_grid _ _ _ _).mpr ⟨m-1, by omega, rfl⟩)
  have hxZ := ((mem_ground N ((a : ℤ)+((m-1 : ℕ) : ℤ)*d)).mp (hground hxS)).2
  have hx : a+(m-1)*d ≤ N := by exact_mod_cast hxZ
  have hsum : ((Code d B a).2*B+(m-1))*d+((Code d B a).1+1) ≤ N := by
    nlinarith only [hx, ha]
  have hp := (Nat.le_div_iff_mul_le hd).mpr (Nat.le_sub_of_add_le hsum)
  exact ⟨by omega, by omega⟩

theorem clipped_card {N d B V : ℕ} (hd : 0 < d) (q : ℕ × ℕ) :
    (ClippedWindows208.Window N d B V q).card ≤
      min V ((N-(q.1+1))/d-q.2*B+1) := by
  let C := min V ((N-(q.1+1))/d-q.2*B+1)
  have hsub : ClippedWindows208.Window N d B V q ⊆ Grid (q.1+1+q.2*B*d) d C := by
    intro x hx
    obtain ⟨hxW, hxN⟩ := Finset.mem_inter.mp hx
    rw [ClippedWindows208.shifted_window_grid] at hxW
    obtain ⟨i, hi, he⟩ := (mem_grid _ _ _ _).mp hxW
    have hxN' := ((mem_ground N x).mp hxN).2
    have heN : q.1+1+q.2*B*d+i*d ≤ N := by
      have heZ : ((q.1+1+q.2*B*d+i*d : ℕ) : ℤ) ≤ N := by
        push_cast at he ⊢
        linarith only [he, hxN']
      exact_mod_cast heZ
    have hsum : (q.2*B+i)*d+(q.1+1) ≤ N := by nlinarith only [heN]
    have hdiv := (Nat.le_div_iff_mul_le hd).mpr (Nat.le_sub_of_add_le hsum)
    apply (mem_grid _ _ _ _).mpr
    exact ⟨i, by dsimp only [C]; omega, he⟩
  have hc := Finset.card_le_card hsub
  simpa only [grid_card _ _ _ hd] using hc

theorem cap_window {N d E B V : ℕ} (hd : 0 < d) (hE : 1 ≤ E) (q : ℕ × ℕ) :
    (ClippedWindows208.Window N d B V q).card ≤ Cap N d E B V (Swap q) := by
  apply (clipped_card hd q).trans
  dsimp only [Cap, Swap]
  exact min_le_min_left V (by omega)

theorem same_block_window_cap {N d E B V : ℕ} {q t : ℕ × ℕ}
    (hd : 0 < d) (hE : 2 ≤ E) (hq : q.1 < d) (ht : t.1 < d)
    (hr : q.2=t.2) :
    (ClippedWindows208.Window N d B V q).card ≤ Cap N d E B V (Swap t) := by
  have hw := clipped_card (N := N) (B := B) (V := V) hd q
  have hqv := phase_floor_bounds (N := N) hd (by omega : q.1+1 ≤ d)
  have htv := phase_floor_bounds (N := N) hd (by omega : t.1+1 ≤ d)
  dsimp only [Cap, Swap]
  rw [hr] at hw
  omega

theorem ordinary_cap {N d E B V : ℕ} {q : ℕ × ℕ}
    (hd : 0 < d) (hq : q.1 < d) (hEV : E ≤ V)
    (ho : V-E+q.2*B ≤ N/d) :
    V-1 ≤ Cap N d E B V (Swap q) := by
  have hp := phase_floor_bounds (N := N) hd (by omega : q.1+1 ≤ d)
  dsimp only [Cap, Swap]
  omega

theorem unsaturated_window {N d E B V : ℕ} {q : ℕ × ℕ}
    (hd : 0 < d) (hE : 1 ≤ E)
    (hlt : Cap N d E B V (Swap q) < V) :
    (ClippedWindows208.Window N d B V q).card+E ≤ Cap N d E B V (Swap q)+1 := by
  have hw := clipped_card (N := N) (B := B) (V := V) hd q
  dsimp only [Cap, Swap] at hlt ⊢
  omega

#print axioms phase_floor_bounds
#print axioms actual_source_cap
#print axioms clipped_card
#print axioms cap_window
#print axioms same_block_window_cap
#print axioms ordinary_cap
#print axioms unsaturated_window
end
end JSP233.PhaseGeometry82427
