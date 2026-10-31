import Erdos272.Resources.ClippedWindows208

namespace JSP233.OrdinaryUnion208
open StarCompletion APGeometry NearAP36 ClippedWindows208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_union_window_bound {N d B V : ℕ} {H : Finset (ℕ × ℕ)}
    (hd : 0 < d) (hB : 0 < B) (hV : 0 < V)
    (hres : ∀ q ∈ H, q.1 < d)
    (hpair : ∀ q ∈ H, ∀ r ∈ H,
      (Window N d B V q ∩ Window N d B V r).Nonempty) :
    (H.biUnion (Window N d B V)).card ≤ min (V+(V-1)/B*B) (N/d+1) := by
  rcases H.eq_empty_or_nonempty with he | hne
  · subst H; simp
  obtain ⟨q0,hq0,hmin⟩ := Finset.exists_min_image H Prod.snd hne
  have hspan : ∀ q ∈ H, q.1=q0.1 ∧ q0.2 ≤ q.2 ∧ q.2 ≤ q0.2+(V-1)/B := by
    intro q hq
    obtain ⟨x,hx⟩ := hpair q hq q0 hq0
    obtain ⟨hxq,hx0⟩ := Finset.mem_inter.mp hx
    have hqW := (ShiftedWindows208.mem_window _ _ _ _ _).mp (Finset.mem_inter.mp hxq).1
    have h0W := (ShiftedWindows208.mem_window _ _ _ _ _).mp (Finset.mem_inter.mp hx0).1
    have hh := HeavyWindows208.window_code_overlap hd (hres q hq) (hres q0 hq0)
      ⟨x-1,Finset.mem_inter.mpr ⟨hqW,h0W⟩⟩
    have hlo := hmin q hq
    have hdiff : (q.2-q0.2)*B ≤ V-1 := by
      have he : (q.2-q0.2)*B+q0.2*B=q.2*B := by rw [←Nat.add_mul,Nat.sub_add_cancel hlo]
      omega
    have hdiv := (Nat.le_div_iff_mul_le hB).mpr hdiff
    exact ⟨hh.1,hlo,by omega⟩
  let U := V+(V-1)/B*B
  have hsub : H.biUnion (Window N d B V) ⊆ Window N d B U q0 := by
    intro x hx
    obtain ⟨q,hq,hxq⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hxqW,hxN⟩ := Finset.mem_inter.mp hxq
    rw [shifted_window_grid] at hxqW
    obtain ⟨i,hi,he⟩ := (mem_grid _ _ _ _).mp hxqW
    have hh := hspan q hq
    have hdiff : q.2-q0.2 ≤ (V-1)/B := by omega
    have hmul := Nat.mul_le_mul_right B hdiff
    have hadd : q.2-q0.2+q0.2=q.2 := Nat.sub_add_cancel hh.2.1
    have haddZ : ((q.2-q0.2 : ℕ) : ℤ)+q0.2=q.2 := by exact_mod_cast hadd
    apply Finset.mem_inter.mpr
    refine ⟨?_,hxN⟩
    rw [shifted_window_grid]
    apply (mem_grid _ _ _ _).mpr
    refine ⟨(q.2-q0.2)*B+i,by dsimp [U]; omega,?_⟩
    rw [hh.1] at he
    push_cast at he ⊢
    rw [←haddZ] at he
    nlinarith only [he]
  have hc := (Finset.card_le_card hsub).trans (actual_clipped_card hd q0)
  exact hc.trans (min_le_min_left U (Nat.add_le_add_right (Nat.sub_le (N/d) (q0.2*B)) 1))

#print axioms actual_union_window_bound
end
end JSP233.OrdinaryUnion208
