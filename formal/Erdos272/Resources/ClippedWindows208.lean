module

public import Erdos272.Resources.ShiftedWindows208

@[expose] public section

namespace JSP233.ClippedWindows208
open StarCompletion APGeometry NearAP36 ShiftedBlocks208 PotentialPhases208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Window (N d B V : ℕ) (q : ℕ × ℕ) : Finset ℤ :=
  ShiftedWindows208.Window d B V q ∩ Ground N

theorem shifted_window_grid (d B V : ℕ) (q : ℕ × ℕ) :
    ShiftedWindows208.Window d B V q = Grid (q.1+1+q.2*B*d) d V := by
  ext x
  rw [ShiftedWindows208.mem_window]
  simp only [HeavyWindows208.Window,mem_grid]
  constructor
  · rintro ⟨i,hi,he⟩
    refine ⟨i,hi,?_⟩
    push_cast at he ⊢
    linarith only [he]
  · rintro ⟨i,hi,he⟩
    refine ⟨i,hi,?_⟩
    push_cast at he ⊢
    linarith only [he]

theorem actual_clipped_card {N d B V : ℕ} (hd : 0 < d) (q : ℕ × ℕ) :
    (Window N d B V q).card ≤ min V (N/d-q.2*B+1) := by
  let C := min V (N/d-q.2*B+1)
  have hsub : Window N d B V q ⊆ Grid (q.1+1+q.2*B*d) d C := by
    intro x hx
    obtain ⟨hxW,hxN⟩ := Finset.mem_inter.mp hx
    rw [shifted_window_grid] at hxW
    obtain ⟨i,hi,he⟩ := (mem_grid _ _ _ _).mp hxW
    have hxN' := ((mem_ground N x).mp hxN).2
    have heN : q.1+1+q.2*B*d+i*d ≤ N := by
      have heZ : ((q.1+1+q.2*B*d+i*d : ℕ) : ℤ) ≤ N := by
        push_cast at he ⊢
        linarith only [he,hxN']
      exact_mod_cast heZ
    have hprod : (q.2*B+i)*d ≤ N := by nlinarith only [heN]
    have hdv := (Nat.le_div_iff_mul_le hd).mpr hprod
    apply (mem_grid _ _ _ _).mpr
    exact ⟨i,by dsimp [C]; omega,he⟩
  have hc := Finset.card_le_card hsub
  simpa only [grid_card _ _ _ hd] using hc

theorem actual_clipped_threshold {N d B V E : ℕ} (hd : 0 < d) (hE : 1 ≤ E) (q : ℕ × ℕ) :
    (Window N d B V q).card ≤ min V (N/d-q.2*B+E) := by
  apply le_trans (actual_clipped_card hd q)
  exact min_le_min_left V (by omega)

theorem fixed_block_window_eq {N d B V r : ℕ} {q t : ℕ × ℕ}
    (hd : 0 < d) (hq : q.1 < d) (ht : t.1 < d) (hqr : q.2=r) (htr : t.2=r)
    (hint : (Window N d B V q ∩ Window N d B V t).Nonempty) : q=t := by
  obtain ⟨x,hx⟩ := hint
  obtain ⟨hxq,hxt⟩ := Finset.mem_inter.mp hx
  have hqW := (ShiftedWindows208.mem_window _ _ _ _ _).mp (Finset.mem_inter.mp hxq).1
  have htW := (ShiftedWindows208.mem_window _ _ _ _ _).mp (Finset.mem_inter.mp hxt).1
  have hres := (HeavyWindows208.window_code_overlap hd hq ht
    ⟨x-1,Finset.mem_inter.mpr ⟨hqW,htW⟩⟩).1
  exact Prod.ext hres (hqr.trans htr.symm)

theorem actual_right_group_census {N d B V r W : ℕ} {H : Finset (ℕ × ℕ)}
    (hd : 0 < d) (family : (ℕ × ℕ) → Finset (Finset ℤ)) (core : Finset ℤ → Finset ℤ)
    (hres : ∀ q ∈ H, q.1 < d) (hblock : ∀ q ∈ H, q.2=r)
    (hcore : ∀ q ∈ H, ∀ S ∈ family q, core S ⊆ Window N d B V q)
    (hdis : ∀ q ∈ H, ∀ S ∈ family q, ∀ T ∈ family q, S ≠ T →
      Disjoint (S \ core S) (T \ core T))
    (hcross : ∀ q ∈ H, ∀ t ∈ H, ∀ S ∈ family q, ∀ T ∈ family t, (S ∩ T).Nonempty)
    (hsmall : ∀ q ∈ H, ∀ S ∈ family q, S.card ≤ W)
    (hwindow : ∀ q ∈ H, (Window N d B V q).card ≤ W)
    (hheavy : ∀ q ∈ H, W < (family q).card) : H.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q hq t ht
  have hint := heavy_core_pools_intersect core (hcore q hq) (hcore t ht)
    (hdis q hq) (hdis t ht) (hcross q hq t ht) (hsmall t ht) (hheavy q hq)
    ((hwindow q hq).trans_lt (hheavy t ht))
  exact fixed_block_window_eq hd (hres q hq) (hres t ht) (hblock q hq) (hblock t ht) hint

#print axioms actual_clipped_card
#print axioms actual_clipped_threshold
#print axioms actual_right_group_census
end
end JSP233.ClippedWindows208
