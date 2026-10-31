import Erdos272.Resources.MaximumCore208

namespace JSP233.HeavyWindows208
open StarCompletion APGeometry NearAP36 SourceBridge208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Window (d B V : ℕ) (q : ℕ × ℕ) : Finset ℤ :=
  Grid (q.1+q.2*B*d) d V

theorem core_in_window {a d m B V : ℕ} (hB : 0 < B) (hlen : m+B-1 ≤ V) :
    Grid a d m ⊆ Window d B V (StartCode d B a) := by
  obtain ⟨i,hi,ha⟩ := start_decomposition (a := a) (d := d) hB
  intro x hx
  obtain ⟨j,hj,hx⟩ := (mem_grid _ _ _ _).mp hx
  apply (mem_grid _ _ _ _).mpr
  refine ⟨i+j, by omega, ?_⟩
  have haZ : (a : ℤ) = (StartCode d B a).1 +
      ((StartCode d B a).2*(B : ℤ)+i)*d := by exact_mod_cast ha
  push_cast
  nlinarith only [haZ,hx]

theorem window_card {d B V : ℕ} (hd : 0 < d) (q : ℕ × ℕ) :
    (Window d B V q).card = V := grid_card _ _ _ hd

theorem window_code_overlap {d B V : ℕ} {q r : ℕ × ℕ}
    (hd : 0 < d) (hq : q.1 < d) (hr : r.1 < d)
    (hint : (Window d B V q ∩ Window d B V r).Nonempty) :
    q.1 = r.1 ∧ q.2*B < r.2*B+V ∧ r.2*B < q.2*B+V := by
  obtain ⟨x,hx⟩ := hint
  obtain ⟨hxq,hxr⟩ := Finset.mem_inter.mp hx
  obtain ⟨i,hi,hix⟩ := (mem_grid _ _ _ _).mp hxq
  obtain ⟨j,hj,hjx⟩ := (mem_grid _ _ _ _).mp hxr
  have he : q.1+q.2*B*d+i*d = r.1+r.2*B*d+j*d := by
    have heZ : ((q.1+q.2*B*d+i*d : ℕ) : ℤ) = (r.1+r.2*B*d+j*d : ℕ) := by
      push_cast
      exact hix.symm.trans hjx
    exact_mod_cast heZ
  have hres : q.1=r.1 := by
    have hh := congrArg (fun n => n%d) he
    simpa only [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hq,Nat.mod_eq_of_lt hr] using hh
  have he' : q.2*B+i = r.2*B+j := by rw [hres] at he; nlinarith only [he,hd]
  exact ⟨hres,by omega,by omega⟩

theorem pairwise_window_census {d B V : ℕ} {H : Finset (ℕ × ℕ)}
    (hd : 0 < d) (hB : 0 < B) (hV : 0 < V)
    (hres : ∀ q ∈ H, q.1 < d)
    (hpair : ∀ q ∈ H, ∀ r ∈ H, (Window d B V q ∩ Window d B V r).Nonempty) :
    H.card ≤ (V-1)/B+1 := by
  rcases H.eq_empty_or_nonempty with he | hne
  · subst H; simp
  obtain ⟨q0,hq0,hmin⟩ := Finset.exists_min_image H Prod.snd hne
  have hbounds : ∀ q ∈ H, q.1=q0.1 ∧ q0.2 ≤ q.2 ∧ q.2 ≤ q0.2+(V-1)/B := by
    intro q hq
    have hh := window_code_overlap hd (hres q hq) (hres q0 hq0) (hpair q hq q0 hq0)
    have hlo := hmin q hq
    have hdiff : (q.2-q0.2)*B ≤ V-1 := by
      have he : (q.2-q0.2)*B+q0.2*B=q.2*B := by
        rw [← Nat.add_mul,Nat.sub_add_cancel hlo]
      omega
    have hdv := (Nat.le_div_iff_mul_le hB).mpr hdiff
    exact ⟨hh.1,hlo,by omega⟩
  have hmaps : Set.MapsTo Prod.snd (H : Set (ℕ × ℕ))
      (Finset.Icc q0.2 (q0.2+(V-1)/B) : Set ℕ) := by
    intro q hq
    exact Finset.mem_Icc.mpr (hbounds q hq).2
  have hinj : Set.InjOn Prod.snd (H : Set (ℕ × ℕ)) := by
    intro q hq r hr he
    exact Prod.ext ((hbounds q hq).1.trans (hbounds r hr).1.symm) he
  have hc := Finset.card_le_card_of_injOn Prod.snd hmaps hinj
  rw [Nat.card_Icc] at hc
  simpa only [Nat.add_assoc,Nat.add_sub_cancel_left] using hc

theorem actual_heavy_windows_intersect {d B V : ℕ} {H : Finset (ℕ × ℕ)}
    (hd : 0 < d) (family : (ℕ × ℕ) → Finset (Finset ℤ)) (core : Finset ℤ → Finset ℤ)
    (hcore : ∀ q ∈ H, ∀ S ∈ family q, core S ⊆ Window d B V q)
    (hdis : ∀ q ∈ H, ∀ S ∈ family q, ∀ T ∈ family q, S ≠ T →
      Disjoint (S \ core S) (T \ core T))
    (hcross : ∀ q ∈ H, ∀ r ∈ H, ∀ S ∈ family q, ∀ T ∈ family r, (S ∩ T).Nonempty)
    (hsmall : ∀ q ∈ H, ∀ S ∈ family q, S.card ≤ V)
    (hheavy : ∀ q ∈ H, V < (family q).card) :
    ∀ q ∈ H, ∀ r ∈ H, (Window d B V q ∩ Window d B V r).Nonempty := by
  intro q hq r hr
  exact heavy_core_pools_intersect core (hcore q hq) (hcore r hr) (hdis q hq) (hdis r hr)
    (hcross q hq r hr) (hsmall r hr) (hheavy q hq)
    (by simpa only [window_card hd] using hheavy r hr)

#print axioms core_in_window
#print axioms pairwise_window_census
#print axioms actual_heavy_windows_intersect
end
end JSP233.HeavyWindows208
