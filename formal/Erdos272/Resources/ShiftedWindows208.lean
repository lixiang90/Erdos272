module

public import Erdos272.Resources.HeavyWindows208
public import Erdos272.Counting.PotentialPhases208

@[expose] public section

namespace JSP233.ShiftedWindows208
open StarCompletion APGeometry NearAP36 PotentialPhases208 ShiftedBlocks208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Window (d B V : ℕ) (q : ℕ × ℕ) : Finset ℤ :=
  (HeavyWindows208.Window d B V q).image (fun x => x+1)

theorem mem_window (d B V : ℕ) (q : ℕ × ℕ) (x : ℤ) :
    x ∈ Window d B V q ↔ x-1 ∈ HeavyWindows208.Window d B V q := by
  simp only [Window,Finset.mem_image]
  constructor
  · rintro ⟨y,hy,he⟩
    have hh : x-1=y := by omega
    simpa only [hh] using hy
  · intro hx
    exact ⟨x-1,hx,by omega⟩

theorem window_card {d B V : ℕ} (hd : 0 < d) (q : ℕ × ℕ) :
    (Window d B V q).card=V := by
  rw [Window,Finset.card_image_of_injective]
  · exact HeavyWindows208.window_card hd q
  · intro x y he
    change x+1=y+1 at he
    omega

theorem core_in_window {a d m B V : ℕ} (ha0 : 1 ≤ a) (hB : 0 < B)
    (hlen : m+B-1 ≤ V) : Grid a d m ⊆ Window d B V (Code d B a) := by
  obtain ⟨i,hi,ha⟩ := code_decomposition (d := d) ha0 hB
  intro x hx
  obtain ⟨j,hj,hx⟩ := (mem_grid _ _ _ _).mp hx
  apply (mem_window _ _ _ _ _).mpr
  apply (mem_grid _ _ _ _).mpr
  refine ⟨i+j, by omega, ?_⟩
  have haZ : (a : ℤ) = (Code d B a).1+1+((Code d B a).2*(B : ℤ)+i)*d := by
    exact_mod_cast ha
  push_cast
  nlinarith only [haZ,hx]

theorem pairwise_window_census {d B V : ℕ} {H : Finset (ℕ × ℕ)}
    (hd : 0 < d) (hB : 0 < B) (hV : 0 < V)
    (hres : ∀ q ∈ H, q.1 < d)
    (hpair : ∀ q ∈ H, ∀ r ∈ H, (Window d B V q ∩ Window d B V r).Nonempty) :
    H.card ≤ (V-1)/B+1 := by
  apply HeavyWindows208.pairwise_window_census hd hB hV hres
  intro q hq r hr
  obtain ⟨x,hx⟩ := hpair q hq r hr
  exact ⟨x-1,Finset.mem_inter.mpr ⟨(mem_window _ _ _ _ _).mp (Finset.mem_inter.mp hx).1,
    (mem_window _ _ _ _ _).mp (Finset.mem_inter.mp hx).2⟩⟩

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
end JSP233.ShiftedWindows208
