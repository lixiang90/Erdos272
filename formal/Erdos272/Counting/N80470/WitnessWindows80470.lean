module

public import Erdos272.Resources.N80470.WitnessCredit80470
public import Erdos272.Resources.ClippedWindows208

@[expose] public section

namespace JSP233.WitnessWindows80470
open StarCompletion APGeometry
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def FeasibleCount (Q A B : ℕ) : ℕ := if A≤Q then (Q-A)/B+1 else 0

theorem actual_point_window_count {N d B V Q A : ℕ} {I : Finset (ℕ×ℕ)}
    (hd : 0<d) (hB : 0<B) (hV : 0<V)
    (hres : ∀ q∈I, q.1<d) (hfeasible : ∀ q∈I, A+q.2*B≤Q) (x : ℤ) :
    (I.filter (fun q => x∈ClippedWindows208.Window N d B V q)).card≤
      min ((V-1)/B+1) (FeasibleCount Q A B) := by
  let H := I.filter (fun q => x∈ClippedWindows208.Window N d B V q)
  have hHI : H⊆I := Finset.filter_subset _ _
  have hx : ∀ q∈H, x∈ClippedWindows208.Window N d B V q :=
    fun q hq => (Finset.mem_filter.mp hq).2
  apply le_min
  · apply ShiftedWindows208.pairwise_window_census hd hB hV
      (fun q hq => hres q (hHI hq))
    intro q hq r hr
    exact ⟨x,Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (hx q hq)).1,(Finset.mem_inter.mp (hx r hr)).1⟩⟩
  · by_cases hAQ : A≤Q
    · have hmaps : Set.MapsTo Prod.snd (H : Set (ℕ×ℕ))
          (Finset.range ((Q-A)/B+1) : Set ℕ) := by
        intro q hq
        have hh := hfeasible q (hHI hq)
        have hmul : q.2*B≤Q-A := by omega
        have hdiv := (Nat.le_div_iff_mul_le hB).mpr hmul
        exact Finset.mem_range.mpr (by omega)
      have hinj : Set.InjOn Prod.snd (H : Set (ℕ×ℕ)) := by
        intro q hq r hr he
        exact ClippedWindows208.fixed_block_window_eq hd
          (hres q (hHI hq)) (hres r (hHI hr)) rfl he.symm
          ⟨x,Finset.mem_inter.mpr ⟨hx q hq,hx r hr⟩⟩
      have hc := Finset.card_le_card_of_injOn Prod.snd hmaps hinj
      simpa only [FeasibleCount,if_pos hAQ,Finset.card_range] using hc
    · have hH : H=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        have hh := hfeasible q (hHI hq)
        omega
      change H.card ≤ FeasibleCount Q A B
      simp only [hH,Finset.card_empty,FeasibleCount,if_neg hAQ,le_refl]

theorem actual_witness_window_count {N d B V Q A W : ℕ}
    {I : Finset (ℕ×ℕ)} {A₀ : Finset ℤ}
    (hd : 0<d) (hB : 0<B) (hV : 0<V)
    (hres : ∀ q∈I, q.1<d) (hfeasible : ∀ q∈I, A+q.2*B≤Q)
    (hcard : A₀.card≤W) :
    (I.filter (fun q => ((ClippedWindows208.Window N d B V q)∩A₀).Nonempty)).card≤
      W*min ((V-1)/B+1) (FeasibleCount Q A B) := by
  apply WitnessCredit80470.hitting_windows_card I (ClippedWindows208.Window N d B V) A₀
    W (min ((V-1)/B+1) (FeasibleCount Q A B)) hcard
  intro x _hx
  exact actual_point_window_count hd hB hV hres hfeasible x

#print axioms actual_point_window_count
#print axioms actual_witness_window_count
end
end JSP233.WitnessWindows80470
