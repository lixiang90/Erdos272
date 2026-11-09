module

public import Erdos272.Core.N200000.ActualRun200000
public import Erdos272.Core.N200000.CoreCeil200000

@[expose] public section

/-! A finer actual run meets a coarser core in one index interval. The
same interval can be padded once before any prime pair counts are taken. -/
namespace JSP233.RunTrace200000
open StarCompletion APGeometry SourceBridge208 ActualRun200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Trace (a : ℕ) (p d : ℤ) (R : Finset ℤ) : Finset ℕ :=
  (Finset.range a).filter (fun i => p + d * (i : ℤ) ∈ R)

theorem coarse_subAP_card {I R : Finset ℤ} {d p g x : ℤ} {a h : ℕ}
    (hI : APAt d p I) (hR : APAt g x R) (hIR : I ⊆ R) (hcard : R.card ≤ a)
    (hh : 0 < h) (hd : d = (h : ℤ) * g) : I.card ≤ (a + h - 1) / h := by
  rcases I.eq_empty_or_nonempty with hzero | hne
  · simp only [hzero, Finset.card_empty, Nat.zero_le]
  have hRne := hne.mono hIR
  have hIpos := Finset.card_pos.mpr hne
  have hRpos := Finset.card_pos.mpr hRne
  have hapos : 0 < a := by omega
  have hmin := Finset.min'_le R (I.min' hne) (hIR (Finset.min'_mem I hne))
  have hmax := Finset.le_max' R (I.max' hne) (hIR (Finset.max'_mem I hne))
  have hspanI := apAt_span_eq hI hne
  have hspanR := apAt_span_eq hR hRne
  have hspan : d * ((I.card : ℤ) - 1) ≤ g * ((R.card : ℤ) - 1) := by omega
  have hcancel : (h : ℤ) * ((I.card : ℤ) - 1) ≤ (R.card : ℤ) - 1 := by
    apply (mul_le_mul_iff_left₀ hR.1).mp
    rw [hd] at hspan
    nlinarith only [hspan]
  have hIcast : ((I.card - 1 : ℕ) : ℤ) = (I.card : ℤ) - 1 := by omega
  have hacast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
  have hprodZ : (((I.card - 1) * h : ℕ) : ℤ) ≤ ((a - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_mul, hIcast, hacast]
    have hcardZ : (R.card : ℤ) ≤ a := by exact_mod_cast hcard
    nlinarith only [hcancel, hcardZ]
  have hprod : (I.card - 1) * h ≤ a - 1 := by exact_mod_cast hprodZ
  have hdiv := (Nat.le_div_iff_mul_le hh).mpr hprod
  rw [← CoreCeil200000.ceil_count hapos hh]
  omega

theorem actual_run_core_card {S P : Finset ℤ} {d p g x : ℤ} {a h : ℕ}
    (hP : APAt d p P) (hg : 0 < g) (hx : x ∈ S) (hmax : MaxAPSize S ≤ a)
    (hh : 0 < h) (hd : d = (h : ℤ) * g) (hgp : g ∣ p - x) :
    (P ∩ Run S g x).card ≤ (a + h - 1) / h := by
  have hgd : g ∣ d := ⟨h, by nlinarith only [hd]⟩
  exact coarse_subAP_card (intersection_coarser_at hP (run_at hg hx) hgd hgp)
    (run_at hg hx) Finset.inter_subset_right ((run_card hg hx).trans hmax) hh hd

theorem trace_card_eq (a : ℕ) {p d : ℤ} (hd : 0 < d) (R : Finset ℤ) :
    (Trace a p d R).card = (((Finset.range a).image (fun i : ℕ => p + d * (i : ℤ))) ∩ R).card := by
  have hinj : Function.Injective (fun i : ℕ => p + d * (i : ℤ)) := by
    intro i j he
    have hij : (i : ℤ) = j := by nlinarith
    exact_mod_cast hij
  rw [← Finset.card_image_of_injective (Trace a p d R) hinj]
  congr 1
  ext y
  simp only [Trace, Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨i, ⟨hi, hRi⟩, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, hRi⟩
  · rintro ⟨⟨i, hi, rfl⟩, hRi⟩
    exact ⟨i, ⟨hi, hRi⟩, rfl⟩

theorem trace_between {a : ℕ} {p d g x : ℤ} {R : Finset ℤ}
    (hd : 0 < d) (hR : APAt g x R) (hgd : g ∣ d) {i j k : ℕ}
    (hi : i ∈ Trace a p d R) (hk : k ∈ Trace a p d R) (hij : i ≤ j) (hjk : j ≤ k) :
    j ∈ Trace a p d R := by
  obtain ⟨_hiA, hiR⟩ := Finset.mem_filter.mp hi
  obtain ⟨hkA, hkR⟩ := Finset.mem_filter.mp hk
  have hjA : j < a := by have := Finset.mem_range.mp hkA; omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr hjA, apAt_fill hR hiR hkR ?_ ?_ ?_⟩
  · have hZ : (i : ℤ) ≤ j := by exact_mod_cast hij
    nlinarith only [hd, hZ]
  · have hZ : (j : ℤ) ≤ k := by exact_mod_cast hjk
    nlinarith only [hd, hZ]
  · rw [show (p + d * (j : ℤ)) - (p + d * (i : ℤ)) = d * ((j : ℤ) - i) by ring]
    exact dvd_mul_of_dvd_left hgd _

theorem finite_interval_of_between {K : Finset ℕ} {a : ℕ} (hK : K ⊆ Finset.range a)
    (hbetween : ∀ i ∈ K, ∀ k ∈ K, ∀ j, i ≤ j → j ≤ k → j ∈ K) :
    ∃ l n : ℕ, l + n ≤ a ∧ K = Finset.Ico l (l + n) := by
  rcases K.eq_empty_or_nonempty with hzero | hne
  · exact ⟨0, 0, by omega, by simp [hzero]⟩
  let l := K.min' hne
  let u := K.max' hne
  have hlK : l ∈ K := Finset.min'_mem _ hne
  have huK : u ∈ K := Finset.max'_mem _ hne
  have hlu : l ≤ u := Finset.min'_le K u huK
  have hua : u < a := Finset.mem_range.mp (hK huK)
  have he : l + (u + 1 - l) = u + 1 := by omega
  refine ⟨l, u + 1 - l, by omega, ?_⟩
  rw [he]
  ext j
  constructor
  · intro hj
    have hl := Finset.min'_le K j hj
    have hu := Finset.le_max' K j hj
    exact Finset.mem_Ico.mpr ⟨hl, by omega⟩
  · intro hj
    obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp hj
    exact hbetween l hlK u huK j hl (by omega)

theorem pad_same_interval {K : Finset ℕ} {a b : ℕ} (hK : K ⊆ Finset.range a)
    (hbetween : ∀ i ∈ K, ∀ k ∈ K, ∀ j, i ≤ j → j ≤ k → j ∈ K)
    (hcard : K.card ≤ b) (hb : b ≤ a) :
    ∃ l : ℕ, l + b ≤ a ∧ K ⊆ Finset.Ico l (l + b) := by
  obtain ⟨l, n, hla, he⟩ := finite_interval_of_between hK hbetween
  have hn : n ≤ b := by simpa only [he, Nat.card_Ico, Nat.add_sub_cancel_left] using hcard
  let t := min l (a - b)
  have htla : t + b ≤ a := by dsimp only [t]; omega
  refine ⟨t, htla, ?_⟩
  intro j hj
  rw [he] at hj
  obtain ⟨hlj, hjn⟩ := Finset.mem_Ico.mp hj
  apply Finset.mem_Ico.mpr
  dsimp only [t]
  omega

#print axioms coarse_subAP_card
#print axioms actual_run_core_card
#print axioms trace_card_eq
#print axioms trace_between
#print axioms finite_interval_of_between
#print axioms pad_same_interval
end
end JSP233.RunTrace200000
