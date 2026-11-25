module

public import Erdos272.Counting.APCount41

@[expose] public section

namespace JSP233.ResidueCard88404
open StarCompletion APGeometry
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def ShortPhase (M q : ℕ) (r : ℤ) : Finset ℤ :=
  (Finset.Icc 1 ((M : ℤ)-q)).filter (fun x => (q : ℤ) ∣ x-r)

theorem short_phase_card {M q : ℕ} {r : ℤ} (hq : 0 < q) :
    (q : ℝ)*((ShortPhase M q r).card : ℝ) ≤ M := by
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  by_cases hne : (ShortPhase M q r).Nonempty
  · have hAP : APAt (q : ℤ) r (ShortPhase M q r) := by
      refine ⟨hqZ, 1, (M : ℤ)-q, ?_⟩
      intro x
      simp only [ShortPhase, Finset.mem_filter, Finset.mem_Icc, and_assoc]
    have ha := Finset.mem_Icc.mp (Finset.mem_filter.mp
      (Finset.min'_mem (ShortPhase M q r) hne)).1
    have hb := Finset.mem_Icc.mp (Finset.mem_filter.mp
      (Finset.max'_mem (ShortPhase M q r) hne)).1
    have hs := apAt_span_eq hAP hne
    have hz : (q : ℤ)*((ShortPhase M q r).card : ℤ) ≤ M := by
      nlinarith only [ha.1, hb.2, hs]
    exact_mod_cast hz
  · have he : ShortPhase M q r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he, Finset.card_empty, Nat.cast_zero, mul_zero]
    positivity

theorem gap_eq_step {q x : ℤ} (hq : 0 < q) (hx : 0 < x) (hxq : x < 2*q)
    (hd : q ∣ x) : x = q := by
  obtain ⟨k, hk⟩ := hd
  have hk0 : 0 < k := by
    apply (mul_lt_mul_iff_right₀ hq).mp
    nlinarith only [hk, hx]
  have hk2 : k < 2 := by
    apply (mul_lt_mul_iff_right₀ hq).mp
    nlinarith only [hk, hxq]
  have he : k = 1 := by omega
  simpa only [he, mul_one] using hk

#print axioms short_phase_card
#print axioms gap_eq_step
end
end JSP233.ResidueCard88404
