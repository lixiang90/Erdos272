import Erdos272.Resources.CoreFringe208

/-! Actual physical steps have the proper-divisor ratio used by the five
arithmetic classes. The final class only excludes 2,3,5,7. -/
namespace JSP233.StepClass208
set_option maxHeartbeats 0

theorem ratio_of_quotient {d delta p : ℤ} (hdelta : 0 < delta)
    (hdiv : delta ∣ d) (hlt : delta < d)
    (hexclude : ∀ q : ℤ, 2 ≤ q → q < p → ¬q ∣ d) : p*delta ≤ d := by
  obtain ⟨q,hq⟩ := hdiv
  have hq2 : 2 ≤ q := by nlinarith only [hdelta,hlt,hq]
  have hpq : p ≤ q := by
    by_contra hn
    exact hexclude q hq2 (by omega) (by rw [hq]; exact dvd_mul_left q delta)
  nlinarith only [hpq,hq,hdelta]

theorem ratio_two {d delta : ℤ} (hdelta : 0 < delta) (hdiv : delta ∣ d)
    (hlt : delta < d) : 2*delta ≤ d :=
  ratio_of_quotient hdelta hdiv hlt (by intro q hq hq'; omega)

theorem ratio_three {d delta : ℤ} (hdelta : 0 < delta) (hdiv : delta ∣ d)
    (hlt : delta < d) (h2 : ¬2 ∣ d) : 3*delta ≤ d := by
  apply ratio_of_quotient hdelta hdiv hlt
  intro q hq hq'
  have he : q=2 := by omega
  simpa only [he] using h2

theorem ratio_five {d delta : ℤ} (hdelta : 0 < delta) (hdiv : delta ∣ d)
    (hlt : delta < d) (h2 : ¬2 ∣ d) (h3 : ¬3 ∣ d) : 5*delta ≤ d := by
  apply ratio_of_quotient hdelta hdiv hlt
  intro q hq hq' hd
  have hf : 2 ∣ q ∨ 3 ∣ q := by omega
  rcases hf with hf | hf
  · exact h2 (dvd_trans hf hd)
  · exact h3 (dvd_trans hf hd)

theorem ratio_seven {d delta : ℤ} (hdelta : 0 < delta) (hdiv : delta ∣ d)
    (hlt : delta < d) (h2 : ¬2 ∣ d) (h3 : ¬3 ∣ d) (h5 : ¬5 ∣ d) : 7*delta ≤ d := by
  apply ratio_of_quotient hdelta hdiv hlt
  intro q hq hq' hd
  have hf : 2 ∣ q ∨ 3 ∣ q ∨ 5 ∣ q := by interval_cases q <;> norm_num
  rcases hf with hf | hf | hf
  · exact h2 (dvd_trans hf hd)
  · exact h3 (dvd_trans hf hd)
  · exact h5 (dvd_trans hf hd)

theorem ratio_eleven {d delta : ℤ} (hdelta : 0 < delta) (hdiv : delta ∣ d)
    (hlt : delta < d) (h2 : ¬2 ∣ d) (h3 : ¬3 ∣ d) (h5 : ¬5 ∣ d)
    (h7 : ¬7 ∣ d) : 11*delta ≤ d := by
  apply ratio_of_quotient hdelta hdiv hlt
  intro q hq hq' hd
  have hf : 2 ∣ q ∨ 3 ∣ q ∨ 5 ∣ q ∨ 7 ∣ q := by interval_cases q <;> norm_num
  rcases hf with hf | hf | hf | hf
  · exact h2 (dvd_trans hf hd)
  · exact h3 (dvd_trans hf hd)
  · exact h5 (dvd_trans hf hd)
  · exact h7 (dvd_trans hf hd)

def PrimeGate (d : ℕ) : ℕ :=
  if 2 ∣ d then 2 else if 3 ∣ d then 3 else if 5 ∣ d then 5 else if 7 ∣ d then 7 else 11

theorem primeGate_range (d : ℕ) : PrimeGate d ∈ ({2,3,5,7,11} : Finset ℕ) := by
  unfold PrimeGate
  split_ifs <;> norm_num

theorem actual_ratio (d : ℕ) {delta : ℤ} (hdelta : 0 < delta)
    (hdiv : delta ∣ (d : ℤ)) (hlt : delta < d) : (PrimeGate d : ℤ)*delta ≤ d := by
  unfold PrimeGate
  split_ifs with h2 h3 h5 h7
  · exact ratio_two hdelta hdiv hlt
  · exact ratio_three hdelta hdiv hlt (by exact_mod_cast h2)
  · exact ratio_five hdelta hdiv hlt (by exact_mod_cast h2) (by exact_mod_cast h3)
  · exact ratio_seven hdelta hdiv hlt (by exact_mod_cast h2) (by exact_mod_cast h3) (by exact_mod_cast h5)
  · exact ratio_eleven hdelta hdiv hlt (by exact_mod_cast h2) (by exact_mod_cast h3)
      (by exact_mod_cast h5) (by exact_mod_cast h7)

#print axioms ratio_of_quotient
#print axioms actual_ratio
end JSP233.StepClass208
