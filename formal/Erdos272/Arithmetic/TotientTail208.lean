import Erdos272.Arithmetic.PrimorialRatio39
import Erdos272.Arithmetic.PureSource208

/-! Analytic tail closure for the finite source calculation.  A kernel
certificate need only cover a short prefix: the already proved primorial
ratio bound pays every later physical size by the d=1 terms alone. -/
namespace JSP233.TotientTail208
open PureSource208
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

theorem seven_totient {q : ℕ} (hq : q < 2^50) : q ≤ 7 * Nat.totient q := by
  have hr := (PrimorialRatio39.uniform_q49 q hq).2.1 q le_rfl
  have hp : (0 : ℝ) ≤ Nat.totient q := Nat.cast_nonneg _
  have hqR : (q : ℝ) ≤ 7 * Nat.totient q := by nlinarith only [hr, hp]
  exact_mod_cast hqR

theorem multiplicity_d1 {s q : ℕ} (hs : 1 ≤ s) : s - q ≤ intervalMultiplicity s q := by
  have hm : 1 ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨le_rfl, hs⟩
  have h := Finset.single_le_sum (fun d _ => Nat.zero_le (s - d*q)) hm
  simpa only [intervalMultiplicity, one_mul] using h

theorem reverse_triangular (s e : ℕ) (he : e ≤ s) :
    (∑ q ∈ Finset.Ico (s-e) s, (s-q)) = (e+1).choose 2 := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hI : Finset.Ico (s-(e+1)) s =
        insert (s-(e+1)) (Finset.Ico (s-e) s) := by
      ext q
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnot : s-(e+1) ∉ Finset.Ico (s-e) s := by
      simp only [Finset.mem_Ico]
      omega
    rw [hI, Finset.sum_insert hnot, ih (by omega)]
    have hsub : s - (s - (e+1)) = e+1 := by omega
    rw [hsub]
    have hp := Nat.choose_succ_succ (e+1) 1
    simpa only [Nat.choose_one_right, Nat.succ_eq_add_one, Nat.add_comm] using hp.symm

theorem physical_tail_lower {s e : ℕ} (hs : 1 ≤ s) (he : e ≤ s) (hhi : s < 2^50) :
    (s-e) * (e+1).choose 2 ≤ 7 * physicalK s e := by
  have hpoint : ∀ q ∈ Finset.Ico (s-e) s,
      (s-e)*(s-q) ≤ 7 * (Nat.totient q * intervalMultiplicity s q) := by
    intro q hq
    obtain ⟨hql, hqs⟩ := Finset.mem_Ico.mp hq
    have hphi := hql.trans (seven_totient (hqs.trans hhi))
    have hmult := multiplicity_d1 (q := q) hs
    have h1 := Nat.mul_le_mul_right (s-q) hphi
    have h2 := Nat.mul_le_mul_left (7 * Nat.totient q) hmult
    nlinarith only [h1, h2]
  have h := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum, ← Finset.mul_sum, reverse_triangular s e he] at h
  simpa only [physicalK] using h

theorem tail_floor {s e b cutoff : ℕ}
    (hs : 1 ≤ s) (he : e ≤ cutoff) (hcut : cutoff ≤ s) (hhi : s < 2^50)
    (hb : 7*b ≤ (cutoff-e) * (e+1).choose 2) : b ≤ physicalK s e := by
  have hmono := Nat.mul_le_mul_right ((e+1).choose 2) (Nat.sub_le_sub_right hcut e)
  have hl := physical_tail_lower hs (he.trans hcut) hhi
  omega

#print axioms seven_totient
#print axioms physical_tail_lower
#print axioms tail_floor
end JSP233.TotientTail208
