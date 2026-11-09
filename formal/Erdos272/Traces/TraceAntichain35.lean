module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Actual divisor-minimal traces have a square lower bound on their index sum.
This module proves the finite arithmetic independently of the external KK file. -/
namespace JSP233.TraceAntichain35
open scoped Classical BigOperators
noncomputable section

def OddPart (n : ℕ) : ℕ := ordCompl[2] n

theorem oddPart_le (n : ℕ) : OddPart n ≤ n := Nat.ordCompl_le n 2

theorem oddPart_odd {n : ℕ} (hn : 0<n) : Odd (OddPart n) := by
  exact Nat.not_even_iff_odd.1
    (mt Even.two_dvd (Nat.not_dvd_ordCompl Nat.prime_two (by omega : n≠0)))

theorem odd_finset_square_le_sum (A : Finset ℕ) (hodd : ∀ a∈A, Odd a) :
    A.card^2 ≤ ∑ a∈A, a := by
  revert hodd
  induction A using Finset.induction_on_max with
  | empty => simp
  | @insert a A hlt ih =>
    intro hodd
    have haodd := hodd a (by simp)
    have hAodd : ∀ x∈A, Odd x := fun x hx => hodd x (Finset.mem_insert_of_mem hx)
    obtain ⟨t, ht⟩ := haodd
    have ha : a=2*t+1 := by omega
    have hinj : Set.InjOn (fun x:ℕ => x/2) (A:Set ℕ) := by
      intro x hx y hy hxy
      have hxo := Nat.odd_iff.mp (hAodd x hx)
      have hyo := Nat.odd_iff.mp (hAodd y hy)
      change x/2=y/2 at hxy
      omega
    have hmaps : Set.MapsTo (fun x:ℕ => x/2) (A:Set ℕ) (Finset.range t : Set ℕ) := by
      intro x hx
      have hxa := hlt x hx
      have hxo := Nat.odd_iff.mp (hAodd x hx)
      apply Finset.mem_range.mpr
      change x/2<t
      omega
    have hcard : A.card≤t := by
      simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmaps hinj
    have hna : a∉A := by intro h; have hh := hlt a h; omega
    have hsum := ih hAodd
    rw [Finset.card_insert_of_notMem hna, Finset.sum_insert hna]
    nlinarith

theorem oddPart_injective_on_divisor_antichain (A : Finset ℕ)
    (hanti : ∀ a∈A, ∀ b∈A, a∣b → a=b) :
    Set.InjOn OddPart (A:Set ℕ) := by
  intro a ha b hb heq
  have hreprA : 2^(a.factorization 2)*OddPart a=a :=
    Nat.ordProj_mul_ordCompl_eq_self a 2
  have hreprB : 2^(b.factorization 2)*OddPart b=b :=
    Nat.ordProj_mul_ordCompl_eq_self b 2
  rcases le_total (a.factorization 2) (b.factorization 2) with hab | hba
  · apply hanti a ha b hb
    rw [←hreprA, ←hreprB, heq]
    exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 hab) (dvd_refl _)
  · symm
    apply hanti b hb a ha
    rw [←hreprB, ←hreprA, heq]
    exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 hba) (dvd_refl _)

theorem divisor_antichain_square_le_sum (A : Finset ℕ)
    (hpos : ∀ a∈A, 0<a)
    (hanti : ∀ a∈A, ∀ b∈A, a∣b → a=b) :
    A.card^2 ≤ ∑ a∈A, a := by
  have hinj := oddPart_injective_on_divisor_antichain A hanti
  have ho : ∀ b∈A.image OddPart, Odd b := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact oddPart_odd (hpos a ha)
  calc
    A.card^2 = (A.image OddPart).card^2 := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ ∑ b∈A.image OddPart, b := odd_finset_square_le_sum _ ho
    _ = ∑ a∈A, OddPart a := Finset.sum_image hinj
    _ ≤ ∑ a∈A, a := Finset.sum_le_sum fun a _ => oddPart_le a

theorem quotient_dvd_reverse {m a b : ℕ} (hm : 0<m)
    (ha : a∣m) (hb : b∣m) (hquot : m/a∣m/b) : b∣a := by
  have ha0 : 0<a := Nat.pos_of_dvd_of_pos ha hm
  have hq : 0<m/a := Nat.div_pos (Nat.le_of_dvd hm ha) ha0
  have hma : a*(m/a)=m := Nat.mul_div_cancel' ha
  have hmb : b*(m/b)=m := Nat.mul_div_cancel' hb
  obtain ⟨t, ht⟩ := hquot
  have heq : (m/a)*a=(m/a)*(b*t) := by nlinarith [hma,hmb,ht]
  have heqa : a=b*t := Nat.eq_of_mul_eq_mul_left hq heq
  exact ⟨t,heqa⟩

theorem quotient_injective_on_divisors {m : ℕ} (hm : 0<m) (I : Finset ℕ)
    (hdiv : ∀ d∈I, d∣m) : Set.InjOn (fun d=>m/d) (I:Set ℕ) := by
  intro a ha b hb hab
  change m/a=m/b at hab
  apply Nat.dvd_antisymm
  · exact quotient_dvd_reverse hm (hdiv b hb) (hdiv a ha) (by rw [hab])
  · exact quotient_dvd_reverse hm (hdiv a ha) (hdiv b hb) (by rw [hab])

theorem divisor_quotients_square_le_sum {m : ℕ} (hm : 0<m) (I : Finset ℕ)
    (hdiv : ∀ d∈I, d∣m)
    (hanti : ∀ a∈I, ∀ b∈I, a∣b → a=b) :
    I.card^2 ≤ ∑ d∈I, m/d := by
  have hinj := quotient_injective_on_divisors hm I hdiv
  have hpos : ∀ t∈I.image (fun d=>m/d), 0<t := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
    exact Nat.div_pos (Nat.le_of_dvd hm (hdiv d hd))
      (Nat.pos_of_dvd_of_pos (hdiv d hd) hm)
  have hqa : ∀ a∈I.image (fun d=>m/d), ∀ b∈I.image (fun d=>m/d), a∣b → a=b := by
    intro a ha b hb hab
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    have hed := quotient_dvd_reverse hm (hdiv d hd) (hdiv e he) hab
    have heq := hanti e he d hd hed
    rw [heq]
  calc
    I.card^2 = (I.image (fun d=>m/d)).card^2 := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ ∑ t∈I.image (fun d=>m/d), t := divisor_antichain_square_le_sum _ hpos hqa
    _ = ∑ d∈I, m/d := Finset.sum_image hinj

theorem prefix_index_square_budget {m : ℕ} (hm : 0<m) (I : Finset ℕ) (k : ℕ→ℕ)
    (hdiv : ∀ d∈I, d∣m)
    (hanti : ∀ a∈I, ∀ b∈I, a∣b → a=b)
    (hprefix : ∀ d∈I, m/d≤k d) :
    I.card^2 ≤ ∑ d∈I, k d :=
  (divisor_quotients_square_le_sum hm I hdiv hanti).trans
    (Finset.sum_le_sum hprefix)

theorem minimal_trace_index_square {m : ℕ} (hm : 0<m)
    (I : Finset ℕ) (P : ℕ→Prop) (k : ℕ→ℕ)
    (hdiv : ∀ d∈I, d∣m) (htrace : ∀ d∈I, P d)
    (hminimal : ∀ d∈I, ∀ e, 0<e → e∣d → P e → d≤e)
    (hprefix : ∀ d∈I, m/d≤k d) :
    I.card^2 ≤ ∑ d∈I, k d := by
  apply prefix_index_square_budget hm I k hdiv _ hprefix
  intro a ha b hb hab
  have ha0 := Nat.pos_of_dvd_of_pos (hdiv a ha) hm
  have hb0 := Nat.pos_of_dvd_of_pos (hdiv b hb) hm
  exact Nat.le_antisymm (Nat.le_of_dvd hb0 hab)
    (hminimal b hb a ha0 hab (htrace a ha))

#print axioms oddPart_le
#print axioms oddPart_odd
#print axioms odd_finset_square_le_sum
#print axioms oddPart_injective_on_divisor_antichain
#print axioms divisor_antichain_square_le_sum
#print axioms quotient_dvd_reverse
#print axioms quotient_injective_on_divisors
#print axioms divisor_quotients_square_le_sum
#print axioms prefix_index_square_budget
#print axioms minimal_trace_index_square

end
end JSP233.TraceAntichain35
