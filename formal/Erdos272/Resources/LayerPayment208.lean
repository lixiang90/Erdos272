module

public import Erdos272.Resources.IntrinsicTriples208
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! A fractional cover pays the one actual triple pool once.  The pointwise
cover is the interface for the source-potential and threshold lemmas; the
near families may differ from layer to layer. -/
namespace JSP233.LayerPayment208
open StarCompletion IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem suffix_increments (psi : ℕ → ℝ) (cap e : ℕ) :
    (∑ i ∈ Finset.range cap, (psi (i+1) - psi i) * (if e < i+1 then 1 else 0)) =
      psi cap - psi (min cap e) := by
  induction cap with
  | zero => simp
  | succ cap ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases he : e < cap+1
    · have hecap : e ≤ cap := by omega
      have hesucc : e ≤ cap+1 := by omega
      simp only [if_pos he, mul_one, min_eq_right hecap, min_eq_right hesucc]
      ring
    · have hsucc : cap+1 ≤ e := by omega
      have hcap : cap ≤ e := by omega
      simp only [if_neg he, mul_zero, min_eq_left hcap, min_eq_left hsucc, sub_self, add_zero]

theorem pointwise_cover_of_potential (psi : ℕ → ℝ) (cap e : ℕ) (mass : ℝ)
    (hmono : Monotone psi) (hmass : psi e ≤ mass) :
    psi cap ≤ mass + ∑ i ∈ Finset.range cap,
      (psi (i+1) - psi i) * (if e < i+1 then 1 else 0) := by
  rw [suffix_increments]
  have hm := (hmono (min_le_right cap e)).trans hmass
  linarith only [hm]

theorem increments_nonneg (psi : ℕ → ℝ) (hmono : Monotone psi) (i : ℕ) :
    0 ≤ psi (i+1) - psi i := sub_nonneg.mpr (hmono (by omega))

theorem fractional_cover {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (F : Finset α) (I : Finset ι) (near : ι → Finset α)
    (mass : α → ℝ) (delta : ι → ℝ) (potential : ℝ)
    (hsub : ∀ i ∈ I, near i ⊆ F)
    (hcover : ∀ S ∈ F, potential ≤ mass S +
      ∑ i ∈ I, delta i * (if S ∈ near i then 1 else 0)) :
    potential * F.card ≤ (∑ S ∈ F, mass S) + ∑ i ∈ I, delta i * (near i).card := by
  have hsum := Finset.sum_le_sum hcover
  rw [Finset.sum_add_distrib, Finset.sum_comm] at hsum
  have hinner : ∀ i ∈ I,
      (∑ S ∈ F, delta i * (if S ∈ near i then 1 else 0)) = delta i * (near i).card := by
    intro i hi
    have he : F.filter (fun S => S ∈ near i) = near i := by
      ext S
      simp only [Finset.mem_filter]
      exact and_iff_right_of_imp (fun hS => hsub i hi hS)
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, he,
      Finset.sum_const, nsmul_eq_mul]
    ring
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  rw [Finset.sum_congr rfl hinner] at hsum
  simpa only [mul_comm] using hsum

theorem actual_layer_payment {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (near : ι → Finset (Finset ℤ)) (delta fee : ι → ℝ) (potential : ℝ)
    (hF : Legal Ω F) (hsub : ∀ i ∈ I, near i ⊆ F)
    (hdelta : ∀ i ∈ I, 0 ≤ delta i)
    (hcover : ∀ S ∈ F, potential ≤ (Pool S).card +
      ∑ i ∈ I, delta i * (if S ∈ near i then 1 else 0))
    (hfee : ∀ i ∈ I, ((near i).card : ℝ) ≤ fee i) :
    potential * F.card ≤ (Ω.card.choose 3 : ℝ) + ∑ i ∈ I, delta i * fee i := by
  have h := fractional_cover F I near (fun S => ((Pool S).card : ℝ)) delta potential hsub hcover
  have hc : (∑ S ∈ F, ((Pool S).card : ℝ)) ≤ (Ω.card.choose 3 : ℝ) := by
    exact_mod_cast actual_capacity hF
  have hf := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hfee i hi) (hdelta i hi))
  linarith only [h, hc, hf]

/-- Reserve the AP triples before paying any near layer. -/
theorem actual_layer_payment_with_AP {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (near : ι → Finset (Finset ℤ)) (delta fee : ι → ℝ) (potential : ℝ)
    (hF : Legal Ω F) (hP : P ∈ F) (hAP : IsAP P)
    (hsub : ∀ i ∈ I, near i ⊆ F) (hdelta : ∀ i ∈ I, 0 ≤ delta i)
    (hcover : ∀ S ∈ F, potential ≤ (Pool S).card +
      ∑ i ∈ I, delta i * (if S ∈ near i then 1 else 0))
    (hfee : ∀ i ∈ I, ((near i).card : ℝ) ≤ fee i) :
    potential * F.card ≤ (Ω.card.choose 3 : ℝ) - (P.card.choose 3 : ℝ) +
      ∑ i ∈ I, delta i * fee i := by
  have h := fractional_cover F I near (fun S => ((Pool S).card : ℝ)) delta potential hsub hcover
  have hc : (∑ S ∈ F, ((Pool S).card : ℝ)) + (P.card.choose 3 : ℝ) ≤
      (Ω.card.choose 3 : ℝ) := by exact_mod_cast actual_capacity_with_AP hF hP hAP
  have hf := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hfee i hi) (hdelta i hi))
  linarith only [h, hc, hf]

#print axioms fractional_cover
#print axioms pointwise_cover_of_potential
#print axioms actual_layer_payment
#print axioms actual_layer_payment_with_AP
end
end JSP233.LayerPayment208
