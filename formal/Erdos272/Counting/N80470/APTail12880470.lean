module

public import Erdos272.Counting.N80470.APLossAggregate80470

@[expose] public section

namespace JSP233.APTail12880470
open StarCompletion APGeometry DenseDeletion40 IntrinsicTriples208 HarmonicAbel29
open APQuotient80470 AP128Family80470 AP128Constants80470 APLossAggregate80470
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
set_option Elab.async false

theorem coefficient_sum :
    (∑ k∈Finset.Icc 1 128, Coefficient k)=NuExact-1/4 := by
  unfold NuExact
  ring

theorem fee_sum : (∑ k∈Finset.Icc 1 128, Fee k)=C-1/8 := by
  norm_num [Fee, C, Finset.sum_Icc_succ_top]

theorem credit_sum (n : ℕ) :
    (∑ k∈Finset.Icc 1 128, Credit n k)=(n : ℝ)*(NuExact-1/4)-(C-1/8) := by
  simp only [Credit]
  rw [Finset.sum_sub_distrib, ←Finset.mul_sum, coefficient_sum, fee_sum]

theorem tail_identity (n : ℕ) :
    Tail n=(∑ d∈Finset.Icc 2 n, Base n d)-(∑ d∈Finset.Icc 2 n, Loss n d) := by
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold Loss
  ring

theorem tail_certificate {n : ℕ} (hn : 16512≤n) : TailCertificate n := by
  have hloss := selected_loss hn
  rw [credit_sum] at hloss
  have hbase := base_sum_bound (by omega : 64≤n)
  have hnu := mul_le_mul_of_nonneg_right AP128Constants80470.nu_coefficient.le
    (Nat.cast_nonneg (α := ℝ) n)
  dsimp only [TailCertificate]
  rw [tail_identity]
  nlinarith only [hloss, hbase, hnu]

theorem actual_AP_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 16513≤N) (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ)≤Flat (N-1) :=
  AP128Family80470.actual_AP_count hF (tail_certificate (by omega : 16512≤N-1))

theorem actual_joint {N : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hN : 16513≤N) (hg : 0<g) (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ)+6*g*(∑ S∈F, ((Pool S).card : ℝ))≤
      Response g ((N-1 : ℕ) : ℝ) (Harmonic (N-1)) :=
  AP128Family80470.actual_joint (by omega : 2≤N) hg hF
    (tail_certificate (by omega : 16512≤N-1))

theorem actual_flat_AP_deleted {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 16513≤N) (hhi : N≤179999) (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ)+((Deleted N 12 F).card : ℝ)≤Flat (N-1) :=
  AP128Family80470.actual_flat_AP_deleted hN hhi hF
    (tail_certificate (by omega : 16512≤N-1))

theorem actual_AP_inner_with_deleted {N : ℕ} {F A0 : Finset (Finset ℤ)} {g Q : ℝ}
    (hN : 16513≤N) (hhi : N≤2^18) (hF : Legal (Ground N) F)
    (hAF : A0⊆F) (hsparse : ∀ S∈A0, 12*S.card≤N) (hg : 0<g)
    (hpay : 1≤6*g*180200)
    (hinner : (A0.card : ℝ)≤6*g*(∑ S∈A0, ((Pool S).card : ℝ))+Q) :
    ((F.filter IsAP).card : ℝ)+(A0.card : ℝ)+((Deleted N 12 F).card : ℝ)≤
      Response g ((N-1 : ℕ) : ℝ) (Harmonic (N-1))+Q :=
  AP128Family80470.actual_AP_inner_with_deleted (by omega : 15000≤N) hhi
    hF hAF hsparse hg hpay (tail_certificate (by omega : 16512≤N-1)) hinner

#print axioms coefficient_sum
#print axioms fee_sum
#print axioms credit_sum
#print axioms tail_identity
#print axioms tail_certificate
#print axioms actual_AP_count
#print axioms actual_joint
#print axioms actual_flat_AP_deleted
#print axioms actual_AP_inner_with_deleted
end
end JSP233.APTail12880470
