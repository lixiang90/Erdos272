import Erdos272.Resources.WeightedTail39
import Erdos272.Retention.ThinFringe38
import Erdos272.Arithmetic.PrimorialRatio39
import Erdos272.Global.SparseRoot49
import Mathlib.Data.Nat.Sqrt

/-! Actual q49 cutoff and r28 recovery arithmetic. -/
namespace JSP233.Startup49
open StarCompletion
open scoped Classical
noncomputable section

def Cutoff (N : ℕ) : ℕ := N.sqrt/128

theorem cutoff_square (N : ℕ) : 16384*(Cutoff N)^2≤N := by
  have hd := Nat.div_mul_le_self N.sqrt 128
  have hs := Nat.sqrt_le N
  have hh := Nat.mul_le_mul hd hd
  dsimp [Cutoff]
  nlinarith only [hh,hs]

theorem cutoff_lower (N : ℕ) (hN : 2^49≤N) : 185363≤Cutoff N := by
  have hs : 185363*128≤N.sqrt := by
    apply Nat.le_sqrt.mpr
    norm_num
    omega
  exact (Nat.le_div_iff_mul_le (by decide : 0<128)).mpr hs

theorem cutoff_upper (N : ℕ) (hN : N≤2^50) : Cutoff N≤262144 := by
  have hs : N.sqrt≤33554432 := by
    have hh : N.sqrt<33554433 := by
      apply Nat.sqrt_lt.mpr
      norm_num at hN ⊢
      omega
    omega
  dsimp [Cutoff]
  omega

theorem cutoff_interval (N : ℕ) (hNl : 2^49≤N) (hNu : N<2^50) :
    185363≤Cutoff N ∧ Cutoff N≤262144 ∧ 16384*(Cutoff N)^2≤N := by
  exact ⟨cutoff_lower N hNl,cutoff_upper N hNu.le,cutoff_square N⟩

theorem anchor_count28 : ThinFringe38.AnchorCount 28=703 := by
  norm_num [ThinFringe38.AnchorCount,Finset.sum_Icc_succ_top]

theorem actual_long_core_restore28 (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : 900≤N) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N) (hfringe : 2812*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<28*S.card)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) : F.card≤B N := by
  apply ThinFringe38.actual_long_core_restore 28 N c L R F G E (by decide) (by norm_num; exact hN)
    hc hcL hLR hRN hthin (by norm_num; omega) ?_ hG hEF hlegal hbad hdense hne hi
  simpa only [anchor_count28] using hfringe

theorem actual_q49_large_budget (N : ℕ) (F : Finset (Finset ℤ))
    (hNl : 2^49≤N) (hNu : N<2^50) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hlow : ∀ S∈F,16*Cutoff N+1≤S.card) :
    (F.card:ℝ)*Cutoff N≤(174/5+16*WeightedTail39.Seed49Sigma)*(N:ℝ)^2 := by
  obtain ⟨hKl,hKu,_⟩ := cutoff_interval N hNl hNu
  obtain ⟨homega,hratio,hproduct⟩ := PrimorialRatio39.uniform_q49 N hNu
  apply WeightedTail39.actual_seed49_large_budget N (Cutoff N) F hlegal hKl hKu hbad hlow
    homega _ hproduct
  simpa only [WeightedTail39.Seed49Ratio] using hratio

theorem actual_q49_sparse_common_root (N : ℕ) (F : Finset (Finset ℤ))
    (hNl : 2^49≤N) (hNu : N<2^50) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,28*S.card≤N)
    (hdense : (N:ℝ)^2/12-6343*(N:ℝ)-3≤F.card) :
    ∃ c∈Ground N,∀ S∈F,c∈S := by
  obtain ⟨hKl,hKu,hthin⟩ := cutoff_interval N hNl hNu
  obtain ⟨homega,hratio,hproduct⟩ := PrimorialRatio39.uniform_q49 N hNu
  apply SparseRoot49.actual_seed49_sparse_common_root hNl hlegal hKl hKu hthin hbad hsize
    hdense homega _ hproduct
  simpa only [WeightedTail39.Seed49Ratio] using hratio

#print axioms cutoff_square
#print axioms cutoff_lower
#print axioms cutoff_upper
#print axioms cutoff_interval
#print axioms anchor_count28
#print axioms actual_long_core_restore28
#print axioms actual_q49_large_budget
#print axioms actual_q49_sparse_common_root
end
end JSP233.Startup49
