import Erdos272.Resources.SharedUniform209
import Erdos272.Resources.StrongAPResponse209

namespace JSP233.SharedUniformStrong209
open StarCompletion APGeometry DenseDeletion40 Density41 IntrinsicTriples208 HarmonicAbel29
open UniformCapacity208 UniformFees208 SevenFamily208 GlobalSeven208 SharedUniform209
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

def CoupledShare : ℝ := 1663/5975
theorem actual_original_shared_payment {N : ℕ} {F : Finset (Finset ℤ)}
    {v g fee : ℝ} (hN : 2≤N) (hv : 0<v) (hF : Legal (Ground N) F) (hg : 0≤g)
    (hT : (TripleShare*g/v^3)*(N : ℝ)≤StrongAPResponse209.T)
    (hsource : ((F.filter fun S=>¬IsAP S).card : ℝ)≤
      6*(TripleShare*g/v^3)*(∑ S∈F,((Pool S).card : ℝ))+
      SlotShare*g*(N : ℝ)^3/v^3+fee) :
    (F.card : ℝ)≤(329/800 : ℝ)*(N : ℝ)^2+CoupledShare*g*(N : ℝ)^3/v^3+
      (N : ℝ)*Harmonic N+1+fee := by
  have hgp : 0≤TripleShare*g/v^3 := by dsimp only [TripleShare]; positivity
  have hh := StrongAPResponse209.actual_joint_any_AP (fee := SlotShare*g*(N : ℝ)^3/v^3+fee)
    hN hF hgp hT (by linarith only [hsource])
  calc
    _≤(329/800 : ℝ)*(N : ℝ)^2+StrongAPResponse209.Kappa*(TripleShare*g/v^3)*(N : ℝ)^3+
        (N : ℝ)*Harmonic N+1+(SlotShare*g*(N : ℝ)^3/v^3+fee) := hh
    _=_ := by dsimp only [SlotShare,TripleShare,CoupledShare,StrongAPResponse209.Kappa]; ring

/-- Root payment and deletion are inserted once, for the original F.
`hcover` is supplied either by A=G, or by the actual root/avoider partition. -/
theorem actual_shared_payment {N : ℕ} {A F : Finset (Finset ℤ)} {v g u eta root : ℝ}
    (hN : 10902≤N) (hv : 0<v) (hF : Legal (Ground N) F) (hg : 0≤g)
    (hAG : A⊆SparseCrooked N 11 F)
    (hcover : ((SparseCrooked N 11 F).card : ℝ)≤A.card+root)
    (hfee : UniformNearObligation N A v g u eta)
    (hT : (TripleShare*g/v^3)*(N : ℝ)≤StrongAPResponse209.T) :
    (F.card : ℝ)≤(329/800 : ℝ)*(N : ℝ)^2+CoupledShare*g*(N : ℝ)^3/v^3+
      u*(N : ℝ)^2/v+eta*N+(N : ℝ)*Harmonic N+121*N+969+root := by
  have hAF : A⊆F := hAG.trans (actual_sparse_subset N 11 F)
  have hs := actual_source_pool (by omega : 2≤N) hv hF hAF hfee
  have hpart := GlobalSeven208.crooked_partition N F
  have hsource : ((F.filter fun S=>¬IsAP S).card : ℝ)≤
      6*(TripleShare*g/v^3)*(∑ S∈F,((Pool S).card : ℝ))+
      SlotShare*g*(N : ℝ)^3/v^3+
      (u*(N : ℝ)^2/v+eta*N+root+(Deleted N 11 F).card) := by
    linarith only [hs,hpart,hcover]
  have hh := actual_original_shared_payment (by omega : 2≤N) hv hF hg hT hsource
  have hd := DenseDeletion208.actual_deleted11_affine hN hF
  have hdR : ((Deleted N 11 F).card : ℝ)≤121*(N : ℝ)+968 := by exact_mod_cast hd
  linarith only [hh,hdR]

theorem actual_shared_contradiction {N : ℕ} {A F : Finset (Finset ℤ)}
    {v g u eta root : ℝ} (hN : 10902≤N) (hv : 0<v)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card) (hg : 0≤g)
    (hAG : A⊆SparseCrooked N 11 F)
    (hcover : ((SparseCrooked N 11 F).card : ℝ)≤A.card+root)
    (hfee : UniformNearObligation N A v g u eta)
    (hT : (TripleShare*g/v^3)*(N : ℝ)≤StrongAPResponse209.T)
    (hH : Harmonic N≤19)
    (hprice : CoupledShare*g*(N : ℝ)/v^3+u/v+(eta+142)/(N : ℝ)+
      root/(N : ℝ)^2<(71/800 : ℝ)) : False := by
  have hh := actual_shared_payment hN hv hF hg hAG hcover hfee hT
  have hl := GlobalSeven208.original_lower hcard
  have hn : (10902 : ℝ)≤N := by exact_mod_cast hN
  have hn0 : (N : ℝ)≠0 := by linarith only [hn]
  have hpaid := mul_lt_mul_of_pos_right hprice
    (sq_pos_of_pos (by linarith only [hn] : (0 : ℝ)<N))
  have he : (CoupledShare*g*(N : ℝ)/v^3+u/v+(eta+142)/(N : ℝ)+
      root/(N : ℝ)^2)*(N : ℝ)^2=
      CoupledShare*g*(N : ℝ)^3/v^3+u*(N : ℝ)^2/v+(eta+142)*N+root := by
    field_simp
    <;> ring
  rw [he] at hpaid
  have hHpay := mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg (α := ℝ) N)
  nlinarith only [hh,hl,hpaid,hHpay,hn]

#print axioms family_pool_resource
#print axioms actual_source_pool
#print axioms actual_original_shared_payment
#print axioms actual_shared_payment
#print axioms actual_shared_contradiction
end
end JSP233.SharedUniformStrong209
