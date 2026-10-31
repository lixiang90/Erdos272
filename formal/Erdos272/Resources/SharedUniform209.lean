import Erdos272.Resources.UniformFees208
import Erdos272.Global.GlobalSeven208

/-! Keep the actual triple pool until the same original family's longest AP
has been selected.  Slot capacity is paid once; no triple cube is substituted
before the existing same-AP response theorem is applied. -/
namespace JSP233.SharedUniform209
open StarCompletion APGeometry DenseDeletion40 Density41 IntrinsicTriples208 HarmonicAbel29
open UniformCapacity208 UniformFees208 SevenFamily208 GlobalSeven208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

theorem family_pool_resource {N : ℕ} {A F : Finset (Finset ℤ)} {v M : ℝ}
    (hN : 2≤N) (hv : 0<v) (hM : 0<M) (hF : Legal (Ground N) F) (hAF : A⊆F)
    (psi : ℕ→ℝ) (hpsi : Monotone psi) (hz : psi 0=0)
    (near : ℕ→Finset (Finset ℤ)) (fee : ℕ→ℝ) (cap : ℕ)
    (hsub : ∀ i<cap,near i⊆A) (hfee : ∀ i<cap,((near i).card : ℝ)≤fee i)
    (hfar : ∀ S∈A,∀ i<cap,S∉near i →v^2*psi (i+1)≤JointMass N v M S) :
    v^2*psi cap*A.card≤25*(N : ℝ)^3/(14*v*M)+
      160/(v*M)*(∑ S∈F,((Pool S).card : ℝ))+
      v^2*(∑ i∈Finset.range cap,(psi (i+1)-psi i)*fee i) := by
  have hh := family_resource hv hM psi hpsi hz near fee cap hsub hfee hfar
  have hs : (∑ S∈A,JointMass N v M S)≤∑ S∈F,JointMass N v M S :=
    Finset.sum_le_sum_of_subset_of_nonneg hAF (fun S _ _=>joint_nonneg hv hM S)
  have hc := actual_slot_capacity hN hv hM hF
  simp only [JointMass,Finset.sum_add_distrib,←Finset.mul_sum] at hh hs
  linarith only [hh,hs,hc]

theorem family_pool_price {N : ℕ} {A F : Finset (Finset ℤ)} {v M : ℝ}
    (hN : 2≤N) (hv : 0<v) (hM : 0<M) (hF : Legal (Ground N) F) (hAF : A⊆F)
    (psi : ℕ→ℝ) (hpsi : Monotone psi) (hz : psi 0=0)
    (near : ℕ→Finset (Finset ℤ)) (fee : ℕ→ℝ) (cap : ℕ) (hcap : 0<psi cap)
    (hsub : ∀ i<cap,near i⊆A) (hfee : ∀ i<cap,((near i).card : ℝ)≤fee i)
    (hfar : ∀ S∈A,∀ i<cap,S∉near i →v^2*psi (i+1)≤JointMass N v M S) :
    (A.card : ℝ)≤25/(14*M*psi cap)*(N : ℝ)^3/v^3+
      160/(M*psi cap)/v^3*(∑ S∈F,((Pool S).card : ℝ))+
      (∑ i∈Finset.range cap,(psi (i+1)-psi i)*fee i)/(psi cap) := by
  have hh := family_pool_resource hN hv hM hF hAF psi hpsi hz near fee cap hsub hfee hfar
  have hden : 0<v^2*psi cap := by positivity
  apply (mul_le_mul_iff_right₀ hden).mp
  have he : (v^2*psi cap)*(25/(14*M*psi cap)*(N : ℝ)^3/v^3+
      160/(M*psi cap)/v^3*(∑ S∈F,((Pool S).card : ℝ))+
      (∑ i∈Finset.range cap,(psi (i+1)-psi i)*fee i)/(psi cap))=
      25*(N : ℝ)^3/(14*v*M)+160/(v*M)*(∑ S∈F,((Pool S).card : ℝ))+
      v^2*(∑ i∈Finset.range cap,(psi (i+1)-psi i)*fee i) := by
    field_simp
    <;> ring
  rw [he]
  exact hh

def SlotShare : ℝ := 15/239
def TripleShare : ℝ := 224/239
def CoupledShare : ℝ := 1831/5975

theorem shares : SlotShare+TripleShare=1 ∧
    SlotShare+APCoupling208.Kappa*TripleShare=CoupledShare := by
  norm_num [SlotShare,TripleShare,CoupledShare,APCoupling208.Kappa]

/-- This keeps the original F's intrinsic pool and the exact same near sets.
The obligation is still the weighted count of actual deficiency families. -/
theorem actual_source_pool {N : ℕ} {A F : Finset (Finset ℤ)} {v g u eta : ℝ}
    (hN : 2≤N) (hv : 0<v) (hF : Legal (Ground N) F) (hAF : A⊆F)
    (hfee : UniformNearObligation N A v g u eta) :
    (A.card : ℝ)≤6*(TripleShare*g/v^3)*(∑ S∈F,((Pool S).card : ℝ))+
      SlotShare*g*(N : ℝ)^3/v^3+u*(N : ℝ)^2/v+eta*N := by
  obtain ⟨psi,cap,hpsi,hzero,hpos,hg,hpaid⟩ := hfee
  have hh := family_pool_price hN hv (by norm_num : (0 : ℝ)<242) hF hAF
    psi hpsi hzero (JointNear N A v 242 psi)
    (fun i=>((JointNear N A v 242 psi i).card : ℝ)) cap hpos
    (fun i hi=>Finset.filter_subset _ _) (fun i hi=>le_rfl) (by
      intro S hS i hi hn
      by_contra hbad
      exact hn (Finset.mem_filter.mpr ⟨hS,lt_of_not_ge hbad⟩))
  have hs : 25/(14*242*psi cap)=SlotShare*g := by
    rw [←hg]
    dsimp only [SlotShare]
    field_simp
    <;> ring
  have ht : 160/(242*psi cap)=6*TripleShare*g := by
    rw [←hg]
    dsimp only [TripleShare]
    field_simp
    <;> ring
  rw [hs,ht] at hh
  have he : 6*TripleShare*g/v^3*(∑ S∈F,((Pool S).card : ℝ))=
      6*(TripleShare*g/v^3)*(∑ S∈F,((Pool S).card : ℝ)) := by ring
  rw [he] at hh
  linarith only [hh,hpaid]

/-- The same longest AP is used by the existing actual joint theorem. -/
theorem actual_original_shared_payment {N : ℕ} {F : Finset (Finset ℤ)}
    {v g fee : ℝ} (hN : 2≤N) (hv : 0<v) (hF : Legal (Ground N) F) (hg : 0≤g)
    (hT : (TripleShare*g/v^3)*(N : ℝ)≤APCoupling208.T)
    (hsource : ((F.filter fun S=>¬IsAP S).card : ℝ)≤
      6*(TripleShare*g/v^3)*(∑ S∈F,((Pool S).card : ℝ))+
      SlotShare*g*(N : ℝ)^3/v^3+fee) :
    (F.card : ℝ)≤(329/800 : ℝ)*(N : ℝ)^2+CoupledShare*g*(N : ℝ)^3/v^3+
      (N : ℝ)*Harmonic N+1+fee := by
  have hgp : 0≤TripleShare*g/v^3 := by dsimp only [TripleShare]; positivity
  have hh := GlobalSeven208.actual_joint_any_AP (fee := SlotShare*g*(N : ℝ)^3/v^3+fee)
    hN hF hgp hT (by linarith only [hsource])
  calc
    _≤(329/800 : ℝ)*(N : ℝ)^2+APCoupling208.Kappa*(TripleShare*g/v^3)*(N : ℝ)^3+
        (N : ℝ)*Harmonic N+1+(SlotShare*g*(N : ℝ)^3/v^3+fee) := hh
    _=_ := by dsimp only [SlotShare,TripleShare,CoupledShare,APCoupling208.Kappa]; ring

/-- Root payment and deletion are inserted once, for the original F.
`hcover` is supplied either by A=G, or by the actual root/avoider partition. -/
theorem actual_shared_payment {N : ℕ} {A F : Finset (Finset ℤ)} {v g u eta root : ℝ}
    (hN : 10902≤N) (hv : 0<v) (hF : Legal (Ground N) F) (hg : 0≤g)
    (hAG : A⊆SparseCrooked N 11 F)
    (hcover : ((SparseCrooked N 11 F).card : ℝ)≤A.card+root)
    (hfee : UniformNearObligation N A v g u eta)
    (hT : (TripleShare*g/v^3)*(N : ℝ)≤APCoupling208.T) :
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
    (hT : (TripleShare*g/v^3)*(N : ℝ)≤APCoupling208.T)
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
end JSP233.SharedUniform209
