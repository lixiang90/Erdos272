module

public import Erdos272.Resources.SharedUniformStrong209
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.IntegerShared209
open StarCompletion APGeometry DenseDeletion40 Density41 IntrinsicTriples208 HarmonicAbel29
open UniformCapacity208 UniformFees208 SevenFamily208 GlobalSeven208 SharedUniform209
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

def NearObligation (N : ℕ) (A : Finset (Finset ℤ)) (M g u eta : ℝ) : Prop :=
  ∃psi : ℕ→ℝ,∃cap : ℕ,Monotone psi ∧ psi 0=0 ∧ 0<psi cap ∧
    1195/(42*M*psi cap)=g ∧
    (∑i∈Finset.range cap,(psi (i+1)-psi i)*((JointNear N A 1 M psi i).card : ℝ))/(psi cap)≤
      u*(N : ℝ)^2+eta*N

theorem actual_source_pool {N : ℕ} {A F : Finset (Finset ℤ)} {M g u eta : ℝ}
    (hN : 2≤N) (hM : 0<M) (hF : Legal (Ground N) F) (hAF : A⊆F)
    (hfee : NearObligation N A M g u eta) :
    (A.card : ℝ)≤6*(TripleShare*g)*(∑ S∈F,((Pool S).card : ℝ))+
      SlotShare*g*(N : ℝ)^3+u*(N : ℝ)^2+eta*N := by
  obtain ⟨psi,cap,hpsi,hzero,hpos,hg,hpaid⟩ := hfee
  have hh := family_pool_price hN (v := 1) (by norm_num) hM hF hAF
    psi hpsi hzero (JointNear N A 1 M psi)
    (fun i=>((JointNear N A 1 M psi i).card : ℝ)) cap hpos
    (fun i hi=>Finset.filter_subset _ _) (fun i hi=>le_rfl) (by
      intro S hS i hi hn
      by_contra hbad
      exact hn (Finset.mem_filter.mpr ⟨hS,lt_of_not_ge hbad⟩))
  have hs : 25/(14*M*psi cap)=SlotShare*g := by
    rw [←hg]
    dsimp only [SlotShare]
    field_simp
    <;> ring
  have ht : 160/(M*psi cap)=6*(TripleShare*g) := by
    rw [←hg]
    dsimp only [TripleShare]
    field_simp
    <;> ring
  rw [hs,ht] at hh
  simp only [one_pow,div_one] at hh
  linarith only [hh,hpaid]

theorem actual_shared_payment {N : ℕ} {A F : Finset (Finset ℤ)} {M g u eta root : ℝ}
    (hN : 10902≤N) (hM : 0<M) (hF : Legal (Ground N) F) (hg : 0≤g)
    (hAG : A⊆SparseCrooked N 11 F)
    (hcover : ((SparseCrooked N 11 F).card : ℝ)≤A.card+root)
    (hfee : NearObligation N A M g u eta)
    (hT : TripleShare*g*(N : ℝ)≤StrongAPResponse209.T) :
    (F.card : ℝ)≤(329/800 : ℝ)*(N : ℝ)^2+SharedUniformStrong209.CoupledShare*g*(N : ℝ)^3+
      u*(N : ℝ)^2+eta*N+(N : ℝ)*Harmonic N+121*N+969+root := by
  have hAF : A⊆F := hAG.trans (actual_sparse_subset N 11 F)
  have hs := actual_source_pool (by omega : 2≤N) hM hF hAF hfee
  have hpart := GlobalSeven208.crooked_partition N F
  have hsource : ((F.filter fun S=>¬IsAP S).card : ℝ)≤
      6*(TripleShare*g/1^3)*(∑ S∈F,((Pool S).card : ℝ))+
      SlotShare*g*(N : ℝ)^3/1^3+
      (u*(N : ℝ)^2+eta*N+root+(Deleted N 11 F).card) := by
    norm_num only [one_pow,div_one]
    linarith only [hs,hpart,hcover]
  have hh := SharedUniformStrong209.actual_original_shared_payment
    (by omega : 2≤N) (v := 1) (by norm_num) hF hg (by simpa using hT) hsource
  simp only [one_pow,div_one] at hh
  have hd := DenseDeletion208.actual_deleted11_affine hN hF
  have hdR : ((Deleted N 11 F).card : ℝ)≤121*(N : ℝ)+968 := by exact_mod_cast hd
  linarith only [hh,hdR]

theorem actual_shared_contradiction {N : ℕ} {A F : Finset (Finset ℤ)}
    {M g u eta root : ℝ} (hN : 10902≤N) (hM : 0<M)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card) (hg : 0≤g)
    (hAG : A⊆SparseCrooked N 11 F)
    (hcover : ((SparseCrooked N 11 F).card : ℝ)≤A.card+root)
    (hfee : NearObligation N A M g u eta)
    (hT : TripleShare*g*(N : ℝ)≤StrongAPResponse209.T)
    (hH : Harmonic N≤19)
    (hprice : SharedUniformStrong209.CoupledShare*g*(N : ℝ)+u+(eta+142)/(N : ℝ)+
      root/(N : ℝ)^2<(71/800 : ℝ)) : False := by
  have hh := actual_shared_payment hN hM hF hg hAG hcover hfee hT
  have hl := GlobalSeven208.original_lower hcard
  have hn : (10902 : ℝ)≤N := by exact_mod_cast hN
  have hn0 : (N : ℝ)≠0 := by linarith only [hn]
  have hpaid := mul_lt_mul_of_pos_right hprice
    (sq_pos_of_pos (by linarith only [hn] : (0 : ℝ)<N))
  have he : (SharedUniformStrong209.CoupledShare*g*(N : ℝ)+u+(eta+142)/(N : ℝ)+
      root/(N : ℝ)^2)*(N : ℝ)^2=
      SharedUniformStrong209.CoupledShare*g*(N : ℝ)^3+u*(N : ℝ)^2+(eta+142)*N+root := by
    field_simp
    <;> ring
  rw [he] at hpaid
  have hHpay := mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg (α := ℝ) N)
  nlinarith only [hh,hl,hpaid,hHpay,hn]

#print axioms actual_source_pool
#print axioms actual_shared_payment
#print axioms actual_shared_contradiction
end
end JSP233.IntegerShared209
