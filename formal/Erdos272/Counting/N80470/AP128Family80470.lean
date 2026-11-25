module

public import Erdos272.Counting.N80470.APQuotient80470
public import Erdos272.Counting.N158375.DenseJoint158375

@[expose] public section

namespace JSP233.AP128Family80470
open StarCompletion APGeometry DenseDeletion40 IntrinsicTriples208 HarmonicAbel29
open APShadowCapacity16858 UnitShadowGeometry291012 APQuotient80470
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Kappa : ℝ := 100771/625000
def A : ℝ := 257021/625000
def Nu : ℝ := 1851/1000
def C : ℝ := 50945/8

-- The universal analytic theorem must construct this proposition for every
-- n≥16512. Its fixed sums have 64/128/129 terms; no actual family enters it.
def TailCertificate (n : ℕ) : Prop :=
  Tail n≤Kappa*(n : ℝ)^2+(n : ℝ)*(Harmonic n-1)-Nu*n+C

def Response (g n : ℝ) (h : ℝ) : ℝ :=
  Kappa*n^2+g*n^3+1/(432*g^2)+n*h-Nu*n+C+1

def Flat (n : ℕ) : ℝ :=
  A*(n : ℝ)^2+(n : ℝ)*Harmonic n-Nu*n+C+1

theorem actual_unit_pool {N : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hN : 2≤N) (hg : 0<g) (hF : Legal (Ground N) F) :
    ((UnitCount218.UnitAP F).card : ℝ)+6*g*(∑ S∈F, ((Pool S).card : ℝ))≤
      g*((N-1 : ℕ) : ℝ)^3+1/(432*g^2)+(N-1 : ℕ) := by
  obtain ⟨y, hy, _hyN, hu, hshadow⟩ := actual_unit_geometry hF
  have hsub : UnitCount218.UnitAP F⊆F := Finset.filter_subset _ _
  have hAP : ∀ S∈UnitCount218.UnitAP F, IsAP S :=
    fun S hS => (Finset.mem_filter.mp hS).2.1
  have hc := actual_AP_family_capacity hF hsub hAP
  rw [ground_card] at hc
  have hcR : (∑ S∈F, ((Pool S).card : ℝ))+
      ((APShadow (UnitCount218.UnitAP F)).card : ℝ)≤(N.choose 3 : ℝ) := by
    exact_mod_cast hc
  have hncast : ((N-1 : ℕ) : ℝ)=(N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤N), Nat.cast_one]
  have hchoose := APResidual208.cast_choose_three N
  have hcapacity : 6*(∑ S∈F, ((Pool S).card : ℝ))+
      6*((APShadow (UnitCount218.UnitAP F)).card : ℝ)≤
      ((N-1 : ℕ) : ℝ)^3-((N-1 : ℕ) : ℝ) := by
    rw [hncast]
    nlinarith only [hcR, hchoose]
  have hpool : 6*(∑ S∈F, ((Pool S).card : ℝ))≤((N-1 : ℕ) : ℝ)^3-8*y^3 := by
    linarith only [hcapacity, hshadow]
  have hp := mul_le_mul_of_nonneg_left hpool hg.le
  have hmax := ShadowResponse291012.cubic_max hy hg
  nlinarith only [hu, hp, hmax]

theorem actual_joint {N : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hN : 2≤N) (hg : 0<g) (hF : Legal (Ground N) F) (htail : TailCertificate (N-1)) :
    ((F.filter IsAP).card : ℝ)+6*g*(∑ S∈F, ((Pool S).card : ℝ))≤
      Response g ((N-1 : ℕ) : ℝ) (Harmonic (N-1)) := by
  have hu := actual_unit_pool hN hg hF
  have ha := actual_AP_tail_partition hF
  dsimp only [TailCertificate] at htail
  dsimp only [Response]
  nlinarith only [hu, ha, htail]

theorem actual_AP_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (htail : TailCertificate (N-1)) :
    ((F.filter IsAP).card : ℝ)≤Flat (N-1) := by
  obtain ⟨y, _hy, hyN, hu, _hshadow⟩ := actual_unit_geometry hF
  have ha := actual_AP_tail_partition hF
  dsimp only [TailCertificate] at htail
  dsimp only [Flat, A, Kappa] at *
  nlinarith only [hyN, hu, ha, htail]

theorem actual_flat_AP_deleted {N : ℕ} {F : Finset (Finset ℤ)}
    (hlo : 16513≤N) (hhi : N≤179999) (hF : Legal (Ground N) F)
    (htail : TailCertificate (N-1)) :
    ((F.filter IsAP).card : ℝ)+((Deleted N 12 F).card : ℝ)≤Flat (N-1) := by
  have hx : (0 : ℝ)<((N-1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0<N-1 by omega)
  have hcap : ((N-1 : ℕ) : ℝ)≤180200 := by
    exact_mod_cast (show N-1≤180200 by omega)
  have hg : 0<1/(6*((N-1 : ℕ) : ℝ)) := by positivity
  have hpay : 1≤6*(1/(6*((N-1 : ℕ) : ℝ)))*180200 := by
    have he : 6*(1/(6*((N-1 : ℕ) : ℝ)))*180200=180200/((N-1 : ℕ) : ℝ) := by
      field_simp [hx.ne']
      <;> ring
    rw [he]
    exact (le_div_iff₀ hx).mpr (by simpa using hcap)
  have hd := DenseJoint158375.actual_deleted_payment (by omega : 15000≤N)
    (by omega : N≤2^18) hF hg.le hpay
  have hm := SourceFees208.pool_sum_subset (actual_deleted_subset N 12 F)
  have hs := mul_le_mul_of_nonneg_left hm
    (show 0≤6*(1/(6*((N-1 : ℕ) : ℝ))) by positivity)
  have hj := actual_joint (by omega : 2≤N) hg hF htail
  have he : (1/(6*((N-1 : ℕ) : ℝ)))*((N-1 : ℕ) : ℝ)^3+
      1/(432*(1/(6*((N-1 : ℕ) : ℝ)))^2)=(1/4 : ℝ)*((N-1 : ℕ) : ℝ)^2 := by
    field_simp [hx.ne']
    <;> ring
  dsimp only [Response] at hj
  dsimp only [Flat, A, Kappa] at *
  nlinarith only [hd, hs, hj, he]

theorem actual_AP_inner_with_deleted {N : ℕ} {F A0 : Finset (Finset ℤ)} {g Q : ℝ}
    (hlo : 15000≤N) (hhi : N≤2^18) (hF : Legal (Ground N) F)
    (hAF : A0⊆F) (hsparse : ∀ S∈A0, 12*S.card≤N) (hg : 0<g)
    (hpay : 1≤6*g*180200) (htail : TailCertificate (N-1))
    (hinner : (A0.card : ℝ)≤6*g*(∑ S∈A0, ((Pool S).card : ℝ))+Q) :
    ((F.filter IsAP).card : ℝ)+(A0.card : ℝ)+((Deleted N 12 F).card : ℝ)≤
      Response g ((N-1 : ℕ) : ℝ) (Harmonic (N-1))+Q := by
  have hi := DenseJoint158375.actual_inner_payment_with_deleted
    hlo hhi hF hAF hsparse hg.le hpay hinner
  have hj := actual_joint (by omega : 2≤N) hg hF htail
  linarith only [hi, hj]

#print axioms actual_unit_pool
#print axioms actual_joint
#print axioms actual_AP_count
#print axioms actual_flat_AP_deleted
#print axioms actual_AP_inner_with_deleted
end
end JSP233.AP128Family80470
