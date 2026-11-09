module

public import Erdos272.Resources.Unit240Aggregate218
public import Erdos272.Global.Common240216

@[expose] public section

namespace JSP233.PaddedUnit240218
open StarCompletion APGeometry Density41
open SevenFamily208 SevenPrices208 Unit240Rows218 Unit240Aggregate218
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_paid {N : ℕ} {A : Finset (Finset ℤ)}
    (hhi : N≤659912) (hlegal : Legal (Ground N) A)
    (hbad : ∀S∈A,¬IsAP S) (hsize : ∀S∈A,240≤S.card)
    (hsparse : ∀S∈A,11*S.card≤N) :
    UnitNearObligation N A G 0 0 Fee := by
  obtain ⟨psi,cap,hmono,hzero,hrecip,hpaid⟩ := actual_paid_pad
    (PaddedUnit212.legal_mono hhi hlegal) hbad hsize
    (fun S hS=>(hsparse S hS).trans hhi)
  refine ⟨psi,cap,hmono,hzero,hrecip,?_⟩
  simpa only [zero_mul,zero_add] using hpaid

theorem actual_fees {N : ℕ} {F : Finset (Finset ℤ)}
    (hhi : N≤659912) (hF : Legal (Ground N) F) :
    Common240216.NearFees N 240 (SparseCrooked N 11 F) G 0 0 Fee := by
  intro A hAG hsize
  have hAF := hAG.trans (actual_sparse_subset N 11 F)
  have hlegal : Legal (Ground N) A :=
    ⟨fun S hS=>hF.1 S (hAF hS),fun S hS T hT hne=>hF.2 S (hAF hS) T (hAF hT) hne⟩
  exact actual_paid hhi hlegal
    (fun S hS=>(actual_sparse_membership.mp (hAG hS)).2.1) hsize
    (fun S hS=>(actual_sparse_membership.mp (hAG hS)).2.2)

theorem actual_price {N : ℕ} (hlo : 642498≤N) (hhi : N≤653292) :
    G*(N : ℝ)≤TruncatedAPResponse209.T ∧
    ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*G) 0
      (968+Loss) (-Fee) N≤(71/800 : ℝ) := by
  have hl : (642498 : ℝ)≤N := by exact_mod_cast hlo
  have hh : (N : ℝ)≤653292 := by exact_mod_cast hhi
  constructor
  · norm_num [G,TruncatedAPResponse209.T]
    linarith only [hh]
  · exact ReciprocalPrice208.window (lo := 642498) (hi := 653292)
      (by norm_num) hl hh (by norm_num [Loss])
      (by norm_num [Fee,Loss])
      (by norm_num [ReciprocalPrice208.Price,TruncatedAPResponse209.Kappa,G,Fee,Loss])
      (by norm_num [ReciprocalPrice208.Price,TruncatedAPResponse209.Kappa,G,Fee,Loss])

#print axioms actual_paid
#print axioms actual_fees
#print axioms actual_price
end
end JSP233.PaddedUnit240218
