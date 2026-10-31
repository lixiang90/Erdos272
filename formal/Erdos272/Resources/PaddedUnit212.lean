import Erdos272.Resources.UnitTruncatedFamily209
import Erdos272.Arithmetic.TruncatedUnitPrices209
import Erdos272.Arithmetic.Cap150UnitRowsChecked209

namespace JSP233.PaddedUnit212
open StarCompletion APGeometry Density41
open SevenFamily208 SevenPrices208 UnitNearAggregate208 ActualUnitFees208
open TruncatedUnitPrices209
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def PaddedLight : ℝ := U*(659912 : ℝ)^2+Eta*659912+Light

theorem ground_mono {N M : ℕ} (hNM : N≤M) : Ground N⊆Ground M := by
  intro x hx
  have hx' := (mem_ground N x).mp hx
  apply (mem_ground M x).mpr
  exact ⟨hx'.1,hx'.2.trans (by exact_mod_cast hNM)⟩

theorem legal_mono {N M : ℕ} {A : Finset (Finset ℤ)}
    (hNM : N≤M) (hlegal : Legal (Ground N) A) : Legal (Ground M) A :=
  ⟨fun S hS=>(hlegal.1 S hS).trans (ground_mono hNM),hlegal.2⟩

/-- The family and its intrinsic pool do not change under ground padding.
All 150 finite facts are supplied by the previously checked index. -/
theorem actual_paid {N : ℕ} {A : Finset (Finset ℤ)}
    (hhi : N≤659912) (hlegal : Legal (Ground N) A)
    (hbad : ∀S∈A,¬IsAP S) (hsize : ∀S∈A,242≤S.card)
    (hsparse : ∀S∈A,11*S.card≤N) :
    UnitNearObligation N A G 0 0 PaddedLight := by
  have hp := UnitTruncatedFamily209.actual_paid150 (N := 659912)
    (by decide) (by decide) (legal_mono hhi hlegal) hbad hsize
    (fun S hS=>(hsparse S hS).trans hhi)
    (fun k hk=>Cap150UnitRowsChecked209.checked242 k hk)
    TruncatedUnitPrices209.nonneg.1 reciprocal (weighted_upper150 659912)
  obtain ⟨psi,cap,hmono,hzero,hrecip,hpaid⟩ := hp
  refine ⟨psi,cap,hmono,hzero,hrecip,?_⟩
  simpa only [zero_mul,zero_add,PaddedLight,Nat.cast_ofNat] using hpaid

theorem actual_fees {N : ℕ} {F : Finset (Finset ℤ)}
    (hhi : N≤659912) (hF : Legal (Ground N) F) :
    ∀A⊆SparseCrooked N 11 F,(∀S∈A,242≤S.card)→
      UnitNearObligation N A G 0 0 PaddedLight := by
  intro A hAG hsize
  have hAF := hAG.trans (actual_sparse_subset N 11 F)
  have hlegal : Legal (Ground N) A :=
    ⟨fun S hS=>hF.1 S (hAF hS),fun S hS T hT hne=>hF.2 S (hAF hS) T (hAF hT) hne⟩
  exact actual_paid hhi hlegal
    (fun S hS=>(actual_sparse_membership.mp (hAG hS)).2.1) hsize
    (fun S hS=>(actual_sparse_membership.mp (hAG hS)).2.2)

theorem padded_light_exact : PaddedLight=(68587245575122/3125 : ℝ) := by
  norm_num [PaddedLight,U,Eta,Light]

/-- Continuous budget certificate. This is a source-fee theorem, not the
remaining common-root recovery or a new public extremal theorem. -/
theorem actual_price {N : ℕ} (hlo : 638202≤N) (hhi : N≤659912) :
    G*(N : ℝ)≤TruncatedAPResponse209.T ∧
    ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*G) 0
      (968+Loss) (-PaddedLight) N≤(71/800 : ℝ) := by
  have hl : (638202 : ℝ)≤N := by exact_mod_cast hlo
  have hh : (N : ℝ)≤659912 := by exact_mod_cast hhi
  constructor
  · norm_num [G,TruncatedAPResponse209.T]
    linarith only [hh]
  · exact ReciprocalPrice208.window (lo := 638202) (hi := 659912)
      (by norm_num) hl hh (by norm_num [Loss])
      (by norm_num [PaddedLight,U,Eta,Light,Loss])
      (by norm_num [ReciprocalPrice208.Price,TruncatedAPResponse209.Kappa,G,PaddedLight,U,Eta,Light,Loss])
      (by norm_num [ReciprocalPrice208.Price,TruncatedAPResponse209.Kappa,G,PaddedLight,U,Eta,Light,Loss])

#print axioms ground_mono
#print axioms legal_mono
#print axioms actual_paid
#print axioms actual_fees
#print axioms padded_light_exact
#print axioms actual_price
end
end JSP233.PaddedUnit212
