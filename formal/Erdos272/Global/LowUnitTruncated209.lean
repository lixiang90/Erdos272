module

public import Erdos272.Global.TruncatedGlobal209
public import Erdos272.Resources.UnitTruncatedFamily209
public import Erdos272.Arithmetic.TruncatedUnitPrices209
public import Erdos272.Global.RobustGlobalWindow209

@[expose] public section

namespace JSP233.LowUnitTruncated209
open StarCompletion APGeometry DenseDeletion40 Density41
open SevenFamily208 SevenPrices208 ActualUnitFees208
open TruncatedUnitPrices209
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 200000

theorem actual_fees {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhi : N≤705097) (hF : Legal (Ground N) F)
    (hrows : ∀k,k<150→Facts242 k) :
    TruncatedGlobal209.NearFees N (SparseCrooked N 11 F) G U Eta Light := by
  intro A hAG hsize
  have hAF:=hAG.trans (actual_sparse_subset N 11 F)
  have hlegal : Legal (Ground N) A :=
    ⟨fun S hS=>hF.1 S (hAF hS),fun S hS T hT hne=>hF.2 S (hAF hS) T (hAF hT) hne⟩
  exact UnitTruncatedFamily209.actual_paid150 hN hhi hlegal
    (fun S hS=>(actual_sparse_membership.mp (hAG hS)).2.1) hsize
    (fun S hS=>(actual_sparse_membership.mp (hAG hS)).2.2)
    hrows TruncatedUnitPrices209.nonneg.1 reciprocal (weighted_upper150 N)

theorem actual_price_weak {N : ℕ} (hN : 659912≤N) (hhi : N≤705097) :
    ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*G) U
      (Eta+968+Loss) (-Light) N≤(71/800 : ℝ) := by
  have hp:=(TruncatedUnitPrices209.actual_price hN hhi).2
  have hc : (Eta+968+Loss)/(N : ℝ)≤(Eta+142+968)/(N : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    norm_num [Loss,Eta]
  simp only [ReciprocalPrice208.Price,neg_div,sub_neg_eq_add]
  linarith only [hc,hp]

/-- The original-family lower window needs only the first 150 genuine
unit242 cleanup facts. No unit243, uniform fee or geometry oracle is used. -/
theorem actual_original_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhi : N≤705097) (hF : Legal (Ground N) F)
    (hrows : ∀k,k<150→Facts242 k) : F.card≤B N :=
  TruncatedGlobal209.actual_original_upper hN hhi hF
    TruncatedUnitPrices209.nonneg.1 (actual_fees hN hhi hF hrows)
    (TruncatedUnitPrices209.actual_price hN hhi).1 (actual_price_weak hN hhi)

/-- The 150 actual finite facts are the sole extra certificate inputs in
the entire finite interval; all eleven higher integer windows are closed. -/
theorem actual_joined_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhi : N≤62443451) (hF : Legal (Ground N) F)
    (hrows : ∀k,k<150→Facts242 k) : F.card≤B N := by
  by_cases hs : N≤705097
  · exact actual_original_upper hN hs hF hrows
  · exact RobustGlobalWindow209.actual_integer_cover_upper (by omega) hhi hF

#print axioms actual_fees
#print axioms actual_price_weak
#print axioms actual_original_upper
#print axioms actual_joined_upper
end
end JSP233.LowUnitTruncated209
