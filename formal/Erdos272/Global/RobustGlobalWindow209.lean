module

public import Erdos272.Resources.IntegerUniformFees209
public import Erdos272.Global.IntegerGlobalCases209
public import Erdos272.Global.ActualUnitNearWindow208

@[expose] public section

namespace JSP233.RobustGlobalWindow209
open StarCompletion APGeometry Density41
open IntegerHighPrices209
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 200000

theorem actual_fees {N : ℕ} {F : Finset (Finset ℤ)}
    (w : Fin 11) (hN : 2≤N) (hhi : N≤Upper w) (hF : Legal (Ground N) F) :
    IntegerGlobalCases209.NearFees N (M w) (SparseCrooked N 11 F)
      (IntegerRobustPrices209.G w) (IntegerRobustPrices209.U w) (IntegerRobustPrices209.Eta w) := by
  intro A hAG hsize
  have hAF:=hAG.trans (actual_sparse_subset N 11 F)
  have hlegal : Legal (Ground N) A :=
    ⟨fun S hS=>hF.1 S (hAF hS),fun S hS T hT hne=>hF.2 S (hAF hS) T (hAF hT) hne⟩
  exact IntegerUniformFees209.actual_obligation w hN hhi hlegal
    (fun S hS=>(actual_sparse_membership.mp (hAG hS)).2.1) hsize
    (fun S hS=>(actual_sparse_membership.mp (hAG hS)).2.2)

theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)}
    (w : Fin 11) (hlo : Lower w≤N) (hhi : N≤Upper w)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    ∃c∈Ground N,∀S∈DenseDeletion40.Retained N 11 F,¬IsAP S→c∈S := by
  have hd:=data_range w
  have hn : (705098 : ℝ)≤N := by exact_mod_cast (hd.2.1.trans hlo)
  have hn0 : (0 : ℝ)<N := by linarith only [hn]
  have hp:=IntegerRobustPrices209.actual_price w hlo hhi
  have he : SharedUniformStrong209.CoupledShare*IntegerRobustPrices209.G w*(N : ℝ)+IntegerRobustPrices209.U w+
      ((IntegerRobustPrices209.Eta w : ℝ)+142)/(N : ℝ)+(4*(M w : ℝ)*N)/(N : ℝ)^2=
      SharedUniformStrong209.CoupledShare*IntegerRobustPrices209.G w*(N : ℝ)+IntegerRobustPrices209.U w+
        ((IntegerRobustPrices209.Eta w : ℝ)+142+4*(M w : ℝ))/(N : ℝ) := by
    field_simp
    <;> ring
  have hprice : SharedUniformStrong209.CoupledShare*IntegerRobustPrices209.G w*(N : ℝ)+IntegerRobustPrices209.U w+
      ((IntegerRobustPrices209.Eta w : ℝ)+142+4*(M w : ℝ))/(N : ℝ)<(71/800 : ℝ) := by
    have hh:=hp.2
    rwa [he] at hh
  exact IntegerGlobalCases209.actual_common_root w hlo hhi hF hcard
    (IntegerRobustPrices209.numeric w).1.le (actual_fees w (by omega) hhi hF) hp.1 hprice

/-- All four actual alternatives are paid with genuine source-deficiency
families. No near-fee premise remains in these eleven integer windows. -/
theorem actual_original_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (w : Fin 11) (hlo : Lower w≤N) (hhi : N≤Upper w) (hF : Legal (Ground N) F) :
    F.card≤B N := by
  have hd:=data_range w
  by_cases hc : B N≤F.card
  · exact RootedFinite209.actual_original_upper_of_root11 (by omega) (hhi.trans hd.2.2.1) hF
      (actual_common_root w hlo hhi hF hc)
  · omega

theorem actual_integer_cover_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 705098≤N) (hhi : N≤62443451) (hF : Legal (Ground N) F) : F.card≤B N := by
  obtain ⟨w,hl,hu⟩:=IntegerWindowEndpoints209.cover hN hhi
  exact actual_original_upper w hl hu hF

/-- Join to the frozen unit242/243 window. The explicit finite cleanup Facts
belong only to the lower window; the eleven integer windows are unconditional. -/
theorem actual_joined_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhi : N≤62443451) (hF : Legal (Ground N) F)
    (hrows242 : ∀k,k<183→ActualUnitFees208.Facts242 k)
    (hrows243 : ∀k,k<184→ActualUnitFees208.Facts243 k) : F.card≤B N := by
  by_cases hs : N≤705097
  · exact ActualUnitNearWindow208.actual_original_upper hN hs hF hrows242 hrows243
  · exact actual_integer_cover_upper (by omega) hhi hF

#print axioms actual_fees
#print axioms actual_common_root
#print axioms actual_original_upper
#print axioms actual_integer_cover_upper
#print axioms actual_joined_upper
end
end JSP233.RobustGlobalWindow209
