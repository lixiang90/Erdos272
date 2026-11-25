module

public import Erdos272.Arithmetic.N20258.Ranges.Cut46
public import Erdos272.Arithmetic.N20258.Ranges.Cut47
public import Erdos272.Arithmetic.N20258.Ranges.Cut48
public import Erdos272.Arithmetic.N20258.Ranges.Cut49
public import Erdos272.Arithmetic.N20258.Ranges.Cut50
public import Erdos272.Arithmetic.N20258.Ranges.Cut51
public import Erdos272.Arithmetic.N20258.Ranges.Cut52
public import Erdos272.Arithmetic.N20258.Ranges.Cut53
public import Erdos272.Arithmetic.N20258.Ranges.Cut54
public import Erdos272.Arithmetic.N20258.Ranges.Cut55
public import Erdos272.Arithmetic.N20258.Ranges.Cut56
public import Erdos272.Arithmetic.N20258.Ranges.Cut57
public import Erdos272.Arithmetic.N20258.Ranges.Cut58
public import Erdos272.Arithmetic.N20258.Ranges.Cut59
public import Erdos272.Arithmetic.N20258.Ranges.Cut60
public import Erdos272.Arithmetic.N20258.Ranges.Cut61
public import Erdos272.Arithmetic.N20258.Ranges.Cut62
public import Erdos272.Arithmetic.N20258.Ranges.Cut63
public import Erdos272.Arithmetic.N20258.Ranges.Cut64
public import Erdos272.Arithmetic.N20258.Ranges.Cut65
public import Erdos272.Arithmetic.N20258.Ranges.Cut66
public import Erdos272.Arithmetic.N20258.Ranges.Cut67
public import Erdos272.Arithmetic.N20258.Ranges.Cut68
public import Erdos272.Arithmetic.N20258.Ranges.Cut69
public import Erdos272.Arithmetic.N20258.Ranges.Cut70
public import Erdos272.Arithmetic.N20258.Ranges.Cut71
public import Erdos272.Arithmetic.N20258.Ranges.Cut72
public import Erdos272.Arithmetic.N20258.Ranges.Cut73
public import Erdos272.Arithmetic.N20258.Ranges.Cut74
public import Erdos272.Arithmetic.N20258.Ranges.Cut75
public import Erdos272.Arithmetic.N20258.LargeCuts.From76
public import Erdos272.Arithmetic.N20258.LargeCuts.From78
public import Erdos272.Arithmetic.N20258.LargeCuts.From81
public import Erdos272.Arithmetic.N20258.LargeCuts.From85
public import Erdos272.Arithmetic.N20258.LargeCuts.From91
public import Erdos272.Arithmetic.N20258.LargeCuts.From111
public import Erdos272.Arithmetic.N20258.LargeCuts.From450
public import Erdos272.Global.N20258.ConcentratedFortyFive20258
public import Erdos272.Global.N40000.Global40000

@[expose] public section
namespace JSP233.Global20258
open StarCompletion FirstSparseCut20258 PopulationRanges20258 FiniteCutRanges20258 ConcentratedBands20258 LargeCuts20258 EndpointCover20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private def bands := [band76,band78,band81,band85,band91,band111,band450]

private theorem large : ∀ b∈bands,b.Layout 20258 39999 ∧ ∀ r∈b.runs,r.Valid b.lower b.upper := by
  intro b hb
  simp only [bands,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact band76_valid
  · exact band78_valid
  · exact band81_valid
  · exact band85_valid
  · exact band91_valid
  · exact band111_valid
  · exact band450_valid

private theorem middle (m : ℕ) (lo : 46≤m) (hi : m≤75) : Win m 20258 39999 := by
  interval_cases m
  · exact cut46
  · exact cut47
  · exact cut48
  · exact cut49
  · exact cut50
  · exact cut51
  · exact cut52
  · exact cut53
  · exact cut54
  · exact cut55
  · exact cut56
  · exact cut57
  · exact cut58
  · exact cut59
  · exact cut60
  · exact cut61
  · exact cut62
  · exact cut63
  · exact cut64
  · exact cut65
  · exact cut66
  · exact cut67
  · exact cut68
  · exact cut69
  · exact cut70
  · exact cut71
  · exact cut72
  · exact cut73
  · exact cut74
  · exact cut75

/-- At the first sparse cutoff, compare the actual ground and, if needed,
the number of crooked members with the certified interval endpoints. -/
theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (lo : 20258≤N) (legal : Legal (Ground N) F) : F.card≤B N := by
  by_cases high : 40000≤N
  · exact Global40000.actual_original_upper_bound high legal
  by_contra! counter
  obtain ⟨m,c,T,cut⟩ := extract (by omega) (by omega) legal counter
  have sparse := cut.sparse
  by_cases small : m≤45
  · apply (not_lt_of_ge (ConcentratedFortyFive20258.actual lo legal ?_)) counter
    intro z hz
    obtain ⟨S,mem,miss,sz⟩ := cut.crooked z hz
    exact ⟨S,mem,miss,sz.trans small⟩
  by_cases tight : m≤75
  · exact (not_lt_of_ge (middle m (by omega) tight lo (by omega) legal cut)) counter
  have asc : increasing 76 3400 (bands.map Band.upper)=true := by decide +kernel
  obtain ⟨p,hp,l,u,_⟩ := locate _ asc (by omega : 76≤m) (by omega)
  have row_match : ∀ p∈rows 76 (bands.map Band.upper),∃ b∈bands,b.lower=p.1 ∧ b.upper=p.2 := by decide +kernel
  obtain ⟨b,hb,left,right⟩ := row_match p hp
  have lower : b.lower ≤ m := by rw [left]; exact l
  have upper : m ≤ b.upper := by rw [right]; exact u
  exact (not_lt_of_ge (ConcentratedBands20258.upper (b := b) lo (by omega : N≤39999)
    lower upper legal cut (large b hb).1 (large b hb).2 (by omega))) counter

theorem actual_value_eq_B (N : ℕ) (lo : 20258≤N) : ExtremalValue45.Value N=B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  exact fun F legal => actual_original_upper_bound lo legal

theorem actual_optimal_family (N : ℕ) (lo : 20258≤N) :
    ∃ F : Finset (Finset ℤ), Legal (Ground N) F ∧ F.card=B N ∧
      ∀ G : Finset (Finset ℤ), Legal (Ground N) G → G.card≤F.card := by
  obtain ⟨F,hF,card⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F,hF,card,fun G hG => by simpa only [card] using actual_original_upper_bound lo hG⟩

#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end JSP233.Global20258
