module

public import Erdos272.Arithmetic.N40000.CutoffsFrom60
public import Erdos272.Arithmetic.N40000.CutoffsFrom70
public import Erdos272.Arithmetic.N40000.CutoffsFrom74
public import Erdos272.Arithmetic.N40000.CutoffsFrom77
public import Erdos272.Arithmetic.N40000.CutoffsFrom83
public import Erdos272.Arithmetic.N40000.CutoffsFrom91
public import Erdos272.Global.N65172.Global65172

@[expose] public section
namespace JSP233.Global40000
open StarCompletion FirstSparseCut20258 ConcentratedBands20258 Concentrated40000 EndpointCover20258
set_option autoImplicit false

private def bands := [band60,band64,band67,band69,band70,band71,band72,band73,band74,band75,band76,band77,band79,band83,band91,band111,band450]

private theorem paid : ∀ b∈bands,b.Layout 40000 65171 ∧ ∀ r∈b.runs,r.Valid b.lower b.upper := by
  intro b hb
  simp only [bands,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact band60_valid
  · exact band64_valid
  · exact band67_valid
  · exact band69_valid
  · exact band70_valid
  · exact band71_valid
  · exact band72_valid
  · exact band73_valid
  · exact band74_valid
  · exact band75_valid
  · exact band76_valid
  · exact band77_valid
  · exact band79_valid
  · exact band83_valid
  · exact band91_valid
  · exact band111_valid
  · exact band450_valid

/-- The integer ranges in the table cover both the first sparse cutoff and
the physical ground. Small cutoffs use their own witnessing member. -/
theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (lo : 40000≤N) (legal : Legal (Ground N) F) : F.card≤B N := by
  by_cases high : 65172≤N
  · exact Global65172.actual_original_upper_bound high legal
  by_contra! counter
  obtain ⟨m,c,T,cut⟩ := extract (by omega) (by omega) legal counter
  have sparse := cut.sparse
  by_cases small : m≤59
  · have square := Nat.mul_le_mul (Nat.sub_le_sub_right small 1) small
    exact (not_lt_of_ge (FortyFourFamily20258.of_member (by omega) (by omega) legal
      (Density41.actual_sparse_membership.mp cut.omitter).1 cut.crooked (by rw [cut.size]; omega))) counter
  have asc : increasing 60 5500 (bands.map Band.upper)=true := by decide +kernel
  obtain ⟨p,hp,l,u,_⟩ := locate _ asc (by omega : 60≤m) (by omega)
  have stored : ∀ p∈rows 60 (bands.map Band.upper),∃ b∈bands,b.lower=p.1 ∧ b.upper=p.2 := by decide +kernel
  obtain ⟨b,hb,left,right⟩ := stored p hp
  exact (not_lt_of_ge (ConcentratedBands20258.upper lo (by omega : N≤65171)
    (left ▸ l) (right ▸ u) legal cut (paid b hb).1 (paid b hb).2 (by omega))) counter

theorem actual_value_eq_B (N : ℕ) (lo : 40000≤N) : ExtremalValue45.Value N=B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  exact fun F legal => actual_original_upper_bound lo legal

theorem actual_optimal_family (N : ℕ) (lo : 40000≤N) :
    ∃ F : Finset (Finset ℤ), Legal (Ground N) F ∧ F.card=B N ∧
      ∀ G : Finset (Finset ℤ), Legal (Ground N) G → G.card≤F.card := by
  obtain ⟨F,hF,card⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F,hF,card,fun G hG => by simpa only [card] using actual_original_upper_bound lo hG⟩

#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end JSP233.Global40000
