import Erdos272.Resources.ShiftedBlocks208

namespace JSP233.PotentialPhases208
open StarCompletion APGeometry NearAP36 ShiftedBlocks208
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

def Phases (N d k : ℕ) : Finset ℕ := (Finset.Icc 1 d).filter (fun a => a+k*d ≤ N)

theorem phases_eq (N d k : ℕ) : Phases N d k = Finset.Icc 1 (min d (N-k*d)) := by
  ext a
  simp only [Phases,Finset.mem_filter,Finset.mem_Icc,le_min_iff]
  omega

theorem potential_phase_count (N d k : ℕ) : (Phases N d k).card = min d (N-k*d) := by
  rw [phases_eq,Nat.card_Icc]
  omega

theorem code_decomposition {a d B : ℕ} (ha0 : 1 ≤ a) (hB : 0 < B) :
    ∃ i < B, a = (Code d B a).1+1+((Code d B a).2*B+i)*d := by
  obtain ⟨i,hi,ha⟩ := start_decomposition (a := a-1) (d := d) hB
  refine ⟨i,hi,?_⟩
  change a = (StartCode d B (a-1)).1+1+((StartCode d B (a-1)).2*B+i)*d
  omega

theorem actual_code_phase {N a d m A B : ℕ} {S : Finset ℤ}
    (hd : 0 < d) (hB : 0 < B) (hm : A+1 ≤ m)
    (hsub : Grid a d m ⊆ S) (hground : S ⊆ Ground N) :
    (Code d B a).1+1 ∈ Phases N d (A+(Code d B a).2*B) := by
  have haS : (a : ℤ) ∈ S := hsub ((mem_grid _ _ _ _).mpr ⟨0,by omega,by simp⟩)
  have ha0 : 1 ≤ a := by exact_mod_cast ((mem_ground N (a : ℤ)).mp (hground haS)).1
  obtain ⟨i,hi,ha⟩ := code_decomposition (d := d) ha0 hB
  have hxS := hsub ((mem_grid _ _ _ _).mpr ⟨A,by omega,rfl⟩)
  have hxZ := ((mem_ground N ((a : ℤ)+(A : ℤ)*d)).mp (hground hxS)).2
  have hx : a+A*d ≤ N := by exact_mod_cast hxZ
  have hres : (Code d B a).1 < d := Nat.mod_lt _ hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
  nlinarith only [hx,ha]

theorem actual_source_cap {N a d m e E B : ℕ} {S : Finset ℤ}
    (hd : 0 < d) (hB : 0 < B) (hm : 0 < m) (he : e < E)
    (hcard : S.card = m+e) (hsub : Grid a d m ⊆ S) (hground : S ⊆ Ground N) :
    S.card ≤ N/d-(Code d B a).2*B+E := by
  have haS : (a : ℤ) ∈ S := hsub ((mem_grid _ _ _ _).mpr ⟨0,by omega,by simp⟩)
  have ha0 : 1 ≤ a := by exact_mod_cast ((mem_ground N (a : ℤ)).mp (hground haS)).1
  obtain ⟨i,hi,ha⟩ := code_decomposition (d := d) ha0 hB
  have hxS := hsub ((mem_grid _ _ _ _).mpr ⟨m-1,by omega,rfl⟩)
  have hxZ := ((mem_ground N ((a : ℤ)+((m-1 : ℕ) : ℤ)*d)).mp (hground hxS)).2
  have hx : a+(m-1)*d ≤ N := by exact_mod_cast hxZ
  have hprod : ((Code d B a).2*B+(m-1))*d ≤ N := by nlinarith only [hx,ha]
  have hdiv := (Nat.le_div_iff_mul_le hd).mpr hprod
  omega

#print axioms potential_phase_count
#print axioms actual_code_phase
#print axioms actual_source_cap
end
end JSP233.PotentialPhases208
