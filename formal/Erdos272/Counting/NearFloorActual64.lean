module

public import Erdos272.Counting.NearFloorDyadic64
public import Erdos272.Counting.CrossBand57

@[expose] public section

namespace JSP233.NearFloorActual64
open NearFloorAnalytic64 NearFloorDyadic64 HarmonicAbel29
open StarCompletion APGeometry NearAP36
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_crossband_near_quadratic {N L U J : ℕ} {F : Finset (Finset ℤ)}
    (hU : 0<U) (hLU : L=3*U) (hN : N<2^J)
    (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S) :
    ((CrossBand57.NearMembers F L U).card:ℝ)≤
      (6909/200:ℝ)*(N:ℝ)^2/L+(7/2:ℝ)*J^2*N := by
  have hL : 0<L := by rw [hLU];omega
  have hex : ∀S:Finset ℤ,∃j:ℕ,S∈CrossBand57.NearMembers F L U→
      S∈CrossBand57.Band F L j ∧ HasNearAPCore (CrossBand57.Scale U j) S := by
    intro S
    by_cases hs : S∈CrossBand57.NearMembers F L U
    · obtain ⟨_hSF,j,hj⟩ := CrossBand57.actual_near_data hL hs
      exact ⟨j,fun _=>hj⟩
    · exact ⟨0,fun hh=>False.elim (hs hh)⟩
  choose level hl using hex
  have hNF : CrossBand57.NearMembers F L U⊆F :=
    fun S hS=>(CrossBand57.actual_near_data hL hS).1
  have hNL : Legal (Ground N) (CrossBand57.NearMembers F L U) :=
    ⟨fun S hS=>hlegal.1 S (hNF hS),fun S hS T hT he=>hlegal.2 S (hNF hS) T (hNF hT) he⟩
  have hbound := actual_dyadic_near_quadratic level hNL hU hN
    (fun S hS=>hbad S (hNF hS)) (by
      intro S hS
      have hs := (Finset.mem_filter.mp (hl S hS).1).2.1
      dsimp only [CrossBand57.Scale] at hs
      rw [hLU] at hs
      nlinarith only [hs]) (by
      intro S hS
      have hs := (Finset.mem_filter.mp (hl S hS).1).2.2
      dsimp only [CrossBand57.Scale] at hs
      rw [hLU] at hs
      nlinarith only [hs]) (by
      intro S hS
      exact (hl S hS).2)
  have he : (2303/200:ℝ)*(N:ℝ)^2/U=(6909/200:ℝ)*(N:ℝ)^2/L := by
    rw [hLU]
    push_cast
    ring
  rwa [he] at hbound

theorem actual_crossband_near_normalized {N L U J : ℕ} {F : Finset (Finset ℤ)}
    (hU : 0<U) (hLU : L=3*U) (hN : N<2^J) (hpos : 0<N)
    (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S) :
    ((CrossBand57.NearMembers F L U).card:ℝ)/(N:ℝ)^2≤
      (6909/200:ℝ)/L+(7/2:ℝ)*J^2/N := by
  have hh := actual_crossband_near_quadratic hU hLU hN hlegal hbad
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hpos
  have hlp : (0:ℝ)<L := by rw [hLU];positivity
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  have he : ((6909/200:ℝ)/L+(7/2:ℝ)*J^2/N)*(N:ℝ)^2=
      (6909/200:ℝ)*(N:ℝ)^2/L+(7/2:ℝ)*J^2*N := by
    field_simp [hp.ne',hlp.ne']
  rw [he]
  exact hh

#print axioms actual_crossband_near_quadratic
#print axioms actual_crossband_near_normalized
end
end JSP233.NearFloorActual64
