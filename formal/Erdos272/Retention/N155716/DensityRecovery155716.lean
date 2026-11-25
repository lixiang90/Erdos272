module

public import Erdos272.Retention.N158375.DensityRecovery158375

@[expose] public section

namespace JSP233.DensityRecovery155716
open StarCompletion APGeometry APCount41 DenseDeletion40 HarmonicAbel29 WitnessInterval43
open RootModel291012 UnitCount218 PairShadowBudget218 LocalRecovery158375 DensityRecovery158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_omitter_size {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    {tau left v alpha beta constant : ℝ}
    (g : Start N c L R F P T) (hN : 155716 ≤ N) (hhi : N ≤ 179999)
    (hl : (L : ℝ) < left*N) (hw : Width N L R < v*N)
    (he : ((Omitted N c F).card : ℝ) ≤ alpha*N+beta*Width N L R+constant)
    (hg : Gate tau left v alpha beta constant) (htau : tau ≤ 1/2)
    (hUF : U ∈ F) (hbad : ¬IsAP U) (hcU : (c : ℤ) ∉ U) : tau*(N : ℝ) < U.card := by
  by_contra hnot
  have hn : (155000 : ℝ) ≤ N := by exact_mod_cast (show 155000 ≤ N by omega)
  have hNp : (0 : ℝ) < N := by linarith only [hn]
  have hsmall : (U.card : ℝ) ≤ tau*N := le_of_not_gt hnot
  have caps := LocalRecovery158375.actual_caps (by omega : 100000 ≤ N) hhi
  have hcleft : (c : ℝ) ≤ left*N := by
    have hcL : (c : ℝ) < L := by exact_mod_cast g.root_left
    linarith only [hcL, hl]
  have hd := density_strict hn (Nat.cast_nonneg c) hcleft (width_nonnegative g) hw
    caps.harmonic_le he (root_density g (by omega : 1 ≤ N)) hg
  let C := F.filter fun S => ¬IsAP S
  have hCF : C ⊆ F := Finset.filter_subset _ _
  have hCL : Legal (Ground N) C :=
    ⟨fun S hS => g.legal.1 S (hCF hS), fun S hS V hV hSV => g.legal.2 S (hCF hS) V (hCF hV) hSV⟩
  have hCB : ∀ S ∈ C, ¬IsAP S := fun S hS => (Finset.mem_filter.mp hS).2
  have hUC : U ∈ C := Finset.mem_filter.mpr ⟨hUF, hbad⟩
  have hroot : RootPart C (c : ℤ) = RootCrooked F (c : ℤ) := by
    ext S
    simp only [RootPart, C, RootCrooked, Finset.mem_filter]
    tauto
  have hsize : U.card+1 ≤ N := by
    have ht := mul_le_mul_of_nonneg_right htau hNp.le
    have hh : (U.card : ℝ)+1 ≤ N := by linarith only [hsmall, ht, hn]
    exact_mod_cast hh
  have hz : (U.card : ℝ)/(N : ℝ) ≤ tau := (div_le_iff₀ hNp).mpr hsmall
  have hq := RootQuadratic208.actual_normalized_root (by omega : 2 ≤ N) hCL hCB hUC hcU hsize hz
    (by linarith only [htau] : tau ≤ 1)
  rw [hroot] at hq
  have hqR := (div_le_iff₀ (sq_pos_of_pos hNp)).mp hq
  linarith only [hd, hqR]

#print axioms actual_omitter_size
end
end JSP233.DensityRecovery155716
