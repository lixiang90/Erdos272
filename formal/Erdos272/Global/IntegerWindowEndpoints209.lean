import Erdos272.Global.IntegerHighRoot209

namespace JSP233.IntegerWindowEndpoints209
open StarCompletion APGeometry Density41 SparseSmall39 SevenFamily208 PrivateFinset
open IntegerHighPrices209
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 200000

theorem cover {N : ℕ} (hlo : 705098≤N) (hhi : N≤62443451) :
    ∃w : Fin 11,Lower w≤N ∧ N≤Upper w := by
  by_cases h0 : N≤727351
  · refine ⟨0,?_,?_⟩ <;> norm_num [Lower,Upper] <;> omega
  by_cases h1 : N≤762585
  · refine ⟨1,?_,?_⟩ <;> norm_num [Lower,Upper] <;> omega
  by_cases h2 : N≤813981
  · refine ⟨2,?_,?_⟩ <;> norm_num [Lower,Upper] <;> omega
  by_cases h3 : N≤902923
  · refine ⟨3,?_,?_⟩ <;> norm_num [Lower,Upper] <;> omega
  by_cases h4 : N≤1054723
  · refine ⟨4,?_,?_⟩ <;> norm_num [Lower,Upper] <;> omega
  by_cases h5 : N≤1328903
  · refine ⟨5,?_,?_⟩ <;> norm_num [Lower,Upper] <;> omega
  by_cases h6 : N≤1890795
  · refine ⟨6,?_,?_⟩ <;> norm_num [Lower,Upper] <;> omega
  by_cases h7 : N≤3200816
  · refine ⟨7,?_,?_⟩ <;> norm_num [Lower,Upper] <;> omega
  by_cases h8 : N≤7055374
  · refine ⟨8,?_,?_⟩ <;> norm_num [Lower,Upper] <;> omega
  by_cases h9 : N≤23102619
  · refine ⟨9,?_,?_⟩ <;> norm_num [Lower,Upper] <;> omega
  refine ⟨10,?_,?_⟩ <;> norm_num [Lower,Upper] <;> omega

theorem cover_with_old {N : ℕ} (hhi : N≤62443451) :
    N≤705097 ∨ ∃w : Fin 11,Lower w≤N ∧ N≤Upper w := by
  by_cases hs : N≤705097
  · exact Or.inl hs
  · exact Or.inr (cover (by omega) hhi)

theorem actual_coarse_small_payment {N M : ℕ} {G : Finset (Finset ℤ)} {T : Finset ℤ}
    (hG : Legal (Ground N) G) (hbad : ∀S∈G,¬IsAP S) (htwo : 2≤G.card)
    (hT : T∈G) (hsize : T.card<M) (hkernel : Kernel (Ground N) (Small G (M-1))=∅) :
    G.card≤(M-1)^2*N := by
  have hn:=actual_member_nonempty_of_two hG htwo hT
  have hb:=actual_small_empty_kernel_direct hG hbad hT hn hkernel
  calc
    G.card≤T.card*((M-1)*N) := by simpa only [Nat.mul_assoc] using hb
    _≤(M-1)*((M-1)*N) := Nat.mul_le_mul_right _ (by omega : T.card≤M-1)
    _=(M-1)^2*N := by ring

/-- The direct small-kernel branch uses the same actual sparse family and
the independently proved 142N density loss. -/
theorem actual_small_contradiction {N : ℕ} {F : Finset (Finset ℤ)} {T : Finset ℤ}
    (w : Fin 11) (hlo : Lower w≤N) (hhi : N≤Upper w)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hT : T∈SparseCrooked N 11 F) (hsize : T.card<M w)
    (hkernel : Kernel (Ground N) (Small (SparseCrooked N 11 F) (M w-1))=∅) : False := by
  have hw:=data_range w
  have hloN:=hw.2.1.trans hlo
  have hhiN:=hhi.trans hw.2.2.1
  have hG:=actual_sparse_legal (r := 11) hF
  have hbad : ∀S∈SparseCrooked N 11 F,¬IsAP S := fun S hS=>(actual_sparse_membership.mp hS).2.1
  have htwo:=IntegerHighRoot209.actual_sparse_two hloN hhiN hF hcard
  have hb:=actual_coarse_small_payment hG hbad htwo hT hsize hkernel
  have hd:=IntegerHighRoot209.actual_sparse_density (by omega : 10902≤N) hhiN hF hcard
  have hbR : ((SparseCrooked N 11 F).card : ℝ)≤(((M w-1)^2 : ℕ) : ℝ)*N := by exact_mod_cast hb
  have hn : (705098 : ℝ)≤N := by exact_mod_cast hloN
  have hn0 : (0 : ℝ)<N := by linarith only [hn]
  have hnum : 800*((M w-1)^2+142)<71*N :=
    (direct_budget w).trans_le (Nat.mul_le_mul_left 71 hlo)
  have hnumR : 800*((((M w-1)^2 : ℕ) : ℝ)+142)<71*(N : ℝ) := by exact_mod_cast hnum
  have hp:=mul_lt_mul_of_pos_right hnumR hn0
  nlinarith only [hd,hbR,hp]

#print axioms cover
#print axioms cover_with_old
#print axioms actual_coarse_small_payment
#print axioms actual_small_contradiction
end
end JSP233.IntegerWindowEndpoints209
