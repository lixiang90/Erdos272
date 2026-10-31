import Erdos272.Core.SmallKernel112
import Erdos272.Global.RootPaid113
import Erdos272.Arithmetic.UniformScale113
import Erdos272.Counting.APDensity112

/-!
The complete sparse-croft empty-kernel alternative, followed by the actual
original-family density contradiction.  Every Small branch pays the whole
original croft family, including all Large members.  The final common point
is a physical point of Ground N and is transferred back to exactly the
retained r11 crooked members of the same original mixed family.
-/
namespace JSP233.CroftKernel113
open StarCompletion APGeometry PrivateFinset SparseSmall39 DenseDeletion40 Density41
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_whole_uniform {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0<K) (hN : 0<N) (hJ : N<2^J)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,3*K≤S.card) :
    (F.card:ℝ)/(N:ℝ)^2≤UniformScale113.whole N J K := by
  have hb := NearFarJoint113.actual_whole_normalized hF hK hN hJ hbad hsize
  have he : NearFarJoint113.Nu K+NearFarJoint113.G N K+NearFarJoint113.Eta N J=
      UniformScale113.whole N J K := by rfl
  rwa [he] at hb

theorem actual_direct_uniform {N K cut : ℕ} {F : Finset (Finset ℤ)} {T : Finset ℤ}
    (hN : 0<N) (hbound : F.card≤T.card*(3*K)*N) (hcut : T.card≤cut) :
    (F.card:ℝ)/(N:ℝ)^2≤UniformScale113.direct N K cut := by
  have hb := hbound.trans (Nat.mul_le_mul_right N (Nat.mul_le_mul_right (3*K) hcut))
  have hbR : (F.card:ℝ)≤(cut:ℝ)*(3*(K:ℝ))*(N:ℝ) := by exact_mod_cast hb
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  have he : UniformScale113.direct N K cut*(N:ℝ)^2=(cut:ℝ)*(3*(K:ℝ))*(N:ℝ) := by
    dsimp only [UniformScale113.direct]
    field_simp [hn.ne']
  rwa [he]

theorem actual_root_uniform {N K J : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 4≤N) (hK : 0<K) (hJ : N<2^J)
    (hF : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hsize : ∀S∈F,11*S.card≤N)
    (hsmall : ∀S∈F,S.card≤3*K→c∈S) (homit : ∃T∈F,c∉T) :
    (F.card:ℝ)/(N:ℝ)^2≤UniformScale113.root N J K := by
  have hb := RootPaid113.actual_root_paid_budget hN (by decide : 2≤11) hK hJ
    hF hbad hsize hsmall homit
  norm_num only [Nat.cast_ofNat] at hb
  have hnu : NearFarJoint113.Nu K=UniformScale113.Nu K := rfl
  have hg : NearFarJoint113.G N K=UniformScale113.G N K := rfl
  have he : NearFarJoint113.Eta N J=UniformScale113.Eta N J := rfl
  simpa only [hnu,hg,he,UniformScale113.root,UniformScale113.rootA,
    UniformScale113.beta,add_assoc] using hb

theorem actual_empty_kernel_bound_of_parameters {N K D cut J : ℕ}
    {F : Finset (Finset ℤ)} (hN : 4≤N) (hJ : N<2^J)
    (hF : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hsize : ∀S∈F,11*S.card≤N) (htwo : 2≤F.card)
    (hkernel : Kernel (Ground N) F=∅)
    (hparam : UniformScale113.ParameterBudget N J K D cut) :
    (F.card:ℝ)/(N:ℝ)^2≤UniformScale113.budget := by
  obtain ⟨hD,hDK,hDC,_hcutK,_hKN,hDirect,hWholeK,hWholeD,hRoot⟩ := hparam
  have hK : 0<K := by omega
  have hn : 0<N := by omega
  by_cases hSmall : SmallKernel112.Small F (3*K)=∅
  · have hlow : ∀S∈F,3*K≤S.card := by
      intro S hS
      by_contra hh
      have hm : S∈SmallKernel112.Small F (3*K) := Finset.mem_filter.mpr ⟨hS,by omega⟩
      rw [hSmall] at hm
      exact Finset.notMem_empty S hm
    exact (actual_whole_uniform hF hK hn hJ hbad hlow).trans hWholeK
  · by_cases hSmallKernel : Kernel (Ground N) (SmallKernel112.Small F (3*K))=∅
    · obtain ⟨T,hTF,_hTpos,hmin,hbound⟩ :=
        SmallKernel112.actual_minimum_member_with_direct hF hbad htwo hSmallKernel
      by_cases hcut : T.card≤cut
      · exact (actual_direct_uniform hn hbound hcut).trans hDirect
      · have hlow : ∀S∈F,3*D≤S.card := by
          intro S hS
          have hm := hmin S hS
          omega
        exact (actual_whole_uniform hF (by omega : 0<D) hn hJ hbad hlow).trans hWholeD
    · obtain ⟨c,hc⟩ := Finset.nonempty_iff_ne_empty.mpr hSmallKernel
      obtain ⟨hcN,hcSmall⟩ := Finset.mem_filter.mp hc
      have hsmall : ∀S∈F,S.card≤3*K→c∈S := by
        intro S hS hs
        exact hcSmall S (Finset.mem_filter.mpr ⟨hS,hs⟩)
      have homit := actual_omitter_of_empty_kernel hkernel c hcN
      exact (actual_root_uniform hN hK hJ hF hbad hsize hsmall homit).trans hRoot

theorem actual_log_gates {N : ℕ} (hN : 74320000≤N) (hNu : N<2^49) :
    let J := Nat.log 2 N+1
    4≤J ∧ J≤49 ∧ N<2^J := by
  have hn : N≠0 := by omega
  have hl : 3≤Nat.log 2 N := (Nat.le_log_iff_pow_le (by decide : 1<2) hn).mpr
    ((by norm_num : (2:ℕ)^3≤74320000).trans hN)
  have hu : Nat.log 2 N<49 := Nat.log_lt_of_lt_pow hn hNu
  exact ⟨by omega,by omega,Nat.lt_pow_succ_log_self (by decide : 1<2) N⟩

theorem actual_sparse_density_gt {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 74320000≤N) (hNu : N<2^49) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) :
    UniformScale113.budget<((SparseCrooked N 11 F).card:ℝ)/(N:ℝ)^2 := by
  let J := Nat.log 2 N+1
  obtain ⟨hJl,hJu,hNJ⟩ := actual_log_gates hN hNu
  have hd := APDensity112.actual_sparse_density11_normalized
    (by omega : 10185≤N) hJl hNJ hF hcard
  change (71/800:ℝ)-((487:ℝ)+J)/N≤
    ((SparseCrooked N 11 F).card:ℝ)/(N:ℝ)^2 at hd
  have hm := UniformScale113.conservative_density_margin hN hJu
  linarith only [hd,hm]

theorem actual_sparse_card_two {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 74320000≤N) (hNu : N<2^49) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) : 2≤(SparseCrooked N 11 F).card := by
  have hd := actual_sparse_density_gt hN hNu hF hcard
  have hn : (74320000:ℝ)≤N := by exact_mod_cast hN
  have hnp : (0:ℝ)<N := by linarith only [hn]
  have hc := (lt_div_iff₀ (sq_pos_of_pos hnp)).mp hd
  have hsq : (74320000:ℝ)^2≤(N:ℝ)^2 :=
    (sq_le_sq₀ (by norm_num) (Nat.cast_nonneg N)).mpr hn
  by_contra hh
  have hl : ((SparseCrooked N 11 F).card:ℝ)≤1 := by
    exact_mod_cast (by omega : (SparseCrooked N 11 F).card≤1)
  norm_num [UniformScale113.budget] at hc
  nlinarith only [hc,hsq,hl]

theorem actual_sparse_kernel_nonempty {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 74320000≤N) (hNu : N<2^49) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) : (Kernel (Ground N) (SparseCrooked N 11 F)).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  let J := Nat.log 2 N+1
  obtain ⟨_hJl,hJu,hNJ⟩ := actual_log_gates hN hNu
  obtain ⟨K,D,cut,hparam⟩ := UniformScale113.exists_uniform_parameters hN hJu
  have hb := actual_empty_kernel_bound_of_parameters (by omega : 4≤N) hNJ
    (actual_sparse_legal hF) (fun S hS=>(actual_sparse_membership.mp hS).2.1)
    (fun S hS=>(actual_sparse_membership.mp hS).2.2)
    (actual_sparse_card_two hN hNu hF hcard) he hparam
  have hd := actual_sparse_density_gt hN hNu hF hcard
  linarith only [hb,hd]

theorem actual_original_root11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 74320000≤N) (hNu : N<2^49) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) :
    ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S := by
  obtain ⟨c,hc⟩ := actual_sparse_kernel_nonempty hN hNu hF hcard
  obtain ⟨hcN,hroot⟩ := Finset.mem_filter.mp hc
  exact ⟨c,hcN,fun S hS hbad=>hroot S (Finset.mem_filter.mpr ⟨hS,hbad⟩)⟩

#print axioms actual_whole_uniform
#print axioms actual_direct_uniform
#print axioms actual_root_uniform
#print axioms actual_empty_kernel_bound_of_parameters
#print axioms actual_log_gates
#print axioms actual_sparse_density_gt
#print axioms actual_sparse_card_two
#print axioms actual_sparse_kernel_nonempty
#print axioms actual_original_root11
end
end JSP233.CroftKernel113
