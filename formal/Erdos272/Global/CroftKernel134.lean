import Erdos272.Core.SmallKernel112
import Erdos272.Global.RootPaid134
import Erdos272.Arithmetic.CroftPrice134
import Erdos272.Counting.APDensity112

/-!
The complete sparse-croft empty-kernel alternative, followed by the actual
original-family density contradiction.  Every Small branch pays the whole
original croft family, including all Large members.  The final common point
is a physical point of Ground N and is transferred back to exactly the
retained r11 crooked members of the same original mixed family.
-/
namespace JSP233.CroftKernel134
open StarCompletion APGeometry PrivateFinset SparseSmall39 DenseDeletion40 Density41
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_whole_uniform {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0<K) (hN : 0<N) (hJ : N<2^J)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,3*K≤S.card) :
    (F.card:ℝ)/(N:ℝ)^2≤CroftPrice134.Whole N J K := by
  have hb := NearFar134.actual_whole_normalized hF hK hN hJ hbad hsize
  have he : NearFar134.Nu K+NearFar134.G N K+NearFar134.Eta N J=
      CroftPrice134.Whole N J K := by
    dsimp [NearFar134.Nu,NearFar134.G,NearFar134.Eta,
      CroftPrice134.Whole,CroftPrice134.Price,CroftPrice134.FarCoefficient,
      CroftPrice134.NuNumerator,CroftPrice134.EtaNumerator]
    ring
  rwa [he] at hb

theorem actual_direct_uniform {N K cut : ℕ} {F : Finset (Finset ℤ)} {T : Finset ℤ}
    (hN : 0<N) (hbound : F.card≤T.card*(3*K)*N) (hcut : T.card≤cut) :
    (F.card:ℝ)/(N:ℝ)^2≤CroftPrice134.Direct N K cut := by
  have hb := hbound.trans (Nat.mul_le_mul_right N (Nat.mul_le_mul_right (3*K) hcut))
  have hbR : (F.card:ℝ)≤(cut:ℝ)*(3*(K:ℝ))*(N:ℝ) := by exact_mod_cast hb
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  have he : CroftPrice134.Direct N K cut*(N:ℝ)^2=(cut:ℝ)*(3*(K:ℝ))*(N:ℝ) := by
    dsimp only [CroftPrice134.Direct,CroftPrice134.Price]
    field_simp [hn.ne']; ring
  rwa [he]

theorem actual_root_uniform {N K J : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 4≤N) (hK : 0<K) (hJ : N<2^J)
    (hF : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hsize : ∀S∈F,11*S.card≤N)
    (hsmall : ∀S∈F,S.card≤3*K→c∈S) (homit : ∃T∈F,c∉T) :
    (F.card:ℝ)/(N:ℝ)^2≤CroftPrice134.Root N J K := by
  have hb := RootPaid134.actual_root_paid_budget hN (by decide : 2≤11) hK hJ
    hF hbad hsize hsmall homit
  norm_num only [Nat.cast_ofNat] at hb
  have hn : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have he : max ((6*(K:ℝ)/N)+(NearFar134.Nu K+NearFar134.G N K))
      ((21/242:ℝ)+(6*(K:ℝ)/N)*(NearFar134.Nu K+NearFar134.G N K)/(21/242:ℝ))+
      NearFar134.Eta N J=CroftPrice134.Root N J K := by
    rw [←max_add_add_right]
    congr 1 <;>
      dsimp [CroftPrice134.Root,CroftPrice134.RootA,CroftPrice134.RootB,
        CroftPrice134.Price,CroftPrice134.FarCoefficient,CroftPrice134.NuNumerator,
        CroftPrice134.EtaNumerator,CroftPrice134.Beta,
        NearFar134.Nu,NearFar134.G,NearFar134.Eta] <;>
      field_simp [hn] <;> ring
  rwa [he] at hb

theorem actual_empty_kernel_bound_of_parameters {N K D cut J : ℕ}
    {F : Finset (Finset ℤ)} (hN : 4≤N) (hJ : N<2^J)
    (hF : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hsize : ∀S∈F,11*S.card≤N) (htwo : 2≤F.card)
    (hkernel : Kernel (Ground N) F=∅)
    (hparam : CroftPrice134.ParameterBudget N J K D cut) :
    (F.card:ℝ)/(N:ℝ)^2≤CroftPrice134.Budget := by
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


theorem actual_log_gates {N : ℕ} (hN : 73967140≤N) (hhi : N≤74320000) :
    Nat.log 2 N+1=27 ∧ N<2^27 := by
  have hn : N≠0 := by omega
  have hl : 26≤Nat.log 2 N := (Nat.le_log_iff_pow_le (by decide : 1<2) hn).mpr
    ((by norm_num : (2:ℕ)^26≤73967140).trans hN)
  have hu : N<2^27 := by norm_num; omega
  have hlog := Nat.log_lt_of_lt_pow hn hu
  exact ⟨by omega,hu⟩

theorem actual_sparse_density_gt {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 73967140≤N) (hhi : N≤74320000) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) :
    CroftPrice134.Budget<((SparseCrooked N 11 F).card:ℝ)/(N:ℝ)^2 := by
  have hNJ := (actual_log_gates hN hhi).2
  have hd := APDensity112.actual_sparse_density11_normalized
    (by omega : 10185≤N) (by norm_num : 4≤27) hNJ hF hcard
  norm_num at hd
  have hnR : (73967140:ℝ)≤N := by exact_mod_cast hN
  have he : (514:ℝ)/N≤514/73967140 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hb : CroftPrice134.Budget<(71/800:ℝ)-514/73967140 := by
    norm_num [CroftPrice134.Budget]
  linarith only [hd,he,hb]

theorem actual_sparse_card_two {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 73967140≤N) (hhi : N≤74320000) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) : 2≤(SparseCrooked N 11 F).card := by
  have hd := actual_sparse_density_gt hN hhi hF hcard
  have hn : (73967140:ℝ)≤N := by exact_mod_cast hN
  have hnp : (0:ℝ)<N := by linarith only [hn]
  have hc := (lt_div_iff₀ (sq_pos_of_pos hnp)).mp hd
  have hsq : (73967140:ℝ)^2≤(N:ℝ)^2 :=
    (sq_le_sq₀ (by norm_num) (Nat.cast_nonneg N)).mpr hn
  by_contra hh
  have hl : ((SparseCrooked N 11 F).card:ℝ)≤1 := by
    exact_mod_cast (by omega : (SparseCrooked N 11 F).card≤1)
  norm_num [CroftPrice134.Budget] at hc
  nlinarith only [hc,hsq,hl]

theorem actual_sparse_kernel_nonempty {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 73967140≤N) (hhi : N≤74320000) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) : (Kernel (Ground N) (SparseCrooked N 11 F)).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  have hNJ := (actual_log_gates hN hhi).2
  obtain ⟨K,D,cut,hparam⟩ := CroftPrice134.actual_parameters hN hhi
  have hb := actual_empty_kernel_bound_of_parameters (by omega : 4≤N) hNJ
    (actual_sparse_legal hF) (fun S hS=>(actual_sparse_membership.mp hS).2.1)
    (fun S hS=>(actual_sparse_membership.mp hS).2.2)
    (actual_sparse_card_two hN hhi hF hcard) he hparam
  have hd := actual_sparse_density_gt hN hhi hF hcard
  linarith only [hb,hd]

theorem actual_original_root11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 73967140≤N) (hhi : N≤74320000) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) :
    ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S := by
  obtain ⟨c,hc⟩ := actual_sparse_kernel_nonempty hN hhi hF hcard
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
end JSP233.CroftKernel134
