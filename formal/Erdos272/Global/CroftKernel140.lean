module

public import Erdos272.Core.SmallKernel112
public import Erdos272.Global.RootPaid136
public import Erdos272.Arithmetic.CroftPrice140
public import Erdos272.Counting.APDensity112

@[expose] public section
namespace JSP233.CroftKernel140
open StarCompletion APGeometry PrivateFinset SparseSmall39 DenseDeletion40 Density41
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_whole_uniform {N K:ℕ} {F:Finset (Finset ℤ)}
    (hF:Legal (Ground N) F) (hK:600≤K) (hN:63≤N) (hhi:N≤62911096)
    (hbad:∀S∈F,¬IsAP S) (hupper:∀S∈F,11*S.card≤N) (hlow:∀S∈F,3*K≤S.card) :
    (F.card:ℝ)/(N:ℝ)^2≤CroftPrice140.Whole N K := by
  have hb:=NearFar136.actual_whole_normalized hF hK hN (by omega:N≤74320000) hbad hupper hlow
  have he:NearFar136.Nu K+NearFar136.G N K+NearFar136.Eta N=
      CroftPrice140.Whole N K := by
    dsimp [NearFar136.Nu,NearFar136.G,NearFar136.Eta,
      CroftPrice140.Whole,CroftPrice140.Price,CroftPrice140.FarCoefficient,
      CroftPrice140.NuNumerator,CroftPrice140.EtaNumerator]
    ring
  rwa [he] at hb

theorem actual_direct_uniform {N K cut : ℕ} {F : Finset (Finset ℤ)} {T : Finset ℤ}
    (hN : 0<N) (hbound : F.card≤T.card*(3*K)*N) (hcut : T.card≤cut) :
    (F.card:ℝ)/(N:ℝ)^2≤CroftPrice140.Direct N K cut := by
  have hb := hbound.trans (Nat.mul_le_mul_right N (Nat.mul_le_mul_right (3*K) hcut))
  have hbR : (F.card:ℝ)≤(cut:ℝ)*(3*(K:ℝ))*(N:ℝ) := by exact_mod_cast hb
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  have he : CroftPrice140.Direct N K cut*(N:ℝ)^2=(cut:ℝ)*(3*(K:ℝ))*(N:ℝ) := by
    dsimp only [CroftPrice140.Direct,CroftPrice140.Price]
    field_simp [hn.ne']; ring
  rwa [he]

theorem actual_root_uniform {N K:ℕ} {F:Finset (Finset ℤ)} {c:ℤ}
    (hN:63≤N) (hhi:N≤62911096) (hK:600≤K)
    (hF:Legal (Ground N) F) (hbad:∀S∈F,¬IsAP S) (hsize:∀S∈F,11*S.card≤N)
    (hsmall:∀S∈F,S.card≤3*K→c∈S) (homit:∃T∈F,c∉T) :
    (F.card:ℝ)/(N:ℝ)^2≤CroftPrice140.Root N K := by
  have hb:=RootPaid136.actual_root_paid_budget hN (by omega:N≤74320000) (by decide:11≤11) hK
    hF hbad hsize hsmall homit
  norm_num only [Nat.cast_ofNat] at hb
  have hn:(N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have he:max (6*(K:ℝ)/N+(NearFar136.Nu K+NearFar136.G N K))
      ((21/242:ℝ)+(6*(K:ℝ)/N)*(NearFar136.Nu K+NearFar136.G N K)/(21/242:ℝ))+
      NearFar136.Eta N=CroftPrice140.Root N K := by
    rw [←max_add_add_right]
    congr 1 <;>
      dsimp [CroftPrice140.Root,CroftPrice140.RootA,CroftPrice140.RootB,
        CroftPrice140.Price,CroftPrice140.FarCoefficient,CroftPrice140.NuNumerator,
        CroftPrice140.EtaNumerator,CroftPrice140.Beta,
        NearFar136.Nu,NearFar136.G,NearFar136.Eta] <;>
      field_simp [hn] <;> ring
  rwa [he] at hb

theorem actual_empty_kernel_bound_of_parameters {N K D cut : ℕ}
    {F : Finset (Finset ℤ)} (hN : 63≤N) (hhi : N≤62911096)
    (hF : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hsize : ∀S∈F,11*S.card≤N) (htwo : 2≤F.card)
    (hkernel : Kernel (Ground N) F=∅)
    (hparam : CroftPrice140.ParameterBudget N K D cut) :
    (F.card:ℝ)/(N:ℝ)^2≤CroftPrice140.Budget := by
  obtain ⟨hD,hDK,hDC,_hcutK,_hKN,hDirect,hWholeK,hWholeD,hRoot⟩ := hparam
  have hK : 600≤K := by omega
  have hn : 0<N := by omega
  by_cases hSmall : SmallKernel112.Small F (3*K)=∅
  · have hlow : ∀S∈F,3*K≤S.card := by
      intro S hS
      by_contra hh
      have hm : S∈SmallKernel112.Small F (3*K) := Finset.mem_filter.mpr ⟨hS,by omega⟩
      rw [hSmall] at hm
      exact Finset.notMem_empty S hm
    exact (actual_whole_uniform hF hK hN hhi hbad hsize hlow).trans hWholeK
  · by_cases hSmallKernel : Kernel (Ground N) (SmallKernel112.Small F (3*K))=∅
    · obtain ⟨T,hTF,_hTpos,hmin,hbound⟩ :=
        SmallKernel112.actual_minimum_member_with_direct hF hbad htwo hSmallKernel
      by_cases hcut : T.card≤cut
      · exact (actual_direct_uniform hn hbound hcut).trans hDirect
      · have hlow : ∀S∈F,3*D≤S.card := by
          intro S hS
          have hm := hmin S hS
          omega
        exact (actual_whole_uniform hF hD hN hhi hbad hsize hlow).trans hWholeD
    · obtain ⟨c,hc⟩ := Finset.nonempty_iff_ne_empty.mpr hSmallKernel
      obtain ⟨hcN,hcSmall⟩ := Finset.mem_filter.mp hc
      have hsmall : ∀S∈F,S.card≤3*K→c∈S := by
        intro S hS hs
        exact hcSmall S (Finset.mem_filter.mpr ⟨hS,hs⟩)
      have homit := actual_omitter_of_empty_kernel hkernel c hcN
      exact (actual_root_uniform hN hhi hK hF hbad hsize hsmall homit).trans hRoot


theorem actual_log_gates {N : ℕ} (hN : 62443451≤N) (hhi : N≤62911096) :
    let J := Nat.log 2 N+1
    26≤J ∧ J≤27 ∧ N<2^J ∧ N<2^27 := by
  have hn : N≠0 := by omega
  have hl : 25≤Nat.log 2 N := (Nat.le_log_iff_pow_le (by decide : 1<2) hn).mpr
    ((by norm_num : (2:ℕ)^25≤62443451).trans hN)
  have hu26 : N<2^26 := by norm_num; omega
  have hu27 : N<2^27 := by norm_num; omega
  have hlog := Nat.log_lt_of_lt_pow hn hu26
  have heq : Nat.log 2 N+1=26 := by omega
  dsimp only
  rw [heq]
  exact ⟨by decide,by decide,hu26,hu27⟩

theorem actual_sparse_density_gt {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 62443451≤N) (hhi : N≤62911096) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) :
    CroftPrice140.Budget<((SparseCrooked N 11 F).card:ℝ)/(N:ℝ)^2 := by
  have hNJ := (actual_log_gates hN hhi).2.2.2
  have hd := APDensity112.actual_sparse_density11_normalized
    (by omega : 10185≤N) (by norm_num : 4≤27) hNJ hF hcard
  norm_num at hd
  have hnR : (62443451:ℝ)≤N := by exact_mod_cast hN
  have he : (514:ℝ)/N≤514/62443451 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hb : CroftPrice140.Budget<(71/800:ℝ)-514/62443451 := by
    norm_num [CroftPrice140.Budget]
  linarith only [hd,he,hb]

theorem actual_sparse_card_two {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 62443451≤N) (hhi : N≤62911096) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) : 2≤(SparseCrooked N 11 F).card := by
  have hd := actual_sparse_density_gt hN hhi hF hcard
  have hn : (62443451:ℝ)≤N := by exact_mod_cast hN
  have hnp : (0:ℝ)<N := by linarith only [hn]
  have hc := (lt_div_iff₀ (sq_pos_of_pos hnp)).mp hd
  have hsq : (62443451:ℝ)^2≤(N:ℝ)^2 :=
    (sq_le_sq₀ (by norm_num) (Nat.cast_nonneg N)).mpr hn
  by_contra hh
  have hl : ((SparseCrooked N 11 F).card:ℝ)≤1 := by
    exact_mod_cast (by omega : (SparseCrooked N 11 F).card≤1)
  norm_num [CroftPrice140.Budget] at hc
  nlinarith only [hc,hsq,hl]

theorem actual_sparse_kernel_nonempty {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 62443451≤N) (hhi : N≤62911096) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) : (Kernel (Ground N) (SparseCrooked N 11 F)).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  obtain ⟨K,D,cut,hparam⟩ := CroftPrice140.actual_parameters hN hhi
  have hb := actual_empty_kernel_bound_of_parameters (by omega : 63≤N) hhi
    (actual_sparse_legal hF) (fun S hS=>(actual_sparse_membership.mp hS).2.1)
    (fun S hS=>(actual_sparse_membership.mp hS).2.2)
    (actual_sparse_card_two hN hhi hF hcard) he hparam
  have hd := actual_sparse_density_gt hN hhi hF hcard
  linarith only [hb,hd]

theorem actual_original_root11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 62443451≤N) (hhi : N≤62911096) (hF : Legal (Ground N) F)
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
end JSP233.CroftKernel140
