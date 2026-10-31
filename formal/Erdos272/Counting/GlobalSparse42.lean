import Erdos272.Arithmetic.WeightedPeriod42
import Erdos272.Counting.Density41

/-! All-N actual large-family budgets and original-family sparse crooked roots.
All arithmetic, band, weighted and density inputs are discharged internally. -/
namespace JSP233.GlobalSparse42
open StarCompletion PrimorialRatio39 StartupSeeds40 PrimePeriod41 WeightedPeriod42
open WeightedFar38 WeightedTail39 SparseSmall39 SparseRoot49 DenseDeletion40 DenseSharper41
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

def LargeCoefficient : ℝ := 174/5+16*160

theorem period_block_large (i : Fin 30) (t N : ℕ) (hblock : PeriodBlock i t N) : 2^49≤N := by
  exact (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega : 49≤49+i.val+30*t)).trans hblock.1

theorem scaled_square_budget (t B kl c K : ℕ) (hB : B^2≤c*kl)
    (hK : (32768:ℕ)^t*kl≤K) : (Scale t*B)^2≤c*K := by
  have hs : (Scale t)^2≤(32768:ℕ)^t := by
    calc
      (Scale t)^2=(16384:ℕ)^t := by dsimp [Scale]; rw [sq,←mul_pow]; norm_num
      _≤(32768:ℕ)^t := Nat.pow_le_pow_left (by decide) t
  have hp := Nat.mul_le_mul hs hB
  have hk := Nat.mul_le_mul_left c hK
  rw [mul_pow]
  nlinarith only [hp,hk]

theorem actual_period_bases (i : Fin 30) (t N : ℕ) (hblock : PeriodBlock i t N) :
    4≤Ell i t ∧ Startup49.Cutoff N≤2^(Ell i t) ∧
    Ell i t*(ProductOmega i t+1)<Scale t*(Seeds i).b0 ∧
    (Ell i t+1)*(ProductOmega i t+1)<Scale t*(Seeds i).b1 ∧
    (Ell i t+3)*(ProductOmega i t+1)<Scale t*(Seeds i).b ∧
    (Scale t*(Seeds i).b0)^2≤Startup49.Cutoff N ∧
    (Scale t*(Seeds i).b1)^2≤2*Startup49.Cutoff N ∧
    (Scale t*(Seeds i).b)^2≤4*Startup49.Cutoff N := by
  obtain ⟨_,hell,h0,h1,hb,hs0,hs1,hsb,_,_,_,_,_,_,_⟩ := seed_checks i
  obtain ⟨he,hv⟩ := seed_min_parameters i
  have hlocal : ∀ e B : ℕ,15≤e → e*((Seeds i).v+1)<B →
      (e+15*t)*((Seeds i).v+10*t+1)<Scale t*B := by
    intro e B he hbase
    exact (error_growth e (Seeds i).v t he hv).trans_lt
      (Nat.mul_lt_mul_of_pos_left hbase (scale_pos t))
  have h0' := hlocal (Seeds i).ell (Seeds i).b0 he h0
  have h1' := hlocal ((Seeds i).ell+1) (Seeds i).b1 (by omega) h1
  have hb' := hlocal ((Seeds i).ell+3) (Seeds i).b (by omega) hb
  have hKl := period_cutoff_lower i t N hblock
  refine ⟨by dsimp [Ell]; omega,period_cutoff_upper i t N hblock,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Ell,ProductOmega] using h0'
  · simpa only [Ell,ProductOmega,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h1'
  · simpa only [Ell,ProductOmega,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hb'
  · simpa only [one_mul] using scaled_square_budget t (Seeds i).b0 (Seeds i).kl 1
      (Startup49.Cutoff N) (by simpa only [one_mul] using hs0) hKl
  · exact scaled_square_budget t (Seeds i).b1 (Seeds i).kl 2 (Startup49.Cutoff N) hs1 hKl
  · exact scaled_square_budget t (Seeds i).b (Seeds i).kl 4 (Startup49.Cutoff N) hsb hKl

theorem actual_period_large_budget (i : Fin 30) (t N : ℕ) (F : Finset (Finset ℤ))
    (hblock : PeriodBlock i t N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hlow : ∀ S∈F,16*Startup49.Cutoff N+1≤S.card) :
    (F.card:ℝ)*Startup49.Cutoff N≤(174/5+16*((2:ℝ)^t*160))*(N:ℝ)^2 := by
  obtain ⟨hell,hfinite,h0,h1,hb,hs0,hs1,hsb⟩ := actual_period_bases i t N hblock
  obtain ⟨homega,hratio,hproduct⟩ := uniform_period_arithmetic i t N hblock.2
  have hKl := Startup49.cutoff_lower N (period_block_large i t N hblock)
  have hK : 0<Startup49.Cutoff N := by omega
  have hh := actual_large_schedule_budget N (Startup49.Cutoff N) (Ell i t)
    (DistanceOmega i t) (ProductOmega i t) (Scale t*(Seeds i).b0)
    (Scale t*(Seeds i).b1) (Scale t*(Seeds i).b) F (PeriodRatio i t)
    hlegal hK hbad hlow (period_ratio_nonneg i t) homega hratio hproduct
    (actual_period_long_gate i t N hblock) hell hfinite h0 h1 hb hs0 hs1 hsb
  have hs := period_sum_bound i t (N+1)
  dsimp only [Envelope] at hs
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (N:ℝ))
  nlinarith only [hh,hm]

theorem actual_large_normalized (N : ℕ) (F : Finset (Finset ℤ))
    (hN : 2^49≤N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hlow : ∀ S∈F,16*Startup49.Cutoff N+1≤S.card) :
    (F.card:ℝ)≤(LargeCoefficient/185363)*(N:ℝ)^2 := by
  obtain ⟨i,t,hblock⟩ := exists_period_block N hN
  have hb := actual_period_large_budget i t N F hblock hlegal hbad hlow
  obtain ⟨hmin,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := seed_checks i
  have hp : (2:ℕ)^t≤(32768:ℕ)^t := Nat.pow_le_pow_left (by decide) t
  have hK := (Nat.mul_le_mul hp hmin).trans (period_cutoff_lower i t N hblock)
  have hKR : (2:ℝ)^t*185363≤(Startup49.Cutoff N:ℝ) := by exact_mod_cast hK
  have hm := mul_le_mul_of_nonneg_left hKR (show (0:ℝ)≤F.card by positivity)
  have hpn : 1≤(2:ℕ)^t := by
    have hh : 0<(2:ℕ)^t := by positivity
    omega
  have hpr : (1:ℝ)≤(2:ℝ)^t := by exact_mod_cast hpn
  have hcost : 174/5+16*((2:ℝ)^t*160)≤(2:ℝ)^t*LargeCoefficient := by
    dsimp [LargeCoefficient]
    nlinarith only [hpr]
  have hcostN := mul_le_mul_of_nonneg_right hcost (sq_nonneg (N:ℝ))
  have htotal : (2:ℝ)^t*((F.card:ℝ)*185363)≤(2:ℝ)^t*(LargeCoefficient*(N:ℝ)^2) := by
    nlinarith only [hb,hm,hcostN]
  have hc := le_of_mul_le_mul_left htotal (by positivity : (0:ℝ)<(2:ℝ)^t)
  nlinarith only [hc]

theorem actual_large_complement_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F,¬IsAP S) :
    ((LargeMembers F (Startup49.Cutoff N)).card:ℝ)≤(LargeCoefficient/185363)*(N:ℝ)^2 := by
  let L := LargeMembers F (Startup49.Cutoff N)
  have hLF : L⊆F := Finset.filter_subset _ _
  have hLL : Legal (Ground N) L := ⟨fun S hS=>hlegal.1 S (hLF hS),
    fun S hS T hT hne=>hlegal.2 S (hLF hS) T (hLF hT) hne⟩
  have hlow : ∀ S∈L,16*Startup49.Cutoff N+1≤S.card := by
    intro S hS
    have hh := (Finset.mem_filter.mp hS).2
    omega
  exact actual_large_normalized N L hN hLL (fun S hS=>hbad S (hLF hS)) hlow

theorem actual_empty_kernel_budget {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,28*S.card≤N)
    (hkernel : PrivateFinset.Kernel (Ground N) F=∅) :
    (F.card:ℝ)≤(1/12-1/1000)*(N:ℝ)^2 := by
  have h4 : 4≤N := (by norm_num : 4≤(2:ℕ)^49).trans hN
  have hK : 0<Startup49.Cutoff N := by have hh:=Startup49.cutoff_lower N hN; omega
  have hs := SparseSmall39.actual_small_empty_kernel_rational h4 (by norm_num : 2≤28)
    hK hlegal hbad hsize hkernel
  have hl := actual_large_complement_bound hN hlegal hbad
  have hp := congrArg (fun m:ℕ=>(m:ℝ)) (actual_small_large_partition F (Startup49.Cutoff N))
  simp only [Nat.cast_add] at hp
  have hthinR : (16384:ℝ)*(Startup49.Cutoff N:ℝ)^2≤N := by exact_mod_cast Startup49.cutoff_square N
  have ht := mul_le_mul_of_nonneg_right hthinR (show (0:ℝ)≤N by positivity)
  have hc := mul_le_mul_of_nonneg_right all_seed_budget_coefficient (sq_nonneg (N:ℝ))
  have hN0 : (0:ℝ)≤N := by positivity
  norm_num only [Nat.cast_ofNat] at hs
  dsimp only [LargeCoefficient] at hl
  nlinarith only [hs,hl,hp,ht,hc,hN0]

theorem actual_sparse_common_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,28*S.card≤N)
    (hdense : (1/12-1/1000)*(N:ℝ)^2<F.card) : ∃ c∈Ground N,∀ S∈F,c∈S := by
  have hne : (PrivateFinset.Kernel (Ground N) F).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hb := actual_empty_kernel_budget hN hlegal hbad hsize he
    linarith
  obtain ⟨c,hc⟩ := hne
  exact ⟨c,(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩

theorem period_density_payment (i : Fin 30) (t N : ℕ) (hblock : PeriodBlock i t N) :
    ((3137:ℝ)+(7/10:ℝ)*(50+i.val+30*t:ℕ)+3)*(N:ℝ)+1<(N:ℝ)^2/1000 := by
  have hscale : (2:ℕ)^49*2^t≤N := by
    rw [←pow_add]
    exact (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ))
      (by omega : 49+t≤49+i.val+30*t)).trans hblock.1
  have hJ : 50+i.val+30*t≤2^t*79 := by
    have hh:=linear_growth 79 30 t (by decide)
    omega
  have hJNat : 1000000*(50+i.val+30*t)≤N := by
    have hh1:=Nat.mul_le_mul_left 1000000 hJ
    have hh2:=Nat.mul_le_mul_left ((2:ℕ)^t) (by norm_num : 1000000*79≤(2:ℕ)^49)
    nlinarith only [hh1,hh2,hscale]
  have hJR : (1000000:ℝ)*(50+i.val+30*t:ℕ)≤N := by exact_mod_cast hJNat
  have hN49:=period_block_large i t N hblock
  have hNR : (562949953421312:ℝ)≤N := by
    exact_mod_cast (show 562949953421312≤N by norm_num at hN49 ⊢; exact hN49)
  have hpos : (0:ℝ)<N := by linarith
  have hcoef : (3137:ℝ)+(7/10:ℝ)*(50+i.val+30*t:ℕ)+3<(N:ℝ)/2000 := by
    nlinarith only [hJR,hNR]
  have hm:=mul_lt_mul_of_pos_right hcoef hpos
  have hJpos : (0:ℝ)≤((50+i.val+30*t:ℕ):ℝ)*(N:ℝ) := by positivity
  have hsmall : (1:ℝ)<(N:ℝ)^2/2000 := by nlinarith only [hm,hNR,hJpos]
  nlinarith only [hm,hsmall]

theorem actual_original_sparse_root28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hlegal : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃ c∈Ground N,∀ S∈Density41.SparseCrooked N 28 F,c∈S := by
  obtain ⟨i,t,hblock⟩ := exists_period_block N hN
  have hNr : (4*28^2+1)*(2*28-1)≤N :=
    (by norm_num : (4*28^2+1)*(2*28-1)≤(2:ℕ)^49).trans hN
  have hd:=Density41.actual_sparse_density_sharp (by decide : 0<28) hNr hblock.2 hlegal hcounter
  have hp:=period_density_payment i t N hblock
  have hdense : (1/12-1/1000)*(N:ℝ)^2<(Density41.SparseCrooked N 28 F).card := by
    norm_num only [Nat.cast_ofNat] at hd
    nlinarith only [hd,hp]
  exact actual_sparse_common_root hN (Density41.actual_sparse_legal hlegal)
    (fun S hS=>(Density41.actual_sparse_membership.mp hS).2.1)
    (fun S hS=>(Density41.actual_sparse_membership.mp hS).2.2) hdense

theorem actual_original_retained_crooked_root28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hlegal : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃ c∈Ground N,∀ S∈Retained N 28 F,¬IsAP S → c∈S := by
  obtain ⟨c,hc,hroot⟩:=actual_original_sparse_root28 hN hlegal hcounter
  exact ⟨c,hc,fun S hS hbad=>hroot S (Finset.mem_filter.mpr ⟨hS,hbad⟩)⟩

theorem actual_original_reduction28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hlegal : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃ c∈Ground N,(∀ S∈Retained N 28 F,¬IsAP S → c∈S) ∧
      Legal (Ground N) (Retained N 28 F) ∧ F.card≤(Retained N 28 F).card+3137*N ∧
      (∀ S∈F,IsAP S → S∈Retained N 28 F) := by
  obtain ⟨c,hc,hroot⟩:=actual_original_retained_crooked_root28 hN hlegal hcounter
  have hNr : (4*28^2+1)*(2*28-1)≤N :=
    (by norm_num : (4*28^2+1)*(2*28-1)≤(2:ℕ)^49).trans hN
  refine ⟨c,hc,hroot,actual_retained_legal hlegal,?_,fun _ hS hAP=>actual_ap_retained hS hAP⟩
  simpa only [show 4*28^2+1=3137 by norm_num] using
    actual_retained_sharp_lower (by decide : 0<28) hNr hlegal

#print axioms period_block_large
#print axioms scaled_square_budget
#print axioms actual_period_bases
#print axioms actual_period_large_budget
#print axioms actual_large_normalized
#print axioms actual_large_complement_bound
#print axioms actual_empty_kernel_budget
#print axioms actual_sparse_common_root
#print axioms period_density_payment
#print axioms actual_original_sparse_root28
#print axioms actual_original_retained_crooked_root28
#print axioms actual_original_reduction28
end
end JSP233.GlobalSparse42
