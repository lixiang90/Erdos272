module

public import Erdos272.Global.Startup49
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! All thirty finite startup blocks. Data supplies only numerals; every arithmetic
and finite prime-count assertion below is checked by the ordinary Lean kernel. -/
namespace JSP233.StartupSeeds40
open StarCompletion PrimorialRatio39 WeightedTail39 SparseSmall39 SparseRoot49
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

structure Seed where
  w : ℕ
  v : ℕ
  kl : ℕ
  ell : ℕ
  b0 : ℕ
  b1 : ℕ
  b : ℕ
  ratio : ℝ

def Seeds : Fin 30→Seed := ![
  ⟨13,21,185363,18,430,608,861,131710070791/19110297600⟩,
  ⟨13,22,262144,19,512,724,1024,131710070791/19110297600⟩,
  ⟨13,22,370727,19,608,861,1217,131710070791/19110297600⟩,
  ⟨13,22,524288,20,724,1024,1448,131710070791/19110297600⟩,
  ⟨14,23,741455,20,861,1217,1722,5663533044013/802632499200⟩,
  ⟨14,23,1048576,21,1024,1448,2048,5663533044013/802632499200⟩,
  ⟨14,23,1482910,21,1217,1722,2435,5663533044013/802632499200⟩,
  ⟨14,24,2097152,22,1448,2048,2896,5663533044013/802632499200⟩,
  ⟨14,24,2965820,22,1722,2435,3444,5663533044013/802632499200⟩,
  ⟨14,24,4194304,23,2048,2896,4096,5663533044013/802632499200⟩,
  ⟨15,25,5931641,23,2435,3444,4870,11573306655157/1605264998400⟩,
  ⟨15,25,8388608,24,2896,4096,5792,11573306655157/1605264998400⟩,
  ⟨15,25,11863283,24,3444,4870,6888,11573306655157/1605264998400⟩,
  ⟨15,26,16777216,25,4096,5792,8192,11573306655157/1605264998400⟩,
  ⟨15,26,23726566,25,4870,6888,9741,11573306655157/1605264998400⟩,
  ⟨16,26,33554432,26,5792,8192,11585,47183480978717/6421059993600⟩,
  ⟨16,27,47453132,26,6888,9741,13777,47183480978717/6421059993600⟩,
  ⟨16,27,67108864,27,8192,11585,16384,47183480978717/6421059993600⟩,
  ⟨16,27,94906265,27,9741,13777,19483,47183480978717/6421059993600⟩,
  ⟨16,28,134217728,28,11585,16384,23170,47183480978717/6421059993600⟩,
  ⟨16,28,189812531,28,13777,19483,27554,47183480978717/6421059993600⟩,
  ⟨17,28,268435456,29,16384,23170,32768,95993978542907/12842119987200⟩,
  ⟨17,29,379625062,29,19483,27554,38967,95993978542907/12842119987200⟩,
  ⟨17,29,536870912,30,23170,32768,46340,95993978542907/12842119987200⟩,
  ⟨17,29,759250124,30,27554,38967,55108,95993978542907/12842119987200⟩,
  ⟨17,30,1073741824,31,32768,46340,65536,95993978542907/12842119987200⟩,
  ⟨17,30,1518500249,31,38967,55108,77935,95993978542907/12842119987200⟩,
  ⟨18,30,2147483648,32,46340,65536,92681,5855632691117327/770527199232000⟩,
  ⟨18,31,3037000499,32,55108,77935,110217,5855632691117327/770527199232000⟩,
  ⟨18,31,4294967296,33,65536,92681,131072,5855632691117327/770527199232000⟩]

def Prime32 : Fin 32→ℕ := ![2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131]

theorem prime_at_seed32 (i : Fin 32) : PrimeAt i=Prime32 i := by
  fin_cases i <;> norm_num only [Prime32,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals apply prime_at_of_count <;> decide

theorem prime_at_seed32_nat (i : ℕ) (hi : i<32) : PrimeAt i=Prime32 ⟨i,hi⟩ :=
  prime_at_seed32 ⟨i,hi⟩

def Block (i : Fin 30) (N : ℕ) : Prop := 2^(49+i.val)≤N ∧ N<2^(50+i.val)

theorem seed_checks (i : Fin 30) :
    185363≤(Seeds i).kl ∧ 4≤(Seeds i).ell ∧
    (Seeds i).ell*((Seeds i).v+1)<(Seeds i).b0 ∧
    ((Seeds i).ell+1)*((Seeds i).v+1)<(Seeds i).b1 ∧
    ((Seeds i).ell+3)*((Seeds i).v+1)<(Seeds i).b ∧
    (Seeds i).b0^2≤(Seeds i).kl ∧ (Seeds i).b1^2≤2*(Seeds i).kl ∧
    (Seeds i).b^2≤4*(Seeds i).kl ∧
    ((Seeds i).kl*128)^2≤2^(49+i.val) ∧
    2^(50+i.val)≤(128*2^(Seeds i).ell)^2 ∧
    2^(50+i.val)≤Primorial ((Seeds i).w+1) ∧
    2^(2*(50+i.val))≤Primorial ((Seeds i).v+1) ∧
    Ratio (Seeds i).w=(Seeds i).ratio ∧ 0≤(Seeds i).ratio ∧
    2*(Seeds i).ratio*(2^(Seeds i).w:ℕ)≤((Seeds i).kl:ℝ) := by
  fin_cases i <;> norm_num [Seeds,Primorial,Ratio,Finset.prod_range_succ,
    prime_at_seed32_nat,Prime32]

theorem seed_tail_gate (i : Fin 30) :
    4*(Seeds i).ratio≤TailSlope (Seeds i).ell (Seeds i).v (Seeds i).b*
      ((Seeds i).ell+32) := by
  fin_cases i <;> norm_num [Seeds,TailSlope]

theorem seed_sigma_bound (i : Fin 30) :
    (∑ j∈Finset.range 32,BandEnvelope (Seeds i).ell (Seeds i).v
      (Seeds i).b0 (Seeds i).b1 (Seeds i).b (Seeds i).ratio j*(1/2:ℝ)^j)+
      TailSlope (Seeds i).ell (Seeds i).v (Seeds i).b*
        (2*((Seeds i).ell+32)+2)*(1/2:ℝ)^32≤160 := by
  fin_cases i <;> norm_num [Seeds,Finset.sum_range_succ,BandEnvelope,
    WeightedFar38.ShortCoefficient,TailSlope]

theorem cutoff_block (i : Fin 30) (N : ℕ) (hblock : Block i N) :
    (Seeds i).kl≤Startup49.Cutoff N ∧ Startup49.Cutoff N≤2^(Seeds i).ell ∧
    16384*(Startup49.Cutoff N)^2≤N := by
  have hc := seed_checks i
  obtain ⟨hmin,hell,h0,h1,hb,hs0,hs1,hsb,hlo,hup,hP,hPP,hR,hR0,hlong⟩ := hc
  have hl : (Seeds i).kl*128≤N.sqrt := Nat.le_sqrt'.mpr (hlo.trans hblock.1)
  have hl' : (Seeds i).kl≤N.sqrt/128 := (Nat.le_div_iff_mul_le (by decide)).mpr hl
  have hu : N≤(128*2^(Seeds i).ell)^2 := hblock.2.le.trans hup
  have hs := Nat.sqrt_le_sqrt hu
  rw [Nat.sqrt_eq'] at hs
  have hs' := Nat.div_le_div_right (c:=128) hs
  have hupper : N.sqrt/128≤2^(Seeds i).ell := by
    simpa only [Nat.mul_div_right _ (by decide : 0<128)] using hs'
  exact ⟨hl',hupper,Startup49.cutoff_square N⟩

theorem uniform_block_arithmetic (i : Fin 30) (N : ℕ) (hblock : Block i N) :
    (∀ m≤N,m.primeFactors.card≤(Seeds i).w) ∧
    (∀ m≤N,(m:ℝ)≤(Seeds i).ratio*Nat.totient m) ∧
    (∀ m≤N^2,m.primeFactors.card≤(Seeds i).v) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hP,hPP,hR,_,_⟩ := seed_checks i
  obtain ⟨hw,hr⟩ := uniform_omega_and_ratio N (Seeds i).w (hblock.2.trans_le hP)
  have hsquare : N^2<2^(2*(50+i.val)) := by
    have hh := Nat.mul_self_lt_mul_self hblock.2
    have he : 2^(50+i.val)*2^(50+i.val)=2^(2*(50+i.val)) := by
      rw [←pow_add]; congr 1; omega
    simpa only [pow_two,he] using hh
  have hp := (uniform_omega_and_ratio (N^2) (Seeds i).v (hsquare.trans_le hPP)).1
  exact ⟨hw,by simpa only [hR] using hr,hp⟩

theorem actual_block_large_budget (i : Fin 30) (N : ℕ) (F : Finset (Finset ℤ))
    (hblock : Block i N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hlow : ∀ S∈F,16*Startup49.Cutoff N+1≤S.card) :
    (F.card:ℝ)*Startup49.Cutoff N≤(174/5+16*(160:ℝ))*(N:ℝ)^2 := by
  obtain ⟨hKl,hKu,_⟩ := cutoff_block i N hblock
  obtain ⟨hmin,hell,h0,h1,hb,hs0,hs1,hsb,_,_,_,_,_,hR0,hlong⟩ := seed_checks i
  obtain ⟨homega,hratio,hproduct⟩ := uniform_block_arithmetic i N hblock
  have hK : 0<Startup49.Cutoff N := by omega
  have hKlR : ((Seeds i).kl:ℝ)≤Startup49.Cutoff N := by exact_mod_cast hKl
  have hh := actual_large_prefix_tail_budget N (Startup49.Cutoff N) (Seeds i).ell
    (Seeds i).w (Seeds i).v (Seeds i).b0 (Seeds i).b1 (Seeds i).b 32 F (Seeds i).ratio
    hlegal hK hbad hlow hR0 homega hratio hproduct (hlong.trans hKlR)
    hell hKu h0 h1 hb (hs0.trans hKl)
    (hs1.trans (Nat.mul_le_mul_left 2 hKl)) (hsb.trans (Nat.mul_le_mul_left 4 hKl))
    (by decide) (seed_tail_gate i)
  have hm := mul_le_mul_of_nonneg_right (seed_sigma_bound i) (sq_nonneg (N:ℝ))
  nlinarith only [hh,hm]

theorem exists_block (N : ℕ) (hNl : 2^49≤N) (hNu : N<2^79) :
    ∃ i : Fin 30,Block i N := by
  have hN : N≠0 := by norm_num at hNl; omega
  have hqlo : 49≤Nat.log 2 N := (Nat.le_log_iff_pow_le (by decide) hN).mpr hNl
  have hqhi : Nat.log 2 N<79 := Nat.log_lt_of_lt_pow hN hNu
  let i : Fin 30 := ⟨Nat.log 2 N-49,by omega⟩
  have he : 49+i.val=Nat.log 2 N := by dsimp [i]; omega
  refine ⟨i,?_,?_⟩
  · rw [he]
    exact Nat.pow_log_le_self 2 hN
  · have he' : 50+i.val=Nat.log 2 N+1 := by omega
    rw [he']
    exact Nat.lt_pow_succ_log_self (by decide) N

theorem actual_large_budget (N : ℕ) (F : Finset (Finset ℤ))
    (hNl : 2^49≤N) (hNu : N<2^79) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hlow : ∀ S∈F,16*Startup49.Cutoff N+1≤S.card) :
    (F.card:ℝ)*Startup49.Cutoff N≤(174/5+16*(160:ℝ))*(N:ℝ)^2 := by
  obtain ⟨i,hi⟩ := exists_block N hNl hNu
  exact actual_block_large_budget i N F hi hlegal hbad hlow

theorem actual_large_complement_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hNl : 2^49≤N) (hNu : N<2^79) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) :
    ((LargeMembers F (Startup49.Cutoff N)).card:ℝ)≤
      ((174/5+16*(160:ℝ))/185363)*(N:ℝ)^2 := by
  let L := LargeMembers F (Startup49.Cutoff N)
  have hLF : L⊆F := Finset.filter_subset _ _
  have hLL : Legal (Ground N) L := ⟨fun S hS=>hlegal.1 S (hLF hS),
    fun S hS T hT hne=>hlegal.2 S (hLF hS) T (hLF hT) hne⟩
  have hlow : ∀ S∈L,16*Startup49.Cutoff N+1≤S.card := by
    intro S hS
    have hh := (Finset.mem_filter.mp hS).2
    omega
  have hb := actual_large_budget N L hNl hNu hLL (fun S hS=>hbad S (hLF hS)) hlow
  have hKl := Startup49.cutoff_lower N hNl
  have hKlR : (185363:ℝ)≤Startup49.Cutoff N := by exact_mod_cast hKl
  have hm := mul_le_mul_of_nonneg_left hKlR (show (0:ℝ)≤L.card by positivity)
  change (L.card:ℝ)≤_
  nlinarith only [hb,hm]

theorem all_seed_budget_coefficient :
    ((2*(28:ℝ)-1)/(2*(28:ℝ)^2))+1/32+
      (174/5+16*(160:ℝ))/185363≤1/12-1/1000 := by norm_num

theorem actual_empty_kernel_budget {N : ℕ} {F : Finset (Finset ℤ)}
    (hNl : 2^49≤N) (hNu : N<2^79) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,28*S.card≤N)
    (hkernel : PrivateFinset.Kernel (Ground N) F=∅) :
    (F.card:ℝ)≤(1/12-1/1000)*(N:ℝ)^2 := by
  have h4 : 4≤N := (by norm_num : 4≤(2:ℕ)^49).trans hNl
  have hK : 0<Startup49.Cutoff N := by have hh := Startup49.cutoff_lower N hNl; omega
  have hs := actual_small_empty_kernel_rational h4 (by norm_num : 2≤28)
    hK hlegal hbad hsize hkernel
  have hl := actual_large_complement_bound hNl hNu hlegal hbad
  have hp := congrArg (fun m:ℕ=>(m:ℝ)) (actual_small_large_partition F (Startup49.Cutoff N))
  simp only [Nat.cast_add] at hp
  have hthinR : (16384:ℝ)*(Startup49.Cutoff N:ℝ)^2≤N := by
    exact_mod_cast Startup49.cutoff_square N
  have ht := mul_le_mul_of_nonneg_right hthinR (show (0:ℝ)≤N by positivity)
  have hc := mul_le_mul_of_nonneg_right all_seed_budget_coefficient (sq_nonneg (N:ℝ))
  have hN0 : (0:ℝ)≤N := by positivity
  norm_num only [Nat.cast_ofNat] at hs
  nlinarith only [hs,hl,hp,ht,hc,hN0]

theorem density_exceeds_empty_kernel_budget {N : ℕ} (hN : 2^49≤N) :
    (1/12-1/1000)*(N:ℝ)^2<(N:ℝ)^2/12-6372*(N:ℝ)-3 := by
  have hNR : (562949953421312:ℝ)≤N := by
    exact_mod_cast (show 562949953421312≤N by norm_num at hN ⊢; exact hN)
  have hpos : (0:ℝ)<N := by linarith
  have hl : (6373:ℝ)<(N:ℝ)/1000 := by linarith
  have hm := mul_lt_mul_of_pos_right hl hpos
  nlinarith only [hm,hNR]

theorem actual_sparse_common_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hNl : 2^49≤N) (hNu : N<2^79) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,28*S.card≤N)
    (hdense : (N:ℝ)^2/12-6372*(N:ℝ)-3≤F.card) :
    ∃ c∈Ground N,∀ S∈F,c∈S := by
  have hne : (PrivateFinset.Kernel (Ground N) F).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hb := actual_empty_kernel_budget hNl hNu hlegal hbad hsize he
    have hc := density_exceeds_empty_kernel_budget hNl
    linarith
  obtain ⟨c,hc⟩ := hne
  exact ⟨c,(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩

#print axioms prime_at_seed32
#print axioms prime_at_seed32_nat
#print axioms seed_checks
#print axioms seed_tail_gate
#print axioms seed_sigma_bound
#print axioms cutoff_block
#print axioms uniform_block_arithmetic
#print axioms actual_block_large_budget
#print axioms exists_block
#print axioms actual_large_budget
#print axioms actual_large_complement_bound
#print axioms all_seed_budget_coefficient
#print axioms actual_empty_kernel_budget
#print axioms density_exceeds_empty_kernel_budget
#print axioms actual_sparse_common_root
end
end JSP233.StartupSeeds40
