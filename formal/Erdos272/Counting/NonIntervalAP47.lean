module

public import Erdos272.Counting.APCount41
public import Erdos272.Resources.ResiduePool46
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Actual noninterval progressions and the full large-step straddling family. -/
namespace JSP233.NonIntervalAP47
open StarCompletion APGeometry APCount41 WitnessInterval43
open scoped Classical BigOperators
noncomputable section

def IsInterval (S : Finset ℤ) : Prop := ∃ a b:ℤ,S=Finset.Icc a b

theorem actual_step_one_interval {p : ℤ} {S : Finset ℤ}
    (hS : APAt 1 p S) : IsInterval S := by
  obtain ⟨_,lo,hi,hr⟩ := hS
  refine ⟨lo,hi,?_⟩
  ext x
  simpa only [Finset.mem_Icc,one_dvd,and_true] using hr x

theorem actual_noninterval_card_two {S : Finset ℤ}
    (hAP : IsAP S) (hno : ¬IsInterval S) : 2≤S.card := by
  by_contra hn
  have hcard : S.card≤1 := by omega
  obtain ⟨a,ha⟩ := isAP_nonempty hAP
  have he : S={a} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨ha,fun b hb=>Finset.card_le_one.mp hcard b hb a ha⟩
  apply hno
  exact ⟨a,a,by simp [he]⟩

theorem actual_noninterval_step_two {S : Finset ℤ}
    (hAP : IsAP S) (hno : ¬IsInterval S) : 2≤Step S := by
  obtain ⟨hd,p,hp⟩ := actual_step hAP
  by_contra hn
  have he : Step S=1 := by omega
  rw [he] at hp
  exact hno (actual_step_one_interval hp)

theorem square_reciprocal_without_one (N : ℕ) :
    (∑ d∈Finset.Icc 2 N,(1:ℝ)/(d:ℝ)^2)≤2/3 := by
  by_cases hN : 1≤N
  · have he : Finset.Icc 1 N=insert 1 (Finset.Icc 2 N) := by
      ext d
      simp only [Finset.mem_Icc,Finset.mem_insert]
      omega
    have hh := square_reciprocal_bound N
    rw [SquareReciprocal,he,Finset.sum_insert (by simp)] at hh
    norm_num only [Nat.cast_one,one_pow,div_one] at hh
    linarith only [hh]
  · have hz : N=0 := by omega
    simp [hz]
    norm_num

theorem actual_noninterval_AP_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hAP : ∀ S∈F,IsAP S)
    (hno : ∀ S∈F,¬IsInterval S) :
    (F.card:ℝ)≤(N:ℝ)^2/6+(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
  have hmaps : ∀ S∈F,Step S∈Finset.Icc 2 N := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨actual_noninterval_step_two (hAP S hS) (hno S hS),
      actual_step_bound (hF.1 S hS) (hAP S hS) (actual_noninterval_card_two (hAP S hS) (hno S hS))⟩
  have he := Finset.card_eq_sum_card_fiberwise hmaps
  have hclass : ∀ d∈Finset.Icc 2 N,
      ((F.filter (fun S=>Step S=d)).card:ℝ)≤(N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1 := by
    intro d hd
    let C := F.filter (fun S=>Step S=d)
    have hCF : C⊆F := Finset.filter_subset _ _
    have hLC : Legal (Ground N) C := ⟨fun S hS=>hF.1 S (hCF hS),
      fun S hS T hT hn=>hF.2 S (hCF hS) T (hCF hT) hn⟩
    apply actual_same_step_count (by have hh:=Finset.mem_Icc.mp hd;omega) hLC
      (fun S hS=>isAP_nonempty (hAP S (hCF hS)))
    intro S hS
    obtain ⟨_,p,hp⟩ := actual_step (hAP S (hCF hS))
    exact ⟨p,by rwa [(Finset.mem_filter.mp hS).2] at hp⟩
  have hrecip : (∑ d∈Finset.Icc 2 N,(1:ℝ)/(d:ℝ))≤HarmonicAbel29.Harmonic N := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      have hh := Finset.mem_Icc.mp hd
      exact Finset.mem_Icc.mpr (by omega)
    · intro _ _ _
      positivity
  have hcard : ((Finset.Icc 2 N).card:ℝ)≤N := by
    exact_mod_cast (show (Finset.Icc 2 N).card≤N by rw [Nat.card_Icc];omega)
  have hsum : (∑ d∈Finset.Icc 2 N,((N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1))=
      (N:ℝ)^2/4*(∑ d∈Finset.Icc 2 N,(1:ℝ)/(d:ℝ)^2)+
        (N:ℝ)*(∑ d∈Finset.Icc 2 N,(1:ℝ)/(d:ℝ))+(Finset.Icc 2 N).card := by
    have ht : ∀ d:ℕ,(N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1=
        (N:ℝ)^2/4*(1/(d:ℝ)^2)+(N:ℝ)*(1/(d:ℝ))+1 := by intro d;ring
    simp_rw [ht]
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,mul_one]
  have hsq := mul_le_mul_of_nonneg_left (square_reciprocal_without_one N)
    (show (0:ℝ)≤(N:ℝ)^2/4 by positivity)
  have hr := mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg (α:=ℝ) N)
  calc
    (F.card:ℝ)=∑ d∈Finset.Icc 2 N,((F.filter (fun S=>Step S=d)).card:ℝ) := by exact_mod_cast he
    _≤∑ d∈Finset.Icc 2 N,((N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1) := Finset.sum_le_sum hclass
    _≤_ := by rw [hsum];nlinarith only [hsq,hr,hcard]

theorem actual_noninterval_part_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) :
    ((F.filter (fun S=>IsAP S ∧ ¬IsInterval S)).card:ℝ)≤
      (N:ℝ)^2/6+(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
  let A := F.filter (fun S=>IsAP S ∧ ¬IsInterval S)
  have hAF : A⊆F := Finset.filter_subset _ _
  exact actual_noninterval_AP_count ⟨fun S hS=>hF.1 S (hAF hS),
    fun S hS T hT hn=>hF.2 S (hAF hS) T (hAF hT) hn⟩
    (fun S hS=>(Finset.mem_filter.mp hS).2.1) (fun S hS=>(Finset.mem_filter.mp hS).2.2)

theorem actual_interval_straddled_root {S : Finset ℤ} {c : ℤ}
    (hI : IsInterval S) (hcross : (∃ x∈S,x<c) ∧ ∃ y∈S,c<y) : c∈S := by
  obtain ⟨a,b,rfl⟩ := hI
  obtain ⟨⟨x,hx,hxc⟩,y,hy,hcy⟩ := hcross
  have hxx := Finset.mem_Icc.mp hx
  have hyy := Finset.mem_Icc.mp hy
  exact Finset.mem_Icc.mpr (by omega)

theorem actual_rooted_interval_isAP {S : Finset ℤ} {c : ℤ}
    (hc : c∈S) (hI : IsInterval S) : IsAP S := by
  obtain ⟨a,b,rfl⟩ := hI
  have hh := Finset.mem_Icc.mp hc
  exact integer_interval_isAP a b (by omega)

theorem actual_family_three_part {F : Finset (Finset ℤ)} {c : ℤ}
    (hroot : ∀ S∈F,IsInterval S→c∈S) :
    (PrivatePairExistence.CrookedMembers F).card+(RootedIntervals46.RootedIntervals F c).card+
      (F.filter (fun S=>IsAP S ∧ ¬IsInterval S)).card=F.card := by
  let H := F.filter IsAP
  have hE : H.filter IsInterval=RootedIntervals46.RootedIntervals F c := by
    ext S
    constructor
    · intro hS
      obtain ⟨hSH,hI⟩ := Finset.mem_filter.mp hS
      have hSF := (Finset.mem_filter.mp hSH).1
      exact Finset.mem_filter.mpr ⟨hSF,hroot S hSF hI,hI⟩
    · intro hS
      obtain ⟨hSF,hc,hI⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hSF,actual_rooted_interval_isAP hc hI⟩,hI⟩
  have hA : H.filter (fun S=>¬IsInterval S)=F.filter (fun S=>IsAP S ∧ ¬IsInterval S) := by
    simp only [H,Finset.filter_filter]
  have hp := Finset.card_filter_add_card_filter_not (s:=F) IsAP
  have hq := Finset.card_filter_add_card_filter_not (s:=H) IsInterval
  rw [hE,hA] at hq
  change H.card+(PrivatePairExistence.CrookedMembers F).card=F.card at hp
  omega

theorem actual_large_step_straddling_count {N : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {c a k : ℤ} (hN : 6≤N) (hcN : c∈Ground N)
    (hF : Legal (Ground N) F) (hc : ∀ S∈F,¬IsAP S→c∈S)
    (hcross : ∀ S∈F,c∉S→(∃ x∈S,x<c) ∧ ∃ y∈S,c<y)
    (hP : P∈F) (hcP : c∉P) (hk : 3≤k) (hAP : APAt k a P) :
    (F.card:ℝ)≤4*(N:ℝ)^2/9+(N:ℝ)*HarmonicAbel29.Harmonic N+6*N+
      6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  have hroot : ∀ S∈F,IsInterval S→c∈S := by
    intro S hS hI
    by_contra hn
    exact hn (actual_interval_straddled_root hI (hcross S hS hn))
  have hp : ((PrivatePairExistence.CrookedMembers F).card:ℝ)+
      (RootedIntervals46.RootedIntervals F c).card+
      (F.filter (fun S=>IsAP S ∧ ¬IsInterval S)).card=F.card := by
    exact_mod_cast actual_family_three_part hroot
  have hCE := ResiduePool46.actual_avoider_sparse_rooted_APAt hN hcN hF hP hcP hc hk hAP
  have hA := actual_noninterval_part_count hF
  linarith only [hp,hCE,hA]

theorem actual_large_step_straddling_gap {N J : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {c a k : ℤ} (hN : 6≤N) (hNJ : N<2^J) (hscale : 468*J^3≤N)
    (hcN : c∈Ground N) (hF : Legal (Ground N) F) (hc : ∀ S∈F,¬IsAP S→c∈S)
    (hcross : ∀ S∈F,c∉S→(∃ x∈S,x<c) ∧ ∃ y∈S,c<y)
    (hP : P∈F) (hcP : c∉P) (hk : 3≤k) (hAP : APAt k a P) :
    (F.card:ℝ)≤17*(N:ℝ)^2/36 := by
  have hJ : 2≤J := by
    by_contra hn
    have hb : J≤1 := by omega
    interval_cases J <;> norm_num at hNJ <;> omega
  have hJR : (2:ℝ)≤J := by exact_mod_cast hJ
  have hH := HarmonicSharp39.actual_harmonic_tight N J hNJ
  have hH0 : 0≤HarmonicAbel29.Harmonic N := by
    unfold HarmonicAbel29.Harmonic
    exact Finset.sum_nonneg (fun _ _=>by positivity)
  have hHJ : HarmonicAbel29.Harmonic N≤J := by linarith only [hH,hJR]
  have hH3 : HarmonicAbel29.Harmonic N^3≤(J:ℝ)^3 := by gcongr
  have hJJ : (J:ℝ)≤(J:ℝ)^3 := by
    have hp := mul_nonneg (show (0:ℝ)≤(J:ℝ)-1 by linarith only [hJR])
      (show (0:ℝ)≤(J:ℝ)^2+J by positivity)
    nlinarith only [hp]
  have hbound := actual_large_step_straddling_count hN hcN hF hc hcross hP hcP hk hAP
  have hlin := mul_le_mul_of_nonneg_left hHJ (Nat.cast_nonneg (α:=ℝ) N)
  have hcubic := mul_le_mul_of_nonneg_left hH3 (show (0:ℝ)≤6*(N:ℝ) by positivity)
  have hlin3 := mul_le_mul_of_nonneg_left hJJ (Nat.cast_nonneg (α:=ℝ) N)
  have hone3 : (1:ℝ)≤(J:ℝ)^3 := by linarith only [hJR,hJJ]
  have hone := mul_le_mul_of_nonneg_left hone3 (Nat.cast_nonneg (α:=ℝ) N)
  have hs : (468:ℝ)*(J:ℝ)^3≤N := by exact_mod_cast hscale
  have hsN := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α:=ℝ) N)
  nlinarith only [hbound,hlin,hcubic,hlin3,hone,hsN]

#print axioms actual_step_one_interval
#print axioms actual_noninterval_card_two
#print axioms actual_noninterval_step_two
#print axioms square_reciprocal_without_one
#print axioms actual_noninterval_AP_count
#print axioms actual_noninterval_part_count
#print axioms actual_interval_straddled_root
#print axioms actual_rooted_interval_isAP
#print axioms actual_family_three_part
#print axioms actual_large_step_straddling_count
#print axioms actual_large_step_straddling_gap
end
end JSP233.NonIntervalAP47
