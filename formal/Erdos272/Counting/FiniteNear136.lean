module

public import Erdos272.Counting.NearWhole112
public import Erdos272.Arithmetic.HarmonicLog55
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
namespace JSP233.FiniteNear136
open StarCompletion APGeometry NearAP36 NearWhole112 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def NuNumerator : ℝ := (2303/200)*(1-1/4096)

theorem exact_twelve_geometric_sum :
    (∑j∈Finset.range 12,(1/2:ℝ)^j)=2-1/2048 := by
  norm_num [Finset.sum_range_succ]

theorem actual_harmonic_le19 {N:ℕ} (hN : 63≤N) (hhi : N≤74320000) :
    Harmonic N≤19 := by
  have hh := HarmonicLog55.actual_refined_harmonic_upper (J:=27) (hi:=74320001)
    hN (by omega)
  exact hh.trans (by norm_num [HarmonicLog55.HarmonicUpper,HarmonicLog55.LogUpper])

theorem actual_sparse_level_lt12 {N K:ℕ} {F:Finset (Finset ℤ)}
    (level:Finset ℤ→ℕ) (hK : 600≤K) (hhi : N≤74320000)
    (hsize : ∀S∈F,11*S.card≤N) (hlow : ∀S∈F,3*Scale K (level S)≤S.card)
    {S:Finset ℤ} (hS:S∈F) : level S<12 := by
  by_contra hn
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) (show 12≤level S by omega)
  have hpK := Nat.mul_le_mul_right K hp
  have hb := hlow S hS
  have hs := hsize S hS
  dsimp only [Scale] at hb
  norm_num at hpK
  have hg : 33*4096*K≤N := by nlinarith only [hpK,hb,hs]
  omega

theorem actual_dyadic_sparse_core_first {N K : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hK : 600≤K)
    (hN : 63≤N) (hhi : N≤74320000) (hbad : ∀S∈F,¬IsAP S)
    (hsize : ∀S∈F,11*S.card≤N)
    (hlow : ∀S∈F,3*Scale K (level S)≤S.card)
    (hhigh : ∀S∈F,S.card≤6*Scale K (level S))
    (hnear : ∀S∈F,HasNearAPCore (Scale K (level S)) S) :
    (F.card:ℝ)≤NuNumerator*(N:ℝ)^2/K+798*N := by
  have hKpos : 0<K := by omega
  let family : ℕ→Finset (Finset ℤ) := fun j=>F.filter (fun S=>level S=j)
  have hfamily : ∀j,family j⊆F := fun j=>Finset.filter_subset _ _
  have hmaps : ∀S∈F,level S∈Finset.range 12 := by
    intro S hS
    exact Finset.mem_range.mpr (actual_sparse_level_lt12 level hK hhi hsize hlow hS)
  have hpart : F.card=∑j∈Finset.range 12,(family j).card := Finset.card_eq_sum_card_fiberwise hmaps
  have hpartR : (F.card:ℝ)=∑j∈Finset.range 12,((family j).card:ℝ) := by exact_mod_cast hpart
  have hrow : ∀j∈Finset.range 12,((family j).card:ℝ)≤
      (2303/400:ℝ)*(N:ℝ)^2/K*(1/2:ℝ)^j+(7/2:ℝ)*N*Harmonic N := by
    intro j _hj
    have hLj : Legal (Ground N) (family j) :=
      ⟨fun S hS=>hlegal.1 S (hfamily j hS),fun S hS T hT he=>
        hlegal.2 S (hfamily j hS) T (hfamily j hT) he⟩
    have hh := NearWhole112.actual_core_first_quadratic hLj (by positivity : 0<2^j*K)
      (fun S hS=>hbad S (hfamily j hS)) (by
        intro S hS
        simpa only [(Finset.mem_filter.mp hS).2,Scale] using hhigh S (hfamily j hS)) (by
        intro S hS
        simpa only [(Finset.mem_filter.mp hS).2,Scale] using hnear S (hfamily j hS))
    push_cast at hh
    have he : (2303/400:ℝ)*(N:ℝ)^2/((2:ℝ)^j*K)=
        (2303/400:ℝ)*(N:ℝ)^2/K*(1/2:ℝ)^j := by
      rw [one_div,inv_pow]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rwa [he] at hh
  have hs := Finset.sum_le_sum hrow
  rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  rw [←hpartR] at hs
  rw [exact_twelve_geometric_sum] at hs
  have hH := actual_harmonic_le19 hN hhi
  have hharm := mul_le_mul_of_nonneg_left hH
    (show (0:ℝ)≤(12:ℝ)*((7/2:ℝ)*N) by positivity)
  calc
    _≤(2303/400:ℝ)*(N:ℝ)^2/K*(2-1/2048)+(12:ℝ)*((7/2:ℝ)*N*Harmonic N) := hs
    _≤(2303/400:ℝ)*(N:ℝ)^2/K*(2-1/2048)+(12:ℝ)*((7/2:ℝ)*N*19) := by
      apply add_le_add le_rfl
      convert hharm using 1 <;> ring
    _=_ := by dsimp only [NuNumerator];ring

theorem actual_sparse_near_quadratic {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 600≤K) (hN : 63≤N) (hhi : N≤74320000)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,11*S.card≤N) :
    ((Near F K).card:ℝ)≤NuNumerator*(N:ℝ)^2/K+798*N := by
  have hKpos : 0<K := by omega
  have hNF : Near F K⊆F := fun S hS =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hNL : Legal (Ground N) (Near F K) :=
    ⟨fun S hS=>hlegal.1 S (hNF hS),fun S hS T hT he=>hlegal.2 S (hNF hS) T (hNF hT) he⟩
  apply actual_dyadic_sparse_core_first (fun S=>Level K S.card) hNL hK hN hhi
    (fun S hS=>hbad S (hNF hS)) (fun S hS=>hsize S (hNF hS))
  · intro S hS
    exact (actual_level_band hKpos (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2).1
  · intro S hS
    exact (actual_level_band hKpos (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2).2.le
  · intro S hS
    exact (Finset.mem_filter.mp hS).2

theorem actual_sparse_near_normalized {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 600≤K) (hN : 63≤N) (hhi : N≤74320000)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,11*S.card≤N) :
    ((Near F K).card:ℝ)/(N:ℝ)^2≤NuNumerator/K+798/N := by
  have hh := actual_sparse_near_quadratic hlegal hK hN hhi hbad hsize
  have hp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hk : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  have he : (NuNumerator/K+798/(N:ℝ))*(N:ℝ)^2=
      NuNumerator*(N:ℝ)^2/K+798*N := by field_simp [hp.ne',hk.ne']
  rwa [he]

theorem actual_sparse_tail_card_budget {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 600≤K) (hN : 63≤N) (hhi : N≤74320000)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,11*S.card≤N) :
    ((Tail F K).card:ℝ)≤NuNumerator*(N:ℝ)^2/K+798*N+
      ((F.filter (fun S=>3*K≤S.card ∧ ¬HasNearAPCore K S)).card:ℝ) := by
  have hpart := actual_tail_partition F K
  have hpartR : ((Near F K).card:ℝ)+((Far F K).card:ℝ)=(Tail F K).card := by exact_mod_cast hpart
  have hnear := actual_sparse_near_quadratic hlegal hK hN hhi hbad hsize
  have hfar : ((Far F K).card:ℝ)≤
      ((F.filter (fun S=>3*K≤S.card ∧ ¬HasNearAPCore K S)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (actual_far_subset_fixed (F:=F) (by omega : 0<K))
  linarith only [hpartR,hnear,hfar]

theorem actual_sparse_whole_normalized {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 600≤K) (hN : 63≤N) (hhi : N≤74320000)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,11*S.card≤N)
    (hlow : ∀S∈F,3*K≤S.card) :
    (F.card:ℝ)/(N:ℝ)^2≤NuNumerator/K+798/N+
      ((F.filter (fun S=>¬HasNearAPCore K S)).card:ℝ)/(N:ℝ)^2 := by
  have ht : Tail F K=F := Finset.filter_eq_self.mpr hlow
  have hf : F.filter (fun S=>3*K≤S.card ∧ ¬HasNearAPCore K S)=F.filter (fun S=>¬HasNearAPCore K S) := by
    ext S
    simp only [Finset.mem_filter]
    exact ⟨fun hs=>⟨hs.1,hs.2.2⟩,fun hs=>⟨hs.1,hlow S hs.1,hs.2⟩⟩
  have hh := actual_sparse_tail_card_budget hlegal hK hN hhi hbad hsize
  rw [ht,hf] at hh
  have hp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hk : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  have he : (NuNumerator/K+798/(N:ℝ)+
      ((F.filter (fun S=>¬HasNearAPCore K S)).card:ℝ)/(N:ℝ)^2)*(N:ℝ)^2=
      NuNumerator*(N:ℝ)^2/K+798*N+((F.filter (fun S=>¬HasNearAPCore K S)).card:ℝ) := by
    field_simp [hp.ne',hk.ne']
  rwa [he]

#print axioms exact_twelve_geometric_sum
#print axioms actual_harmonic_le19
#print axioms actual_sparse_level_lt12
#print axioms actual_dyadic_sparse_core_first
#print axioms actual_sparse_near_quadratic
#print axioms actual_sparse_near_normalized
#print axioms actual_sparse_tail_card_budget
#print axioms actual_sparse_whole_normalized
end
end JSP233.FiniteNear136
