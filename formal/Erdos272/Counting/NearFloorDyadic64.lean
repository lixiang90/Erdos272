module

public import Erdos272.Counting.NearFloorAnalytic64
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.NearFloorDyadic64
open NearFloorAnalytic64 NearFloor63 HarmonicAbel29 BandAggregation34
open StarCompletion APGeometry NearAP36
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_nearAP_quadratic_budget {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K)
    (hbad : ∀S∈F,¬IsAP S) (hlow : ∀S∈F,3*K+1≤S.card)
    (hhigh : ∀S∈F,S.card≤6*K) (hnear : ∀S∈F,HasNearAPCore K S) :
    (F.card:ℝ)≤(2303/400:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*N*Harmonic N := by
  have hh := actual_near_members_quadratic_budget hlegal hK hbad hlow hhigh
  have he : NearMembers K F=F := Finset.filter_eq_self.mpr hnear
  rwa [he] at hh

theorem actual_harmonic_le_exponent {N J : ℕ} (hN : N<2^J) : Harmonic N≤(J:ℝ) := by
  by_cases hJ : 2≤J
  · have hh := HarmonicSharp39.actual_harmonic_tight N J hN
    have hjR : (2:ℝ)≤J := by exact_mod_cast hJ
    linarith only [hh,hjR]
  · by_cases hz : J=0
    · subst J
      have hn : N=0 := by norm_num at hN;omega
      subst N
      simp [Harmonic]
    · have hj : J=1 := by omega
      subst J
      have hn : N≤1 := by norm_num at hN;omega
      have hh := harmonic_mono hn
      simpa [Harmonic] using hh

theorem actual_member_level_lt {N K J : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<2^J)
    (hlow : ∀S∈F,3*(2^(level S)*K)+1≤S.card) {S : Finset ℤ} (hS : S∈F) :
    level S<J := by
  by_contra hn
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) (show J≤level S by omega)
  have hm := Nat.mul_le_mul_left (2^(level S)) (show 1≤K by omega)
  have hc : S.card≤N := by simpa only [ground_card] using Finset.card_le_card (hlegal.1 S hS)
  have hlo := hlow S hS
  nlinarith only [hp,hm,hc,hlo,hN]

theorem actual_dyadic_near_quadratic {N K J : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<2^J)
    (hbad : ∀S∈F,¬IsAP S)
    (hlow : ∀S∈F,3*(2^(level S)*K)+1≤S.card)
    (hhigh : ∀S∈F,S.card≤6*(2^(level S)*K))
    (hnear : ∀S∈F,HasNearAPCore (2^(level S)*K) S) :
    (F.card:ℝ)≤(2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J^2*N := by
  let family : ℕ→Finset (Finset ℤ) := fun j=>F.filter (fun S=>level S=j)
  have hfamily : ∀j,family j⊆F := fun j=>Finset.filter_subset _ _
  have hmaps : ∀S∈F,level S∈Finset.range J := by
    intro S hS
    exact Finset.mem_range.mpr (actual_member_level_lt level hlegal hK hN hlow hS)
  have hpart : F.card=∑j∈Finset.range J,(family j).card := Finset.card_eq_sum_card_fiberwise hmaps
  have hpartR : (F.card:ℝ)=∑j∈Finset.range J,((family j).card:ℝ) := by exact_mod_cast hpart
  have hrow : ∀j∈Finset.range J,((family j).card:ℝ)≤
      (2303/400:ℝ)*(N:ℝ)^2/K*(1/2:ℝ)^j+(7/2:ℝ)*N*Harmonic N := by
    intro j _hj
    have hLj : Legal (Ground N) (family j) :=
      ⟨fun S hS=>hlegal.1 S (hfamily j hS),fun S hS T hT he=>
        hlegal.2 S (hfamily j hS) T (hfamily j hT) he⟩
    have hh := actual_nearAP_quadratic_budget hLj (by positivity : 0<2^j*K)
      (fun S hS=>hbad S (hfamily j hS)) (by
        intro S hS
        simpa only [(Finset.mem_filter.mp hS).2] using hlow S (hfamily j hS)) (by
        intro S hS
        simpa only [(Finset.mem_filter.mp hS).2] using hhigh S (hfamily j hS)) (by
        intro S hS
        simpa only [(Finset.mem_filter.mp hS).2] using hnear S (hfamily j hS))
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
  have hgeom := mul_le_mul_of_nonneg_left (dyadic_sum_le_two J)
    (by positivity : (0:ℝ)≤(2303/400:ℝ)*(N:ℝ)^2/K)
  have hharm := mul_le_mul_of_nonneg_left (actual_harmonic_le_exponent hN)
    (by positivity : (0:ℝ)≤(J:ℝ)*((7/2:ℝ)*N))
  calc
    _≤(2303/400:ℝ)*(N:ℝ)^2/K*(∑j∈Finset.range J,(1/2:ℝ)^j)+
      (J:ℝ)*((7/2:ℝ)*N*Harmonic N) := hs
    _≤(2303/400:ℝ)*(N:ℝ)^2/K*2+(J:ℝ)*((7/2:ℝ)*N*J) := by
      apply add_le_add hgeom
      convert hharm using 1 <;> ring
    _=_ := by ring

theorem actual_dyadic_near_members_quadratic {N K J : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<2^J)
    (hbad : ∀S∈F,¬IsAP S)
    (hlow : ∀S∈F,3*(2^(level S)*K)+1≤S.card)
    (hhigh : ∀S∈F,S.card≤6*(2^(level S)*K)) :
    ((F.filter (fun S=>HasNearAPCore (2^(level S)*K) S)).card:ℝ)≤
      (2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J^2*N := by
  let G := F.filter (fun S=>HasNearAPCore (2^(level S)*K) S)
  have hGF : G⊆F := Finset.filter_subset _ _
  exact actual_dyadic_near_quadratic level
    (show Legal (Ground N) G from ⟨fun S hS=>hlegal.1 S (hGF hS),
      fun S hS T hT he=>hlegal.2 S (hGF hS) T (hGF hT) he⟩) hK hN
    (fun S hS=>hbad S (hGF hS)) (fun S hS=>hlow S (hGF hS))
    (fun S hS=>hhigh S (hGF hS)) (fun S hS=>(Finset.mem_filter.mp hS).2)

#print axioms actual_nearAP_quadratic_budget
#print axioms actual_harmonic_le_exponent
#print axioms actual_member_level_lt
#print axioms actual_dyadic_near_quadratic
#print axioms actual_dyadic_near_members_quadratic
end
end JSP233.NearFloorDyadic64
