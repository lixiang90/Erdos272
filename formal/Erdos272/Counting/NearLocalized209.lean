import Erdos272.Counting.NearWholeSlim209
import Erdos272.Resources.FarFinal112

namespace JSP233.NearLocalized209
open StarCompletion APGeometry NearAP36 NearWholeSlim209 HarmonicAbel29 BandAggregation34
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_level_lt {N K J : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hK : 0<K)
    (hN : N<3*K*2^J) (hlow : ∀ S∈F,3*Scale K (level S)≤S.card)
    {S : Finset ℤ} (hS : S∈F) : level S<J := by
  by_contra hn
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) (show J≤level S by omega)
  have hm := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right K hp)
  have hc : S.card≤N := by simpa only [ground_card] using Finset.card_le_card (hlegal.1 S hS)
  have hlo := hlow S hS
  dsimp only [Scale] at hlo
  nlinarith only [hm,hc,hlo,hN]

theorem actual_dyadic_core_first_quadratic {N K J : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<3*K*2^J)
    (hbad : ∀S∈F,¬IsAP S)
    (hlow : ∀S∈F,3*Scale K (level S)≤S.card)
    (hhigh : ∀S∈F,S.card≤6*Scale K (level S))
    (hnear : ∀S∈F,HasNearAPCore (Scale K (level S)) S) :
    (F.card:ℝ)≤(2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J*Harmonic N*N := by
  let family : ℕ→Finset (Finset ℤ) := fun j=>F.filter (fun S=>level S=j)
  have hfamily : ∀j,family j⊆F := fun j=>Finset.filter_subset _ _
  have hmaps : ∀S∈F,level S∈Finset.range J := by
    intro S hS
    exact Finset.mem_range.mpr (actual_level_lt level hlegal hK hN hlow hS)
  have hpart : F.card=∑j∈Finset.range J,(family j).card := Finset.card_eq_sum_card_fiberwise hmaps
  have hpartR : (F.card:ℝ)=∑j∈Finset.range J,((family j).card:ℝ) := by exact_mod_cast hpart
  have hrow : ∀j∈Finset.range J,((family j).card:ℝ)≤
      (2303/400:ℝ)*(N:ℝ)^2/K*(1/2:ℝ)^j+(7/2:ℝ)*N*Harmonic N := by
    intro j _hj
    have hLj : Legal (Ground N) (family j) :=
      ⟨fun S hS=>hlegal.1 S (hfamily j hS),fun S hS T hT he=>
        hlegal.2 S (hfamily j hS) T (hfamily j hT) he⟩
    have hh := actual_core_first_quadratic hLj (by positivity : 0<2^j*K)
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
  have hgeom := mul_le_mul_of_nonneg_left (dyadic_sum_le_two J)
    (by positivity : (0:ℝ)≤(2303/400:ℝ)*(N:ℝ)^2/K)
  calc
    _≤(2303/400:ℝ)*(N:ℝ)^2/K*(∑j∈Finset.range J,(1/2:ℝ)^j)+
      (J:ℝ)*((7/2:ℝ)*N*Harmonic N) := hs
    _≤(2303/400:ℝ)*(N:ℝ)^2/K*2+(J:ℝ)*((7/2:ℝ)*N*Harmonic N) :=
      add_le_add hgeom le_rfl
    _=_ := by ring

theorem actual_near_whole_quadratic {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<3*K*2^J)
    (hbad : ∀S∈F,¬IsAP S) :
    ((Near F K).card:ℝ)≤(2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J*Harmonic N*N := by
  have hNF : Near F K⊆F := fun S hS =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hNL : Legal (Ground N) (Near F K) :=
    ⟨fun S hS=>hlegal.1 S (hNF hS),fun S hS T hT he=>hlegal.2 S (hNF hS) T (hNF hT) he⟩
  apply actual_dyadic_core_first_quadratic (fun S => Level K S.card) hNL hK hN
    (fun S hS=>hbad S (hNF hS))
  · intro S hS
    exact (actual_level_band hK (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2).1
  · intro S hS
    exact (actual_level_band hK (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2).2.le
  · intro S hS
    exact (Finset.mem_filter.mp hS).2

theorem actual_tail_card_budget {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<3*K*2^J)
    (hbad : ∀S∈F,¬IsAP S) :
    ((Tail F K).card:ℝ)≤(2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J*Harmonic N*N+
      ((F.filter (fun S => 3*K≤S.card ∧ ¬HasNearAPCore K S)).card:ℝ) := by
  have hpart := actual_tail_partition F K
  have hpartR : ((Near F K).card:ℝ)+((Far F K).card:ℝ)=(Tail F K).card := by
    exact_mod_cast hpart
  have hnear := actual_near_whole_quadratic hlegal hK hN hbad
  have hfar : ((Far F K).card:ℝ)≤
      ((F.filter (fun S => 3*K≤S.card ∧ ¬HasNearAPCore K S)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (actual_far_subset_fixed (F:=F) hK)
  linarith only [hpartR,hnear,hfar]

theorem actual_whole_card_budget {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<3*K*2^J)
    (hbad : ∀S∈F,¬IsAP S) (hlow : ∀S∈F,3*K≤S.card) :
    (F.card:ℝ)≤(2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J*Harmonic N*N+
      ((F.filter (fun S => ¬HasNearAPCore K S)).card:ℝ) := by
  have ht : Tail F K=F := Finset.filter_eq_self.mpr hlow
  have hf : F.filter (fun S => 3*K≤S.card ∧ ¬HasNearAPCore K S)=
      F.filter (fun S => ¬HasNearAPCore K S) := by
    ext S
    simp only [Finset.mem_filter]
    exact ⟨fun hs => ⟨hs.1,hs.2.2⟩,fun hs => ⟨hs.1,hlow S hs.1,hs.2⟩⟩
  simpa only [ht,hf] using actual_tail_card_budget hlegal hK hN hbad

theorem actual_whole_normalized {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hN : N<3*K*2^J) (hpos : 0<N)
    (hbad : ∀S∈F,¬IsAP S) (hlow : ∀S∈F,3*K≤S.card) :
    (F.card:ℝ)/(N:ℝ)^2≤(2303/200:ℝ)/K+(7/2:ℝ)*J*Harmonic N/N+
      ((F.filter (fun S => ¬HasNearAPCore K S)).card:ℝ)/(N:ℝ)^2 := by
  have hh := actual_whole_card_budget hlegal hK hN hbad hlow
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hpos
  have hk : (0:ℝ)<K := Nat.cast_pos.mpr hK
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  have he : ((2303/200:ℝ)/K+(7/2:ℝ)*J*Harmonic N/N+
      ((F.filter (fun S => ¬HasNearAPCore K S)).card:ℝ)/(N:ℝ)^2)*(N:ℝ)^2=
      (2303/200:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*J*Harmonic N*N+
      ((F.filter (fun S => ¬HasNearAPCore K S)).card:ℝ) := by
    field_simp [hp.ne',hk.ne']
  rwa [he]

theorem actual_family_normalized {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0<K) (hN : 0<N) (hJ : N<3*K*2^J)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,3*K≤S.card) :
    (F.card : ℝ)/(N : ℝ)^2≤(2303/200 : ℝ)/K+
      2*(N : ℝ)/((K : ℝ)*((5*K/3 : ℕ) : ℝ)^2)+
      (7/2 : ℝ)*J*Harmonic N/N := by
  let H := F.filter (fun S=>¬HasNearAPCore K S)
  have hsub : H⊆F := Finset.filter_subset _ _
  have hHL : Legal (Ground N) H := ⟨fun S hS=>hF.1 S (hsub hS),
    fun S hS T hT hne=>hF.2 S (hsub hS) T (hsub hT) hne⟩
  have hfar := FarFinal112.actual_far_normalized hHL hK hN
    (fun S hS=>hsize S (hsub hS)) (fun S hS=>(Finset.mem_filter.mp hS).2)
  have hwhole := actual_whole_normalized hF hK hJ hN hbad hsize
  change (H.card : ℝ)/(N : ℝ)^2≤_ at hfar
  change (F.card : ℝ)/(N : ℝ)^2≤(2303/200 : ℝ)/K+
    (7/2 : ℝ)*J*Harmonic N/N+(H.card : ℝ)/(N : ℝ)^2 at hwhole
  linarith only [hfar,hwhole]

#print axioms actual_level_lt
#print axioms actual_dyadic_core_first_quadratic
#print axioms actual_near_whole_quadratic
#print axioms actual_whole_normalized
#print axioms actual_family_normalized
end
end JSP233.NearLocalized209
