import Erdos272.Arithmetic.IntegerHighPrices209
import Erdos272.Counting.NearLocalized209
import Erdos272.Resources.GlobalBootstrap209
import Erdos272.Global.GlobalSeven208

namespace JSP233.IntegerHighRoot209
open StarCompletion APGeometry NearAP36 DenseDeletion40 Density41 SparseSmall39
open HarmonicAbel29 SevenFamily208 SevenPrices208 GlobalSeven208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 200000

theorem actual_sparse_density {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 10902≤N) (hhi : N≤62443451) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    (71/800 : ℝ)*(N : ℝ)^2-142*N<((SparseCrooked N 11 F).card : ℝ) := by
  have hAP:=GlobalSeven208.actual_flat_AP (by omega : 1≤N) hF
  have hl:=GlobalSeven208.original_lower hcard
  have hd:=DenseDeletion208.actual_deleted11_affine hN hF
  have hdR : ((Deleted N 11 F).card : ℝ)≤121*(N : ℝ)+968 := by exact_mod_cast hd
  have hp:=actual_original_three_part_partition N 11 F
  have hpR : ((APPart F).card : ℝ)+(SparseCrooked N 11 F).card+(Deleted N 11 F).card=F.card := by exact_mod_cast hp
  have hH:=mul_le_mul_of_nonneg_right (GlobalBootstrap209.harmonic_cap hN hhi)
    (Nat.cast_nonneg (α := ℝ) N)
  have hn : (10902 : ℝ)≤N := by exact_mod_cast hN
  nlinarith only [hAP,hl,hdR,hpR,hH,hn]

theorem actual_sparse_two {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 705098≤N) (hhi : N≤62443451) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    2≤(SparseCrooked N 11 F).card := by
  have hd:=actual_sparse_density (by omega : 10902≤N) hhi hF hcard
  have hn : (705098 : ℝ)≤N := by exact_mod_cast hN
  by_contra h
  have hc : ((SparseCrooked N 11 F).card : ℝ)≤1 := by exact_mod_cast (show (SparseCrooked N 11 F).card≤1 by omega)
  nlinarith only [hd,hn,hc]

theorem actual_scale {M t : ℕ} (hM : 0<M) (ht : 4*M≤t) :
    ∃j : ℕ,2≤j ∧ M*2^j≤t ∧ t≤2*M*2^j := by
  let q:=t/M
  have hq : 4≤q := (Nat.le_div_iff_mul_le hM).mpr (by omega)
  let j:=Nat.log 2 q
  have hj : 2≤j := by
    apply (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : q≠0)).mpr
    norm_num
    exact hq
  have hl:=Nat.pow_log_le_self 2 (by omega : q≠0)
  have hu:=Nat.lt_pow_succ_log_self (by decide : 1<2) q
  have hprod:=Nat.div_mul_le_self t M
  have hquot : t<2^(j+1)*M := (Nat.div_lt_iff_lt_mul hM).mp hu
  have hm:=Nat.mul_le_mul_right M hl
  refine ⟨j,hj,?_,?_⟩
  · dsimp only [j] at *
    change q*M≤t at hprod
    nlinarith only [hm,hprod]
  · rw [pow_succ] at hquot
    nlinarith only [hquot]

theorem actual_high_payment {N j : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (w : Fin 11) (hlo : IntegerHighPrices209.Lower w≤N) (hhi : N≤IntegerHighPrices209.Upper w)
    (hG : Legal (Ground N) G) (hbad : ∀S∈G,¬IsAP S) (hT : T∈Avoiders G c)
    (hmin : ∀S∈Avoiders G c,T.card≤S.card) (hj : 2≤j)
    (hl : IntegerHighPrices209.M w*2^j≤T.card) (hu : T.card≤2*IntegerHighPrices209.M w*2^j)
    (hsp : 11*T.card≤N) :
    (G.card : ℝ)/(N : ℝ)^2≤Budget-142/(N : ℝ) := by
  have hw:=IntegerHighPrices209.data_range w
  have hn : (705098 : ℝ)≤N := by exact_mod_cast (hw.2.1.trans hlo)
  have hN0 : (0 : ℝ)<N := by linarith only [hn]
  obtain ⟨hTG,hTc⟩:=Finset.mem_filter.mp hT
  have hjmax:=IntegerHighPrices209.scale_index w hhi (by nlinarith only [hl,hsp])
  obtain ⟨hK,hKs,hD⟩:=IntegerHighPrices209.minimum_size w j hj hjmax
  have hAL : Legal (Ground N) (Avoiders G c) :=
    ⟨fun S hS=>hG.1 S (Finset.mem_filter.mp hS).1,
      fun S hS R hR hSR=>hG.2 S (Finset.mem_filter.mp hS).1 R (Finset.mem_filter.mp hR).1 hSR⟩
  have hA:=NearLocalized209.actual_family_normalized hAL hK (by omega : 0<N)
    (hhi.trans_lt (IntegerHighPrices209.level_cutoff w j hj hjmax))
    (fun S hS=>hbad S (Finset.mem_filter.mp hS).1)
    (fun S hS=>hKs.trans (hl.trans (hmin S hS)))
  have hH:=GlobalBootstrap209.harmonic_cap (by omega : 10902≤N) (hhi.trans hw.2.2.1)
  have hHpay:=mul_le_mul_of_nonneg_left hH
    (show (0 : ℝ)≤(7/2 : ℝ)*(IntegerHighPrices209.Levels w j : ℝ)/(N : ℝ) by positivity)
  have hHpay' : (7/2 : ℝ)*(IntegerHighPrices209.Levels w j : ℝ)*Harmonic N/N≤
      (7/2 : ℝ)*(IntegerHighPrices209.Levels w j : ℝ)*19/N := by
    simpa only [div_mul_eq_mul_div] using hHpay
  have hApaid : ((Avoiders G c).card : ℝ)/(N : ℝ)^2≤
      (2303/200 : ℝ)/(IntegerHighPrices209.K w j : ℝ)+
      2*(N : ℝ)/((IntegerHighPrices209.K w j : ℝ)*((5*IntegerHighPrices209.K w j/3 : ℕ) : ℝ)^2)+
      (7/2 : ℝ)*(IntegerHighPrices209.Levels w j : ℝ)*19/N := by linarith only [hA,hHpay']
  have hr : ((RootPart G c).card : ℝ)/(N : ℝ)^2≤
      if j≤6 then ((2*IntegerHighPrices209.M w*2^j : ℕ) : ℝ)/N else Beta := by
    by_cases hj6 : j≤6
    · rw [if_pos hj6]
      have hdegree:=actual_degree_from_omitter hG hbad hTG hTc
      have hlinear : DegreeBudget N T.card≤T.card*N := by
        unfold DegreeBudget
        calc
          _≤∑_i∈Finset.range T.card,N := Finset.sum_le_sum (fun i hi=>by omega)
          _=_ := by simp [mul_comm]
      have hb:=(hdegree.trans hlinear).trans (Nat.mul_le_mul_right N hu)
      have hbR : ((RootPart G c).card : ℝ)≤((2*IntegerHighPrices209.M w*2^j : ℕ) : ℝ)*N := by exact_mod_cast hb
      apply (div_le_iff₀ (sq_pos_of_pos hN0)).mpr
      have he : (((2*IntegerHighPrices209.M w*2^j : ℕ) : ℝ)/(N : ℝ))*(N : ℝ)^2=
          ((2*IntegerHighPrices209.M w*2^j : ℕ) : ℝ)*N := by field_simp
      rw [he]
      exact hbR
    · rw [if_neg hj6]
      have hq:=RootQuadratic208.actual_root_scale_envelope (by omega : 4≤N) hG hbad hTG hTc hu hsp
      have hm:=RootQuadratic208.q_mono
        (min_le_right (2*(IntegerHighPrices209.M w : ℝ)*((2^j : ℕ) : ℝ)/(N : ℝ)) (1/11 : ℝ))
        (by norm_num : (1/11 : ℝ)≤1)
      have he : RootQuadratic208.Q (1/11 : ℝ)=Beta := by norm_num [RootQuadratic208.Q,Beta]
      rw [he] at hm
      exact hq.trans hm
  have hpart:=RootQuadratic208.actual_partition_payment hr hApaid
  have he : (if j≤6 then ((2*IntegerHighPrices209.M w*2^j : ℕ) : ℝ)/(N : ℝ) else Beta)+
      ((2303/200 : ℝ)/(IntegerHighPrices209.K w j : ℝ)+
        2*(N : ℝ)/((IntegerHighPrices209.K w j : ℝ)*((5*IntegerHighPrices209.K w j/3 : ℕ) : ℝ)^2)+
        (7/2 : ℝ)*(IntegerHighPrices209.Levels w j : ℝ)*19/N)+142/N=
      IntegerHighPrices209.High w j N := by
    unfold IntegerHighPrices209.High ReciprocalPrice208.Price
    split_ifs <;> ring
  have hprice:=IntegerHighPrices209.high_window (n := (N : ℝ)) w j hj hjmax
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  linarith only [hpart,he,hprice]

theorem actual_high_contradiction {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (w : Fin 11) (hlo : IntegerHighPrices209.Lower w≤N) (hhi : N≤IntegerHighPrices209.Upper w)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card) (hT : T∈Avoiders (SparseCrooked N 11 F) c)
    (hmin : ∀S∈Avoiders (SparseCrooked N 11 F) c,T.card≤S.card)
    (hsize : 4*IntegerHighPrices209.M w≤T.card) : False := by
  have hw:=IntegerHighPrices209.data_range w
  have hG:=actual_sparse_legal (r := 11) hF
  have hbad : ∀S∈SparseCrooked N 11 F,¬IsAP S := fun S hS=>(actual_sparse_membership.mp hS).2.1
  have hsp:=(actual_sparse_membership.mp (Finset.mem_filter.mp hT).1).2.2
  obtain ⟨j,hj,hl,hu⟩:=actual_scale (by omega : 0<IntegerHighPrices209.M w) hsize
  have hp:=actual_high_payment w hlo hhi hG hbad hT hmin hj hl hu hsp
  have hd:=actual_sparse_density (by omega : 10902≤N) (hhi.trans hw.2.2.1) hF hcard
  have hn : (705098 : ℝ)≤N := by exact_mod_cast (hw.2.1.trans hlo)
  have hN0 : (0 : ℝ)<N := by linarith only [hn]
  have hpaid:=(div_le_iff₀ (sq_pos_of_pos hN0)).mp hp
  have he : (Budget-142/(N : ℝ))*(N : ℝ)^2=Budget*(N : ℝ)^2-142*N := by field_simp
  rw [he] at hpaid
  have hb:=mul_le_mul_of_nonneg_right (show Budget≤(71/800 : ℝ) by norm_num [Budget]) (sq_nonneg (N : ℝ))
  nlinarith only [hd,hpaid,hb]

#print axioms actual_sparse_density
#print axioms actual_sparse_two
#print axioms actual_scale
#print axioms actual_high_payment
#print axioms actual_high_contradiction
end
end JSP233.IntegerHighRoot209
