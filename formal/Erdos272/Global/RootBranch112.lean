import Erdos272.Global.RootEnvelope112
import Erdos272.Counting.NearWhole112
import Erdos272.Global.SparseSmall39

/-! Actual first-omitter preparation for the whole root branch.
All root-bearing members and all actual avoiders are retained. The final
unpaid term is the cardinality of the actual Far subfamily, not a numerical
Far estimate or an assumed cardinality bound on the original family.
-/
namespace JSP233.RootBranch112
open StarCompletion SparseSmall39 NearAP36
open scoped Classical BigOperators
noncomputable section

theorem actual_minimum_omitter {F : Finset (Finset ℤ)} {c : ℤ}
    (homitter : ∃ T∈F,c∉T) :
    ∃ T∈Avoiders F c,∀ S∈Avoiders F c,T.card≤S.card := by
  have hV : (Avoiders F c).Nonempty := by
    obtain ⟨T,hTF,hTc⟩ := homitter
    exact ⟨T,Finset.mem_filter.mpr ⟨hTF,hTc⟩⟩
  exact Finset.exists_min_image (Avoiders F c) Finset.card hV

theorem degreeBudget_linear (N t : ℕ) : DegreeBudget N t≤t*N := by
  unfold DegreeBudget
  calc
    _≤∑ _i∈Finset.range t,N := Finset.sum_le_sum (fun i _ => by omega)
    _=_ := by simp

theorem actual_omitter_root_linear {N : ℕ} {F : Finset (Finset ℤ)}
    {c : ℤ} {T : Finset ℤ} (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hT : T∈F) (hTc : c∉T) :
    (RootPart F c).card≤T.card*N :=
  (actual_degree_from_omitter hlegal hbad hT hTc).trans (degreeBudget_linear N T.card)

theorem actual_root_normalized_min {N r L h : ℕ} {F : Finset (Finset ℤ)}
    {c : ℤ} {T : Finset ℤ} (hN : 4≤N) (hr : 2≤r)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F,¬IsAP S)
    (hsize : ∀ S∈F,r*S.card≤N) (hT : T∈F) (hTc : c∉T)
    (hband : T.card≤2*(2^h*L)) :
    ((RootPart F c).card:ℝ)/(N:ℝ)^2≤
      min ((2*(r:ℝ)-1)/(2*(r:ℝ)^2)) ((2*(L:ℝ)/N)*(2:ℝ)^h) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hrp : (0:ℝ)<r := by exact_mod_cast (by omega : 0<r)
  apply le_min
  · apply (div_le_iff₀ (sq_pos_of_pos hNp)).mpr
    have hb := actual_degree_sparse_rational hN hr hlegal hbad hsize ⟨T,hT,hTc⟩
    have herr : (0:ℝ)≤3*(N:ℝ)/(2*(r:ℝ)) := by positivity
    linarith
  · apply (div_le_iff₀ (sq_pos_of_pos hNp)).mpr
    have hb := (actual_omitter_root_linear hlegal hbad hT hTc).trans
      (Nat.mul_le_mul_right N hband)
    have hbR : ((RootPart F c).card:ℝ)≤2*((2:ℝ)^h*(L:ℝ))*N := by
      exact_mod_cast hb
    have he : ((2*(L:ℝ)/N)*(2:ℝ)^h)*(N:ℝ)^2=
        2*((2:ℝ)^h*(L:ℝ))*N := by field_simp
    rwa [he]

theorem actual_first_omitter_scale {K : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hK : 0<K) (hsmall : ∀ S∈F,S.card≤3*K→c∈S)
    (homitter : ∃ T∈F,c∉T) :
    ∃ T∈Avoiders F c,∃ h:ℕ,
      3*NearWhole112.Scale K h<T.card ∧ T.card≤6*NearWhole112.Scale K h ∧
      ∀ S∈Avoiders F c,3*NearWhole112.Scale K h≤S.card := by
  obtain ⟨T,hTV,hmin⟩ := actual_minimum_omitter homitter
  obtain ⟨hTF,hTc⟩ := Finset.mem_filter.mp hTV
  have hlarge : 3*K<T.card := by
    by_contra hn
    exact hTc (hsmall T hTF (by omega))
  obtain ⟨h,hlo,hhi⟩ := CrossBand57.actual_band_exists (by positivity : 0<3*K) hlarge
  have hlo' : 3*NearWhole112.Scale K h<T.card := by
    simpa only [CrossBand57.Scale,NearWhole112.Scale,mul_assoc,mul_comm,mul_left_comm] using hlo
  have hhi' : T.card≤6*NearWhole112.Scale K h := by
    dsimp only [CrossBand57.Scale] at hhi
    dsimp only [NearWhole112.Scale]
    nlinarith only [hhi]
  exact ⟨T,Finset.mem_filter.mpr ⟨hTF,hTc⟩,h,hlo',hhi',
    fun S hS => (Nat.le_of_lt hlo').trans (hmin S hS)⟩

theorem actual_first_omitter_near_far_budget
    {N r K J : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 4≤N) (hr : 2≤r) (hK : 0<K) (hNJ : N<2^J)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F,¬IsAP S)
    (hsize : ∀ S∈F,r*S.card≤N)
    (hsmall : ∀ S∈F,S.card≤3*K→c∈S) (homitter : ∃ T∈F,c∉T) :
    ∃ h:ℕ,(F.card:ℝ)/(N:ℝ)^2≤
      min ((2*(r:ℝ)-1)/(2*(r:ℝ)^2)) ((6*(K:ℝ)/N)*(2:ℝ)^h)+
      ((2303/200:ℝ)/K)/(2:ℝ)^h+(7/2:ℝ)*J^2/N+
      (((Avoiders F c).filter (fun S => ¬HasNearAPCore (NearWhole112.Scale K h) S)).card:ℝ)/(N:ℝ)^2 := by
  obtain ⟨T,hTV,h,hlo,hhi,hlow⟩ := actual_first_omitter_scale hK hsmall homitter
  obtain ⟨hTF,hTc⟩ := Finset.mem_filter.mp hTV
  have hroot := actual_root_normalized_min (L:=3*K) (h:=h) hN hr hlegal hbad hsize hTF hTc (by
    dsimp only [NearWhole112.Scale] at hhi
    nlinarith only [hhi])
  have hVF : Avoiders F c⊆F := Finset.filter_subset _ _
  have hVL : Legal (Ground N) (Avoiders F c) :=
    ⟨fun S hS => hlegal.1 S (hVF hS),
      fun S hS U hU he => hlegal.2 S (hVF hS) U (hVF hU) he⟩
  have hnear := NearWhole112.actual_whole_normalized hVL
    (by unfold NearWhole112.Scale;positivity : 0<NearWhole112.Scale K h)
    hNJ (by omega) (fun S hS => hbad S (hVF hS)) hlow
  have hscale : (2303/200:ℝ)/(NearWhole112.Scale K h:ℝ)=
      ((2303/200:ℝ)/K)/(2:ℝ)^h := by
    simp only [NearWhole112.Scale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  rw [hscale] at hnear
  have hlinear : 2*((3*K:ℕ):ℝ)/(N:ℝ)=6*(K:ℝ)/N := by push_cast;ring
  rw [hlinear] at hroot
  have hp : ((RootPart F c).card:ℝ)/(N:ℝ)^2+
      ((Avoiders F c).card:ℝ)/(N:ℝ)^2=(F.card:ℝ)/(N:ℝ)^2 := by
    rw [←add_div,←Nat.cast_add,root_avoider_card_partition]
  exact ⟨h,by linarith⟩

#print axioms actual_minimum_omitter
#print axioms degreeBudget_linear
#print axioms actual_omitter_root_linear
#print axioms actual_root_normalized_min
#print axioms actual_first_omitter_scale
#print axioms actual_first_omitter_near_far_budget
end
end JSP233.RootBranch112
