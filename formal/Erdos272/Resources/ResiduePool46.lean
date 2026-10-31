import Erdos272.Geometry.ResidueSpacing46
import Erdos272.Resources.MeetingPool46
import Erdos272.Geometry.RootedIntervals46

/-! The actual interval/witness pool for an actual step-at-least-three avoider. -/
namespace JSP233.ResiduePool46
open StarCompletion WitnessInterval43 ResidueSpacing46 MeetingPool46
open scoped Classical
noncomputable section

theorem large_step_pool_polynomial {n l w h j : ℝ}
    (hn : 6≤n) (hl : 0≤l) (hw : 0≤w) (hlen : l+w≤n)
    (hhw : h≤w) (hh : 3*h≤w+6) (hj : 3*j≤l+6) :
    l^2/4+h*n-h^2/2+j*(w-h)≤5*n^2/18+3*n := by
  let A := w/3+2
  let B := l/3+2
  have hA : h≤A := by dsimp [A];linarith only [hh]
  have hB : j≤B := by dsimp [B];linarith only [hj]
  have hAB : A+B≤n := by dsimp [A,B];linarith only [hlen,hn]
  have hfirst := mul_le_mul_of_nonneg_right hB (sub_nonneg.mpr hhw)
  have hsecond := mul_nonneg (sub_nonneg.mpr hA)
    (show 0≤n-B-(h+A)/2 by linarith only [hA,hAB])
  have hcount : l^2/4+h*n-h^2/2+j*(w-h)≤l^2/4+A*n-A^2/2+B*(w-A) := by
    nlinarith only [hfirst,hsecond]
  have hprod := mul_nonneg (show 0≤n-l-w by linarith only [hlen])
    (show 0≤5*n+5*l-w by linarith only [hlen,hl,hw])
  have hmain : l^2/4+w*n/3-w^2/18+2*l*w/9≤5*n^2/18 := by
    nlinarith only [hprod,sq_nonneg l]
  dsimp only [A,B] at hcount
  nlinarith only [hcount,hmain,hlen,hl,hn]

theorem actual_interval_pool_sparse_residue {N : ℕ} {P : Finset ℤ} {c a k u v : ℤ}
    (hN : 6≤N) (hcN : c∈Ground N) (hP : P⊆Ground N) (hcP : c∉P)
    (hu : 1≤u) (huc : u≤c) (hcv : c≤v) (hv : v≤N)
    (hk : 3≤k) (hmod : ∀ x∈P,k∣x-a) :
    ((IntervalPool (Ground N) c u v P).card:ℝ)≤5*(N:ℝ)^2/18+3*N := by
  let U := (Ground N).erase c
  let B := (Finset.Icc u v).erase c
  have hBU : B⊆U := by
    intro x hx
    obtain ⟨hxc,hxI⟩ := Finset.mem_erase.mp hx
    have hh := Finset.mem_Icc.mp hxI
    exact Finset.mem_erase.mpr ⟨hxc,(mem_ground N x).mpr (by omega)⟩
  have hPU : P⊆U := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun he=>hcP (he ▸ hx),hP hx⟩
  have hUc : U.card≤N := by
    have hh := Finset.card_le_card (Finset.erase_subset (s:=Ground N) c)
    simpa only [ground_card] using hh
  have hLR : ((Finset.Ico u c).card:ℝ)+(Finset.Ioc c v).card=B.card := by
    have hcB : c∈Finset.Icc u v := Finset.mem_Icc.mpr ⟨huc,hcv⟩
    have hh : B.card+1=(Finset.Icc u v).card := Finset.card_erase_add_one hcB
    have hh2 : (Finset.Ico u c).card+(Finset.Ioc c v).card=B.card := by
      rw [Int.card_Icc] at hh
      rw [Int.card_Ico,Int.card_Ioc]
      omega
    exact_mod_cast hh2
  have hcross : ((Finset.Ico u c).card:ℝ)*(Finset.Ioc c v).card≤(B.card:ℝ)^2/4 := by
    nlinarith only [hLR,sq_nonneg (((Finset.Ico u c).card:ℝ)-(Finset.Ioc c v).card)]
  have hUcR : (U.card:ℝ)≤N := by exact_mod_cast hUc
  have hmN := mul_le_mul_of_nonneg_left hUcR
    (Nat.cast_nonneg (α:=ℝ) (P\B).card)
  have hm := actual_meeting_outside_card_le hBU hPU
  have hparts := actual_ground_residue_parts hcN hP hcP hu huc hcv hv hk hmod
  have hh : 3*((P\B).card:ℝ)≤((U\B).card:ℝ)+6 := by exact_mod_cast hparts.1
  have hj : 3*((P∩B).card:ℝ)≤(B.card:ℝ)+6 := by
    have hh : 3*((P∩B).card:ℝ)≤(B.card:ℝ)+4 := by exact_mod_cast hparts.2
    linarith only [hh]
  have hlen : (B.card:ℝ)+(U\B).card≤(N:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card hBU
    have hnat : B.card+(U\B).card≤N := by omega
    exact_mod_cast hnat
  have hhw : ((P\B).card:ℝ)≤(U\B).card := by
    exact_mod_cast Finset.card_le_card (show P\B⊆U\B by
      intro x hx
      obtain ⟨hxP,hxB⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨hPU hxP,hxB⟩)
  have hp := large_step_pool_polynomial (by exact_mod_cast hN)
    (Nat.cast_nonneg B.card) (Nat.cast_nonneg (U\B).card) hlen hhw hh hj
  have he := actual_interval_pool_card (Ground N) P c u v
  have heR : ((IntervalPool (Ground N) c u v P).card:ℝ)=
      ((Finset.Ico u c).card:ℝ)*(Finset.Ioc c v).card+
        (MeetingOutsidePairs U B P).card := by exact_mod_cast he
  nlinarith only [heR,hcross,hm,hmN,hp]

theorem actual_supported_envelope_ground {N : ℕ} {F : Finset (Finset ℤ)}
    {c u v : ℤ} (hcN : c∈Ground N) (hF : Legal (Ground N) F)
    (hE : SupportedEnvelope F c u v) : 1≤u ∧ u≤c ∧ c≤v ∧ v≤N := by
  obtain ⟨huc,hcv,hl,hr⟩ := hE
  have hu : u∈Ground N := by
    rcases hl with he|⟨T,hT,_hAP,hs⟩
    · exact he ▸ hcN
    · exact hF.1 T hT (hs (Finset.mem_Icc.mpr ⟨le_rfl,huc⟩))
  have hv : v∈Ground N := by
    rcases hr with he|⟨T,hT,_hAP,hs⟩
    · exact he ▸ hcN
    · exact hF.1 T hT (hs (Finset.mem_Icc.mpr ⟨hcv,le_rfl⟩))
  exact ⟨((mem_ground N u).mp hu).1,huc,hcv,((mem_ground N v).mp hv).2⟩

theorem actual_avoider_sparse_joint_harmonic {N : ℕ} {F : Finset (Finset ℤ)}
    {c a k : ℤ} {P : Finset ℤ} (hN : 6≤N) (hcN : c∈Ground N)
    (hF : Legal (Ground N) F) (hP : P∈F) (hcP : c∉P)
    (hc : ∀ S∈F,¬IsAP S→c∈S) (hk : 3≤k) (hmod : ∀ x∈P,k∣x-a) :
    ((PrivatePairExistence.CrookedMembers F).card:ℝ)+(StraddledIntervals F c).card≤
      5*(N:ℝ)^2/18+3*N+6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  obtain ⟨u,v,hE,hh⟩ := DivisorMoment45.actual_avoider_joint_harmonic c P hcN hF hP hcP hc
  obtain ⟨hu,huc,hcv,hv⟩ := actual_supported_envelope_ground hcN hF hE
  have hp := actual_interval_pool_sparse_residue hN hcN (hF.1 P hP) hcP hu huc hcv hv hk hmod
  linarith only [hh,hp]

theorem actual_avoider_sparse_joint_APAt {N : ℕ} {F : Finset (Finset ℤ)}
    {c a k : ℤ} {P : Finset ℤ} (hN : 6≤N) (hcN : c∈Ground N)
    (hF : Legal (Ground N) F) (hP : P∈F) (hcP : c∉P)
    (hc : ∀ S∈F,¬IsAP S→c∈S) (hk : 3≤k) (hAP : APGeometry.APAt k a P) :
    ((PrivatePairExistence.CrookedMembers F).card:ℝ)+(StraddledIntervals F c).card≤
      5*(N:ℝ)^2/18+3*N+6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  obtain ⟨_hk,lo,hi,hr⟩ := hAP
  exact actual_avoider_sparse_joint_harmonic hN hcN hF hP hcP hc hk
    (fun x hx=>((hr x).mp hx).2.2)

theorem actual_avoider_sparse_rooted_harmonic {N : ℕ} {F : Finset (Finset ℤ)}
    {c a k : ℤ} {P : Finset ℤ} (hN : 6≤N) (hcN : c∈Ground N)
    (hF : Legal (Ground N) F) (hP : P∈F) (hcP : c∉P)
    (hc : ∀ S∈F,¬IsAP S→c∈S) (hk : 3≤k) (hmod : ∀ x∈P,k∣x-a) :
    ((PrivatePairExistence.CrookedMembers F).card:ℝ)+(RootedIntervals46.RootedIntervals F c).card≤
      5*(N:ℝ)^2/18+5*N+6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  have hh := actual_avoider_sparse_joint_harmonic hN hcN hF hP hcP hc hk hmod
  have hb : ((RootedIntervals46.RootedIntervals F c).card:ℝ)≤
      (StraddledIntervals F c).card+2*(N:ℝ) := by
    exact_mod_cast RootedIntervals46.actual_legal_rooted_intervals_card_le N F c hF
  linarith only [hh,hb]

theorem actual_avoider_sparse_rooted_APAt {N : ℕ} {F : Finset (Finset ℤ)}
    {c a k : ℤ} {P : Finset ℤ} (hN : 6≤N) (hcN : c∈Ground N)
    (hF : Legal (Ground N) F) (hP : P∈F) (hcP : c∉P)
    (hc : ∀ S∈F,¬IsAP S→c∈S) (hk : 3≤k) (hAP : APGeometry.APAt k a P) :
    ((PrivatePairExistence.CrookedMembers F).card:ℝ)+(RootedIntervals46.RootedIntervals F c).card≤
      5*(N:ℝ)^2/18+5*N+6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  obtain ⟨_hk,lo,hi,hr⟩ := hAP
  exact actual_avoider_sparse_rooted_harmonic hN hcN hF hP hcP hc hk
    (fun x hx=>((hr x).mp hx).2.2)

theorem actual_avoider_sparse_rooted_tight_dyadic {N J : ℕ} {F : Finset (Finset ℤ)}
    {c a k : ℤ} {P : Finset ℤ} (hN : 6≤N) (hcN : c∈Ground N) (hNJ : N<2^J)
    (hF : Legal (Ground N) F) (hP : P∈F) (hcP : c∉P)
    (hc : ∀ S∈F,¬IsAP S→c∈S) (hk : 3≤k) (hmod : ∀ x∈P,k∣x-a) :
    ((PrivatePairExistence.CrookedMembers F).card:ℝ)+(RootedIntervals46.RootedIntervals F c).card≤
      5*(N:ℝ)^2/18+5*N+6*(N:ℝ)*(53/100+(7/10:ℝ)*J)^3 := by
  have hh := actual_avoider_sparse_rooted_harmonic hN hcN hF hP hcP hc hk hmod
  have hH := HarmonicSharp39.actual_harmonic_tight N J hNJ
  have hnon : 0≤HarmonicAbel29.Harmonic N := by
    unfold HarmonicAbel29.Harmonic
    exact Finset.sum_nonneg (fun _ _=>by positivity)
  have hp : HarmonicAbel29.Harmonic N^3≤(53/100+(7/10:ℝ)*J)^3 := by gcongr
  have hm := mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤6*(N:ℝ) by positivity)
  linarith only [hh,hm]

#print axioms large_step_pool_polynomial
#print axioms actual_interval_pool_sparse_residue
#print axioms actual_supported_envelope_ground
#print axioms actual_avoider_sparse_joint_harmonic
#print axioms actual_avoider_sparse_joint_APAt
#print axioms actual_avoider_sparse_rooted_harmonic
#print axioms actual_avoider_sparse_rooted_APAt
#print axioms actual_avoider_sparse_rooted_tight_dyadic
end
end JSP233.ResiduePool46
