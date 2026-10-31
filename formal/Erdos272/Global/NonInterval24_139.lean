import Erdos272.Global.NonInterval53

/-! The actual noninterval gap needs only 1024 J^3, preserving the complete
count, actual root, actual omitter and the full witness exception. -/
namespace JSP233.NonInterval24_139
open StarCompletion PrivatePairExistence LongTerminal35 WitnessInterval43 RestrictedWitness44
open APGeometry APCount41 APLinearCount49 APExterior50 APPrepare49 NonIntervalAP47
open MeetingPool46 DivisorMoment45 KKRetention32 ThinFringe33 NonInterval53
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 5000000

theorem actual_noninterval_family_gap {N J c L : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (hN : 6≤N) (hNJ : N<2^J) (hcN : (c:ℤ)∈Ground N)
    (hF : Legal (Ground N) G) (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hcL : c≤L) (hLN : L≤N)
    (hlow : ∀S∈Avoiders G (c:ℤ),∃a∈S,a≤(L:ℤ))
    (hP : P∈G) (hcP : (c:ℤ)∉P) (hno : ¬IsInterval P)
    (hscale : 24*L≤N) (hJcube : 1024*J^3≤N) :
    (G.card:ℝ)≤11*(N:ℝ)^2/24 := by
  have hJ : 2≤J := by
    by_contra hn
    have hh:J≤1 := by omega
    interval_cases J <;>norm_num at hNJ <;>omega
  have hJR : (2:ℝ)≤J := by exact_mod_cast hJ
  have hNN : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hH := HarmonicSharp39.actual_harmonic_tight N J hNJ
  have hH0 := HarmonicAbel29.harmonic_nonneg N
  have hHJ : HarmonicAbel29.Harmonic N≤(J:ℝ) := by linarith only [hH,hJR]
  have hH3 : HarmonicAbel29.Harmonic N^3≤(J:ℝ)^3 := by gcongr
  have hJJ : 4*(J:ℝ)≤(J:ℝ)^3 := by
    have hh := mul_nonneg (show (0:ℝ)≤(J:ℝ)-2 by linarith only [hJR])
      (show (0:ℝ)≤(J:ℝ)^2+2*J by positivity)
    nlinarith only [hh]
  have h1J : (8:ℝ)≤(J:ℝ)^3 := by linarith only [hJR,hJJ]
  have hW := actual_exception_harmonic hcN
  have hb := actual_noninterval_family_count hF hroot hcL hLN hlow hP hcP hno
  have hlin := mul_le_mul_of_nonneg_left hHJ (show (0:ℝ)≤2*N by positivity)
  have hcube := mul_le_mul_of_nonneg_left hH3 (show (0:ℝ)≤6*N by positivity)
  have hlin3 := mul_le_mul_of_nonneg_left hJJ (Nat.cast_nonneg (α:=ℝ) N)
  have hone := mul_le_mul_of_nonneg_left h1J (Nat.cast_nonneg (α:=ℝ) N)
  have hs : (24:ℝ)*L≤N := by exact_mod_cast hscale
  have hsc := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α:=ℝ) N)
  have ht : (1024:ℝ)*(J:ℝ)^3≤N := by exact_mod_cast hJcube
  have htc := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (α:=ℝ) N)
  have hN6 : (6:ℝ)≤N := by exact_mod_cast hN
  have hconst : (48:ℝ)≤(N:ℝ)*(J:ℝ)^3 := by nlinarith only [hone,hN6]
  nlinarith only [hb,hW,hlin,hcube,hlin3,hone,hsc,htc,hconst,sq_nonneg (N:ℝ)]

theorem actual_avoiders_are_intervals {N J c L δ : ℕ} {G : Finset (Finset ℤ)}
    (hN : 6≤N) (hNJ : N<2^J) (hcN : (c:ℤ)∈Ground N)
    (hF : Legal (Ground N) G) (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hcL : c≤L) (hLN : L≤N)
    (hlow : ∀S∈Avoiders G (c:ℤ),∃a∈S,a≤(L:ℤ))
    (hscale : 24*L≤N) (hJcube : 1024*J^3≤N) (hdelta : 24*δ<N)
    (hfull : (N:ℝ)^2/2≤G.card+(δ:ℝ)*N) :
    ∀S∈Avoiders G (c:ℤ),IsInterval S := by
  intro S hS
  by_contra hn
  obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
  have hb := actual_noninterval_family_gap hN hNJ hcN hF hroot hcL hLN hlow hSG hcS hn hscale hJcube
  have hd : (24:ℝ)*δ<N := by exact_mod_cast hdelta
  have hpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hdn := mul_lt_mul_of_pos_right hd hpos
  nlinarith only [hb,hfull,hdn]

theorem actual_avoiders_intervals {N J c L R δ : ℕ} {G : Finset (Finset ℤ)}
    (hN : 6≤N) (hNJ : N<2^J) (hcN : (c:ℤ)∈Ground N)
    (hF : Legal (Ground N) G) (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hlow : ∀S∈Avoiders G (c:ℤ),∃a∈S,a≤(L:ℤ))
    (hright : ∀S∈Avoiders G (c:ℤ),∃b∈S,(R:ℤ)≤b)
    (hscale : 24*L≤N) (hJcube : 1024*J^3≤N) (hdelta : 24*δ<N)
    (hfull : (N:ℝ)^2/2≤G.card+(δ:ℝ)*N) :
    ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b) := by
  have hi := actual_avoiders_are_intervals hN hNJ hcN hF hroot hcL.le (hLR.trans hRN)
    hlow hscale hJcube hdelta hfull
  intro S hS
  obtain ⟨a,b,hrep⟩ := hi S hS
  obtain ⟨u,hu,huL⟩ := hlow S hS
  obtain ⟨v,hv,hRv⟩ := hright S hS
  obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
  have huI : a≤u ∧ u≤b := Finset.mem_Icc.mp (by rwa [←hrep])
  have hvI : a≤v ∧ v≤b := Finset.mem_Icc.mp (by rwa [←hrep])
  have hab : a≤b := huI.1.trans huI.2
  have haS : a∈S := by rw [hrep];exact Finset.mem_Icc.mpr ⟨le_rfl,hab⟩
  have hbS : b∈S := by rw [hrep];exact Finset.mem_Icc.mpr ⟨hab,le_rfl⟩
  have haN := (mem_ground N a).mp (hF.1 S hSG haS)
  have hbN := (mem_ground N b).mp (hF.1 S hSG hbS)
  have hca : (c:ℤ)<a := by
    by_contra hn
    apply hcS
    rw [hrep]
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have ha : (a.toNat:ℤ)=a := Int.toNat_of_nonneg (by omega)
  have hb : (b.toNat:ℤ)=b := Int.toNat_of_nonneg (by omega)
  refine ⟨a.toNat,b.toNat,by omega,by omega,by omega,by omega,?_⟩
  simpa only [Interval,ha,hb] using hrep

#print axioms actual_noninterval_family_gap
#print axioms actual_avoiders_are_intervals
#print axioms actual_avoiders_intervals
end
end JSP233.NonInterval24_139
