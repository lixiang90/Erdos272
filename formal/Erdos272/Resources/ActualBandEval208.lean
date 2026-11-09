module

public import Erdos272.Resources.BandWindowRatio208
public import Erdos272.Resources.CrossBandNormalize208
public import Erdos272.Resources.CleanupChecked208
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.ActualBandEval208
open StarCompletion APGeometry NearAP36 SourceBridge208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208 CrossBandMenu208 CrossBandNormalize208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 200000

theorem actual_piece_empty {s : System} (v : Valid s) {d : ℕ}
    (hd : d∈Finset.Icc 1 s.D) (b : Band) (hE : s.E d b≤1) : s.Piece d b=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hSF := s.piece_subset d b hS
  have he := v.small d hd b S hS
  have hM := v.M_le d hd b
  have hlow := v.low d hd b S hS
  have heM := v.eM
  have he2 := v.e_two
  have hp := CoreCoordinates208.defect_positive (by omega : 2≤S.card) (v.legal.1 S hSF) (v.crooked S hSF)
  omega

/-- Actual same-heavy counts and physical windows satisfy precisely the two
integer components evaluated by the finite cleanup machine. -/
theorem actual_band_value {s : System} (v : Valid s) {d : ℕ}
    (hd : d∈Finset.Icc 1 s.D) (b : Band) (r : CleanupEval208.Row) (q : CleanupEval208.Band)
    (hT : q.T=s.T d b) (hE : q.E=s.E d b) (hU : q.U=s.U d b)
    (hB : CleanupEval208.block q d=s.B d b)
    (hgood : CleanupEval208.BandGood r d q (CleanupEval208.bandValue r d q))
    (hgrid : 0<r.grid) (hlow : 0<r.low) (hlN : r.low≤s.N) (hNh : s.N≤r.high) :
    (s.Heavy d b).card≤(CleanupEval208.bandValue r d q).count ∧
      (RawWindows s d b : ℝ)/s.N≤((CleanupEval208.bandValue r d q).windows : ℝ)/r.grid := by
  by_cases hE1 : s.E d b≤1
  · have hp := actual_piece_empty v hd b hE1
    have hh : s.Heavy d b=∅ := by
      simp only [System.Heavy,BandSystem208.Heavy,hp,Finset.image_empty,Finset.filter_empty]
    have hq : q.E≤1 := by simpa only [hE] using hE1
    simp only [hh,Finset.card_empty,Nat.zero_le,RawWindows,Finset.biUnion_empty,
      Nat.cast_zero,zero_div,CleanupEval208.bandValue,if_pos hq,CleanupEval208.bandZero,le_refl,and_self]
  · have he1 : 1≤s.E d b := by omega
    have hq : ¬q.E≤1 := by simpa only [hE] using hE1
    have heM := v.eM
    have he2 := v.e_two
    have hM := v.M_le d hd b
    have hET := v.ET d hd b
    have hTU := v.TU d hd b
    have hB2 := v.B_two d hd b
    have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;omega
    have hp := BandSystem208.actual_properties (s.piece_legal v.legal d b) hd0
      (by omega : 2≤s.T d b) hET.le he1 hTU hB2 (v.BA d hd b) s.start
      (fun S hS=>v.crooked S (s.piece_subset d b hS))
      (v.low d hd b) (v.high d hd b) (v.small d hd b) (fun S hS=>v.piece_sub hS) (v.gate d hd b)
    have hTV : s.T d b<SizeV s d b := by
      have hh:=hgood.2.2.2.2.2.2.1
      simpa only [hT,hU,hB,SizeV] using hh
    have hV0 : 0<SizeV s d b := by dsimp only [SizeV];omega
    have hEV : s.E d b<SizeV s d b := by omega
    have hAJ : s.T d b-s.E d b≤SizeV s d b-s.E d b-1 := by omega
    have hc := CleanupWindowBounds208.actual_window_bounds hp hd0 (by omega : 0<s.B d b) hV0 hEV hAJ
      (Nat.div_le_div_right (c := d) hlN) (Nat.div_le_div_right (c := d) hNh)
    have hz := BandWindowRatio208.actual_window_ratio hp hd0 (by omega : 0<s.B d b) hV0 hEV hAJ
      hgrid hlow hlN hNh
    simp only [CleanupEval208.bandValue,if_neg hq]
    refine ⟨?_,?_⟩
    · simpa only [hT,hE,hU,hB,SizeV,System.Heavy] using hc.1
    · simpa only [hT,hE,hU,hB,RawWindows,SizeV,System.Heavy,
        BandWindowRatio208.OrdinaryGrid,BandWindowRatio208.RightGrid] using hz

theorem closed_mono {N high d T E B V : ℕ} (hNh : N≤high) (hd : 0<d)
    (hB : 0<B) (hET : E≤T) (hTV : T≤V) :
    LightPrice208.Closed N d T E B V≤LightPrice208.Closed high d T E B V := by
  rw [←LightPrice208.price_closed hd hB hET hTV,←LightPrice208.price_closed hd hB hET hTV]
  unfold LightPhases208.Price LightPhases208.Cap
  calc
    _≤∑ r∈Finset.range (N+1),min d (high-(T-E+r*B)*d)*min V (high/d-r*B+E) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Nat.mul_le_mul
      · exact min_le_min_left d (Nat.sub_le_sub_right hNh _)
      · exact min_le_min_left V (Nat.add_le_add_right
          (Nat.sub_le_sub_right (Nat.div_le_div_right (c := d) hNh) _) E)
    _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hNh))
      (by intros;exact Nat.zero_le _)

/-- Empty defect-one pieces have zero light cost, exactly as in the machine;
the other pieces pay the monotone physical light price at the common high endpoint. -/
theorem actual_piece_eval_credit {s : System} (v : Valid s) {d : ℕ}
    (hd : d∈Finset.Icc 1 s.D) (b : Band) (r : CleanupEval208.Row) (q : CleanupEval208.Band)
    (hT : q.T=s.T d b) (hE : q.E=s.E d b) (hU : q.U=s.U d b)
    (hB : CleanupEval208.block q d=s.B d b)
    (hgood : CleanupEval208.BandGood r d q (CleanupEval208.bandValue r d q))
    (hNh : s.N≤r.high) :
    ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(s.Heavy d b).card≤
      (CleanupEval208.bandValue r d q).light+(s.HeavyPiece d b).card := by
  by_cases hE1 : s.E d b≤1
  · have hp := actual_piece_empty v hd b hE1
    have hh : s.Heavy d b=∅ := by
      simp only [System.Heavy,BandSystem208.Heavy,hp,Finset.image_empty,Finset.filter_empty]
    have hhp : s.HeavyPiece d b=∅ := by simp only [System.HeavyPiece,hp,Finset.filter_empty]
    have hq : q.E≤1 := by simpa only [hE] using hE1
    simp only [hp,hh,hhp,Finset.card_empty,Nat.cast_zero,mul_zero,zero_add,
      CleanupEval208.bandValue,if_pos hq,CleanupEval208.bandZero,le_refl]
  · have hc := v.piece_credit hd b
    have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;omega
    have hB2 := v.B_two d hd b
    have hET := v.ET d hd b
    have hTV : s.T d b≤s.U d b+s.B d b-3 := by
      have hh:=hgood.2.2.2.2.2.2.1
      have ht : s.T d b<s.U d b+s.B d b-3 := by simpa only [hT,hU,hB] using hh
      exact ht.le
    have hm := closed_mono hNh hd0 (by omega : 0<s.B d b) hET.le hTV
    have hmR : s.Light d b≤(LightPrice208.Closed r.high d (s.T d b) (s.E d b) (s.B d b)
        (s.U d b+s.B d b-3) : ℝ) := by
      change (LightPrice208.Closed s.N d (s.T d b) (s.E d b) (s.B d b)
        (s.U d b+s.B d b-3) : ℝ)≤_
      exact_mod_cast hm
    have hq : ¬q.E≤1 := by simpa only [hE] using hE1
    simp only [CleanupEval208.bandValue,if_neg hq]
    simp only [hT,hE,hU,hB]
    linarith only [hc,hmR]

#print axioms actual_piece_empty
#print axioms actual_band_value
#print axioms closed_mono
#print axioms actual_piece_eval_credit
end
end JSP233.ActualBandEval208
