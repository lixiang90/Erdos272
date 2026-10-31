import Erdos272.Resources.CrossBandCredit208

namespace JSP233.CrossBandCleanup208
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208
open CrossBandCredit208 CrossBandCredit208.System
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Physical band hypotheses.  The core is one chosen maximum actual AP for
each member, shared by every light, heavy, and residual calculation. -/
structure Valid (s : System) : Prop where
  legal : Legal (Ground s.N) s.F
  step_range : ∀S∈s.F,s.step S∈Finset.Icc 1 s.D
  sub : ∀S∈s.F,s.Core S⊆S
  crooked : ∀S∈s.F,¬IsAP S
  e_two : 2≤s.e
  eM : s.e<s.M
  M_le : ∀d∈Finset.Icc 1 s.D,∀b : Band,s.M≤s.T d b
  E_le : ∀d∈Finset.Icc 1 s.D,∀b : Band,s.E d b≤s.e
  ET : ∀d∈Finset.Icc 1 s.D,∀b : Band,s.E d b<s.T d b
  TU : ∀d∈Finset.Icc 1 s.D,∀b : Band,s.T d b<s.U d b
  B_two : ∀d∈Finset.Icc 1 s.D,∀b : Band,2≤s.B d b
  BA : ∀d∈Finset.Icc 1 s.D,∀b : Band,s.B d b≤s.T d b-s.E d b
  gate : ∀d∈Finset.Icc 1 s.D,∀b : Band,
    (StepClass208.PrimeGate d-1)*(s.T d b-s.E d b+1-s.B d b)≥s.E d b ∨
      StepClass208.PrimeGate d*s.B d b≤(StepClass208.PrimeGate d-1)*(s.T d b-s.E d b+1)
  low : ∀d∈Finset.Icc 1 s.D,∀b : Band,∀S∈s.Piece d b,s.T d b≤S.card
  high : ∀d∈Finset.Icc 1 s.D,∀b : Band,∀S∈s.Piece d b,S.card<s.U d b
  small : ∀d∈Finset.Icc 1 s.D,∀b : Band,∀S∈s.Piece d b,Defect S<s.E d b

namespace Valid
theorem self_piece {s : System} (v : Valid s) {S : Finset ℤ} (hS : S∈s.F) :
    S∈s.Piece (s.step S) (s.band S) := Finset.mem_filter.mpr ⟨hS,rfl,rfl⟩

theorem size {s : System} (v : Valid s) {S : Finset ℤ} (hS : S∈s.F) : s.M≤S.card :=
  (v.M_le (s.step S) (v.step_range S hS) (s.band S)).trans
    (v.low _ (v.step_range S hS) _ S (v.self_piece hS))

theorem core_card {s : System} (v : Valid s) {S : Finset ℤ} (hS : S∈s.F) :
    (s.Core S).card=MaxAPSize S :=
  grid_card _ _ _ ((Finset.mem_Icc.mp (v.step_range S hS)).1)

theorem remainder {s : System} (v : Valid s) {S : Finset ℤ} (hS : S∈s.F) :
    (S\s.Core S).card=Defect S := by
  have hh := Finset.card_sdiff_add_card_eq_card (v.sub S hS)
  rw [v.core_card hS] at hh
  unfold Defect
  omega

theorem piece_sub {s : System} (v : Valid s) {d : ℕ} {b : Band} {S : Finset ℤ}
    (hS : S∈s.Piece d b) : Grid (s.start S) d (MaxAPSize S)⊆S := by
  have hh := v.sub S (s.piece_subset d b hS)
  simpa only [System.Core,(Finset.mem_filter.mp hS).2.1] using hh

theorem piece_credit {s : System} (v : Valid s) {d : ℕ} (hd : d∈Finset.Icc 1 s.D) (b : Band) :
    ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(s.Heavy d b).card≤
      s.Light d b+(s.HeavyPiece d b).card := by
  have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;omega
  have hB := v.B_two d hd b
  have hM := v.M_le d hd b
  have hTM := v.TU d hd b
  have heM := v.eM
  have he2 := v.e_two
  have hh := BandCredit208.actual_closed_credit s.start MaxAPSize Defect hd0 (by omega : 0<s.B d b)
    (v.low d hd b) (v.ET d hd b) (by omega : s.T d b≤s.U d b+s.B d b-3)
    (v.small d hd b) (by
      intro S hS
      have hm := maxAPSize_le_card S
      unfold Defect
      omega) (fun S hS=>v.piece_sub hS)
    (fun S hS=>v.legal.1 S (s.piece_subset d b hS)) (by
      intro S hS
      have hh := v.high d hd b S hS
      omega)
  dsimp only [System.Heavy,System.HeavyPiece,System.Light]
  exact_mod_cast hh

theorem core_in_windows {s : System} (v : Valid s) {S : Finset ℤ} (hS : S∈s.G) :
    s.Core S⊆s.Windows (s.step S) := by
  have hSF := s.g_subset hS
  have hd := v.step_range S hSF
  let d := s.step S
  let b := s.band S
  have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;dsimp [d];omega
  have heM := v.eM
  have he2 := v.e_two
  have hM := v.M_le d hd b
  have hET := v.ET d hd b
  have hw := BandGeometry208.actual_band_windows (s.piece_legal v.legal d b) hd0
    (by omega : 2≤s.T d b) hET.le (v.B_two d hd b) s.start
    (fun R hR=>v.crooked R (s.piece_subset d b hR))
    (v.low d hd b) (v.high d hd b) (v.small d hd b) (fun R hR=>v.piece_sub hR)
    S (v.self_piece hSF)
  have hH := (Finset.mem_filter.mp hS).2
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,Finset.mem_biUnion.mpr
    ⟨Code d (s.B d b) (s.start S),hH,hw.1 hx⟩⟩

theorem equal_label_disjoint {s : System} (v : Valid s) {S T : Finset ℤ}
    (hS : S∈s.G) (hT : T∈s.G) (hST : S≠T) (hstep : s.step S=s.step T)
    (hlabel : s.Label S=s.Label T) : Disjoint (S\s.Core S) (T\s.Core T) := by
  have hSF := s.g_subset hS
  have hTF := s.g_subset hT
  have hd := v.step_range S hSF
  let d := s.step S
  let b := s.band S
  have hb : s.band S=s.band T := congrArg Prod.fst hlabel
  have hc := congrArg Prod.snd hlabel
  have hcode : Code d (s.B d b) (s.start S)=Code d (s.B d b) (s.start T) := by
    simpa only [System.Label,←hstep,←hb] using hc
  have hSP : S∈s.Piece d b := v.self_piece hSF
  have hTP : T∈s.Piece d b := Finset.mem_filter.mpr ⟨hTF,hstep.symm,hb.symm⟩
  have heM := v.eM
  have he2 := v.e_two
  have hM := v.M_le d hd b
  have hET := v.ET d hd b
  have hB := v.B_two d hd b
  have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;dsimp [d];omega
  have hh := BandGeometry208.actual_band_disjoint (s.piece_legal v.legal d b) hd0
    (by omega : 2≤s.T d b) hET.le (by omega : 0<s.B d b) (v.BA d hd b) s.start
    (fun R hR=>v.crooked R (s.piece_subset d b hR)) (v.low d hd b) (v.high d hd b)
    (v.small d hd b) (fun R hR=>v.piece_sub hR) (v.gate d hd b) S hSP T hTP hST hcode
  simpa only [System.Core,←hstep] using hh
end Valid

/-- The global residual term is paid once for the union of the actual heavy
pieces.  The labels are `(band, Code)`, so equal labels remain in one band. -/
theorem actual_heavy_cleanup (s : System) (v : Valid s) (Z : ℕ→Band→ℕ)
    (hZ : ∀d∈Finset.Icc 1 s.D,∀b : Band,((s.Heavy d b).biUnion
      (ClippedWindows208.Window s.N d (s.B d b) (s.U d b+s.B d b-3))).card≤Z d b) :
    (s.G.card : ℝ)≤(s.N : ℝ)^2*ResidualAggregate208.Price s.e (ResidualTwoCensus208.H s.M)+
      (253/35 : ℝ)*s.N+
      ((∑d∈Finset.Icc 1 s.D,(∑b : Band,(s.Heavy d b).card)*
        (min s.N (∑b : Band,Z d b)+(s.e-1)) : ℕ) : ℝ) := by
  have hG : Legal (Ground s.N) s.G :=
    ⟨fun S hS=>v.legal.1 S (s.g_subset hS),
      fun S hS T hT hST=>v.legal.2 S (s.g_subset hS) T (s.g_subset hT) hST⟩
  have hstep : ∀S∈s.G,s.step S∈Finset.Icc 1 s.D := fun S hS=>v.step_range S (s.g_subset hS)
  have heM := v.eM
  have he2 := v.e_two
  have hAP : ∀S∈s.G,∃a : ℤ,APAt (s.step S : ℤ) a (s.Core S) := by
    intro S hS
    exact ⟨s.start S,grid_APAt _ _ _ (by have := (Finset.mem_Icc.mp (hstep S hS)).1;omega)⟩
  have hne : ∀S∈s.G,(s.Core S).Nonempty := by
    intro S hS
    apply Finset.card_pos.mp
    rw [v.core_card (s.g_subset hS)]
    have hs := v.size (s.g_subset hS)
    have hm := two_le_maxAPSize (show 2≤S.card by omega)
    omega
  have hmax : ∀S∈s.G,∀R : Finset ℤ,IsAP R→R⊆S→R.card≤(s.Core S).card := by
    intro S hS R hR hRS
    rw [v.core_card (s.g_subset hS)]
    exact AP_card_le_max hR hRS
  have hsmall : ∀S∈s.G,(S\s.Core S).card<s.e := by
    intro S hS
    have hSF := s.g_subset hS
    rw [v.remainder hSF]
    exact (v.small _ (v.step_range S hSF) _ S (v.self_piece hSF)).trans_le
      (v.E_le _ (v.step_range S hSF) _)
  have hp := NearResidual208.actual_near_payment hG v.e_two v.eM s.Core s.step hstep
    (fun S hS=>v.sub S (s.g_subset hS)) hAP hne hmax
    (fun S hS=>v.size (s.g_subset hS)) (fun S hS=>v.crooked S (s.g_subset hS)) hsmall
    s.Windows (fun S hS=>v.core_in_windows hS) s.Label s.Labels
    (fun S hS=>s.label_mem hS) (fun S hS T hT hST hstep hlabel=>v.equal_label_disjoint hS hT hST hstep hlabel)
  have hb : (∑d∈Finset.Icc 1 s.D,(s.Labels d).card*((s.Windows d).card+(s.e-1)))≤
      ∑d∈Finset.Icc 1 s.D,(∑b : Band,(s.Heavy d b).card)*(min s.N (∑b : Band,Z d b)+(s.e-1)) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [s.labels_card]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (s.windows_card d (Z d) (hZ d hd)) (s.e-1))
  have hbR : ((∑d∈Finset.Icc 1 s.D,(s.Labels d).card*((s.Windows d).card+(s.e-1)) : ℕ) : ℝ)≤
      ((∑d∈Finset.Icc 1 s.D,(∑b : Band,(s.Heavy d b).card)*(min s.N (∑b : Band,Z d b)+(s.e-1)) : ℕ) : ℝ) := by exact_mod_cast hb
  linarith only [hp,hbR]

theorem actual_near_payment_with_credit (s : System) (v : Valid s) (Z : ℕ→Band→ℕ)
    (hZ : ∀d∈Finset.Icc 1 s.D,∀b : Band,((s.Heavy d b).biUnion
      (ClippedWindows208.Window s.N d (s.B d b) (s.U d b+s.B d b-3))).card≤Z d b) :
    (s.F.card : ℝ)+(∑d∈Finset.Icc 1 s.D,∑b : Band,(s.T d b : ℝ)*(s.Heavy d b).card)≤
      (∑d∈Finset.Icc 1 s.D,∑b : Band,s.Light d b)+
      (s.N : ℝ)^2*ResidualAggregate208.Price s.e (ResidualTwoCensus208.H s.M)+
      (253/35 : ℝ)*s.N+
      ((∑d∈Finset.Icc 1 s.D,(∑b : Band,(s.Heavy d b).card)*
        (min s.N (∑b : Band,Z d b)+(s.e-1)) : ℕ) : ℝ) := by
  have hc := s.actual_credit_sum v.step_range (fun d hd b=>v.piece_credit hd b)
  have hp := actual_heavy_cleanup s v Z hZ
  linarith only [hc,hp]

#print axioms Valid.piece_credit
#print axioms Valid.core_in_windows
#print axioms Valid.equal_label_disjoint
#print axioms actual_heavy_cleanup
#print axioms actual_near_payment_with_credit
end
end JSP233.CrossBandCleanup208
