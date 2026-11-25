module

public import Erdos272.Resources.N82426.PointSource82426
public import Erdos272.Global.N82427.CommonBounds82427
public import Erdos272.Global.N82426.HighRoot82426
public import Erdos272.Resources.N82427.SmallCredit82427

@[expose] public section

namespace JSP233.PointCommon82426
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 HarmonicAbel29 IntrinsicTriples208
open WindowData82427 WindowGates82427 PointSource82426
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def PointMargin (w : ℕ) : ℝ :=
  (271/800-QuadraticExtra w)*(82426 : ℝ)^2-EffectiveG w*(82425 : ℝ)^3-
    ((RootK w : ℝ)+1/2+HCommon)*82426-
      (PointFee w+Penalty w-((RootCredit w : ℝ)+1))

theorem point_margin {w : ℕ} (hw : LiveWindow w) : 0<PointMargin w := by
  rcases hw with rfl | rfl | rfl <;>
    norm_num [PointMargin, PointFee, Fee, CoeffA, CoeffB, CoeffC,
      G, EffectiveG, QuadraticExtra, Penalty, RootK, RootCredit, HCommon]

theorem source_contradiction {w : ℕ} {F A : Finset (Finset ℤ)}
    (hw : LiveWindow w) (hF : Legal (Ground 82426) F) (hcard : B 82426≤F.card)
    (hsparse : ∀ S ∈ A, 12*S.card≤82426) (hAF : A⊆F)
    (hinner : (A.card : ℝ)≤6*G w*(∑ S ∈ A, ((Pool S).card : ℝ))+PointFee w)
    (hG : ((SparseCrooked 82426 12 F).card : ℝ)≤
      A.card+(RootK w : ℝ)*82426-(RootCredit w : ℝ)) : False := by
  have hw' : w<4 := by rcases hw with rfl | rfl | rfl <;> decide
  have hg := gates hw'
  have hpred : ((82426-1 : ℕ) : ℝ)=82425 := by norm_num
  have hj : ((F.filter IsAP).card : ℝ)+(A.card : ℝ)+(Deleted 82426 12 F).card≤
      (129/800+QuadraticExtra w : ℝ)*(82426 : ℝ)^2+EffectiveG w*(82425 : ℝ)^3+
        Penalty w+82426*Harmonic 82426+PointFee w := by
    by_cases hlow : w<3
    · have hcap : 3*G w*((82426-1 : ℕ) : ℝ)≤1 := by
        rcases hw with rfl | rfl | rfl <;> norm_num [G]
      have hb := DenseJoint88404.actual_AP_inner_with_deleted
        (by decide : 15000≤82426) (by decide : 82426≤2^18) hF hAF hsparse
        hg.g_positive hg.dense_payment hcap hinner
      simpa only [hpred, EffectiveG, Penalty, QuadraticExtra, if_pos hlow,
        SieveConstants88404.alpha_one, Nat.cast_ofNat, mul_comm] using hb
    · have hb := DenseJoint158375.actual_AP_inner_with_deleted
        (by decide : 15000≤82426) (by decide : 82426≤2^18) hF hAF hsparse
        hg.g_positive hg.dense_payment hinner
      simpa only [hpred, EffectiveG, Penalty, QuadraticExtra, if_neg hlow,
        Nat.cast_ofNat, mul_comm, add_zero] using hb
  have hp := CommonRoot84364.sparse_partition (N:=82426) (F:=F)
  have hb := CommonRoot84364.original_lower hcard
  have hh : Harmonic 82426≤HCommon := Harmonic82427.actual_cap (by decide) (by decide)
  have hgate := point_margin hw
  dsimp only [PointMargin] at hgate
  norm_num only [Nat.cast_ofNat] at hp hb
  nlinarith only [hj, hp, hb, hh, hG, hgate]

theorem small_contradiction {F : Finset (Finset ℤ)}
    (hF : Legal (Ground 82426) F) (hcard : B 82426≤F.card)
    (hG : ((SparseCrooked 82426 12 F).card : ℝ)≤7311*82426-632402) : False := by
  have ha := DenseJoint158375.actual_flat_AP_deleted (by decide : 15000≤82426)
    (by decide : 82426≤179999) hF
  have hp := CommonRoot84364.sparse_partition (N:=82426) (F:=F)
  have hb := CommonRoot84364.original_lower hcard
  have hh : Harmonic 82426≤HCommon := Harmonic82427.actual_cap (by decide) (by decide)
  norm_num only [Nat.cast_ofNat] at ha hp hb
  norm_num [HCommon] at hh
  nlinarith only [ha, hp, hb, hh, hG]

theorem high_contradiction {F : Finset (Finset ℤ)}
    (hF : Legal (Ground 82426) F) (hcard : B 82426≤F.card)
    (hG : ((SparseCrooked 82426 12 F).card : ℝ)≤(7/80 : ℝ)*(82426 : ℝ)^2) : False := by
  have ha := DenseJoint158375.actual_flat_AP_deleted (by decide : 15000≤82426)
    (by decide : 82426≤179999) hF
  have hp := CommonRoot84364.sparse_partition (N:=82426) (F:=F)
  have hb := CommonRoot84364.original_lower hcard
  have hh : Harmonic 82426≤HCommon := Harmonic82427.actual_cap (by decide) (by decide)
  norm_num only [Nat.cast_ofNat] at ha hp hb
  norm_num [HCommon] at hh
  nlinarith only [ha, hp, hb, hh, hG]

theorem actual_common_root {F : Finset (Finset ℤ)}
    (hF : Legal (Ground 82426) F) (hcard : B 82426≤F.card) :
    ∃ c∈Ground 82426, ∀ S∈Retained 82426 12 F, ¬IsAP S→c∈S := by
  let G := SparseCrooked 82426 12 F
  have hGF : G⊆F := actual_sparse_subset 82426 12 F
  have hlegal : Legal (Ground 82426) G := actual_sparse_legal hF
  have hbad : ∀ S∈G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  have hsparse : ∀ S∈G, 12*S.card≤82426 := fun S hS => (actual_sparse_membership.mp hS).2.2
  by_cases hsmall : Small G 86=∅
  · have hsize : ∀ S∈G, (info 0).memberFloor≤S.card := by
      intro S hS
      change 87≤S.card
      by_contra hn
      have hh : S∈Small G 86 := Finset.mem_filter.mpr ⟨hS, by omega⟩
      rw [hsmall] at hh
      exact Finset.notMem_empty _ hh
    have hb := actual_source (Or.inl rfl : LiveWindow 0) hlegal hbad hsize hsparse (le_refl G)
    apply False.elim (source_contradiction (Or.inl rfl) hF hcard hsparse hGF hb ?_)
    change (G.card : ℝ)≤G.card+(RootK 0 : ℝ)*82426-(RootCredit 0 : ℝ)
    norm_num only [RootK, RootCredit, Nat.cast_ofNat]
    linarith
  by_cases hkernel : Kernel (Ground 82426) (Small G 86)=∅
  · have hb := SmallCredit82427.actual_small_empty_kernel86 (by decide : 1893≤82426)
      hlegal hbad (Finset.nonempty_iff_ne_empty.mpr hsmall) hkernel
    exact False.elim (small_contradiction hF hcard hb)
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hkernel
  obtain ⟨hcN, hcsmall⟩ := Finset.mem_filter.mp hc
  by_cases hroot : ∀ S∈G, c∈S
  · exact ⟨c, hcN, fun S hS hbadS => hroot S (Finset.mem_filter.mpr ⟨hS,hbadS⟩)⟩
  have homit : ∃ S∈G, c∉S := by simpa only [not_forall,exists_prop] using hroot
  obtain ⟨T,hT,hmin⟩ := actual_minimum_omitter homit
  let A := Avoiders G c
  have hAG : A⊆G := Finset.filter_subset _ _
  have hA : Legal (Ground 82426) A :=
    ⟨fun S hS => hlegal.1 S (hAG hS),
      fun S hS U hU hSU => hlegal.2 S (hAG hS) U (hAG hU) hSU⟩
  have hAsize : ∀ S∈A, 87≤S.card := by
    intro S hS
    by_contra hn
    have hh : S∈Small G 86 := Finset.mem_filter.mpr ⟨hAG hS,by omega⟩
    exact (Finset.mem_filter.mp hS).2 (hcsmall S hh)
  have hp := root_avoider_card_partition G c
  have hpR : (G.card : ℝ)=(RootPart G c).card+A.card := by exact_mod_cast hp.symm
  have hpaid : ∀ w, LiveWindow w→T.card≤RootK w→
      (∀ S∈A, (info w).memberFloor≤S.card)→False := by
    intro w hw hcut hsize
    have hK : RootK w+2≤82426 := by
      rcases hw with rfl | rfl | rfl <;> norm_num [RootK]
    have hr := CommonBounds82427.degree_payment (by decide : 2≤82426) hK
      hlegal hbad hT hcut
    have hcredit : (RootCredit w : ℝ)=(RootK w : ℝ)*((RootK w : ℝ)+3)/2 := by
      rcases hw with rfl | rfl | rfl <;> norm_num [RootK,RootCredit]
    have hpay : (G.card : ℝ)≤A.card+(RootK w : ℝ)*82426-(RootCredit w : ℝ) := by
      rw [hcredit]
      norm_num only [Nat.cast_ofNat] at hr
      linarith only [hpR,hr]
    exact source_contradiction hw hF hcard (fun S hS => hsparse S (hAG hS))
      (hAG.trans hGF) (actual_source hw hA (fun S hS => hbad S (hAG hS)) hsize
        (fun S hS => hsparse S (hAG hS)) (le_refl A)) hpay
  by_cases h87 : T.card≤87
  · exact False.elim (hpaid 0 (Or.inl rfl) h87 hAsize)
  by_cases h129 : T.card≤129
  · apply False.elim (hpaid 2 (Or.inr (Or.inl rfl)) h129 ?_)
    intro S hS
    change 88≤S.card
    have hm := hmin S hS
    omega
  by_cases h554 : T.card≤554
  · apply False.elim (hpaid 3 (Or.inr (Or.inr rfl)) h554 ?_)
    intro S hS
    change 130≤S.card
    have hm := hmin S hS
    omega
  have hb := HighRoot82426.actual_high_root (by decide : 82426≤82426) (by decide)
    hlegal hbad hsparse hT (by omega) hmin
  exact False.elim (high_contradiction hF hcard hb)

#print axioms point_margin
#print axioms source_contradiction
#print axioms small_contradiction
#print axioms high_contradiction
#print axioms actual_common_root
end
end JSP233.PointCommon82426
