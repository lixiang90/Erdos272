module

public import Erdos272.Global.N67702.EXGlobal67702

@[expose] public section

namespace JSP233.EXCap67702
open StarCompletion APGeometry APCount41 HarmonicAbel29 EXOneHole67702
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem width_nat {N L R : ℕ} (hRN : R≤N) (k : Fin 2)
    (hw : (L : ℝ)+((N : ℝ)-R)≤WidthCap k*N) :
    Denominator k*(L+N-R)≤Numerator k*N := by
  have hd := (parameter_bounds k).1
  have hdr : (0 : ℝ)<Denominator k := by exact_mod_cast hd
  have he : ((L+N-R : ℕ) : ℝ)=(L : ℝ)+((N : ℝ)-R) := by
    rw [Nat.cast_sub (by omega : R≤L+N)]
    push_cast
    ring
  have hh := mul_le_mul_of_nonneg_left hw hdr.le
  dsimp only [WidthCap] at hh
  have hx : (Denominator k : ℝ)*((Numerator k : ℝ)/Denominator k*(N : ℝ))=
      (Numerator k : ℝ)*N := by field_simp
  rw [hx,←he] at hh
  exact_mod_cast hh

theorem actual_cap_width {N L R : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2000≤N) (hLR : L≤R) (hRN : R≤N) (k : Fin 2)
    (hw : (L : ℝ)+((N : ℝ)-R)≤WidthCap k*N)
    (hF : Legal (Ground N) F) (hAP : ∀ S∈F,IsAP S)
    (hfour : ∀ S∈F,4≤S.card) (hlarge : ∀ S∈F,2≤Step S)
    (hends : ∀ S∈F,Low S≤(L : ℤ) ∧ (R : ℤ)≤High S) :
    (F.card : ℝ)≤(129/200 : ℝ)*L*((N : ℝ)-R)+
      ((L : ℝ)+((N : ℝ)-R))*(Harmonic N-EXLog67702.Beta k)+(29/100 : ℝ)*N+1 := by
  let M := Truncate N k
  let D := (N-1)/3
  let w : ℝ := (L : ℝ)+((N : ℝ)-R)
  have ht := truncate_bounds hN k
  have hp := parameter_bounds k
  have hwn := width_nat hRN k hw
  have hLM : L+N-R≤M := by
    apply (Nat.le_div_iff_mul_le hp.1).mpr
    nlinarith only [hwn]
  have hJ : Hole N k⊆Finset.Icc (M+1) D := by
    intro d hd
    have hb := hole_bounds hN k hd
    exact Finset.mem_Icc.mpr ⟨by dsimp only [M];omega,hb.2.2.1⟩
  have hempty : ∀ d∈Hole N k,F.filter (fun S=>Step S=d)=∅ := by
    intro d hd
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨hSF,hSd⟩ := Finset.mem_filter.mp hS
    have hb := hole_bounds hN k hd
    have hg := hole_below_span hN hLR hRN k hwn hd
    exact EXGeometry67702.actual_empty_three_gap (hF.1 S hSF) (hAP S hSF) hSd
      (hends S hSF) hb.2.2.2.1 (by omega)
  have hcap : ∀ d∈Finset.Icc 2 D,M<d → (F.filter (fun S=>Step S=d)).card≤1 := by
    intro d hd hMd
    let A := F.filter (fun S=>Step S=d)
    have hAF : A⊆F := Finset.filter_subset _ _
    have hlegal : Legal (Ground N) A :=
      ⟨fun S hS=>hF.1 S (hAF hS),fun S hS T hT hne=>hF.2 S (hAF hS) T (hAF hT) hne⟩
    have hh := APExterior50.actual_same_step_endpoint_rectangle hlegal
      (fun S hS=>isAP_nonempty (hAP S (hAF hS))) (by
        intro S hS
        obtain ⟨hSF,hSd⟩ := Finset.mem_filter.mp hS
        obtain ⟨_,p,hpS⟩ := actual_step (hAP S hSF)
        exact ⟨p,by simpa only [hSd] using hpS⟩)
      (fun S hS=>hends S (hAF hS))
    have hLd : L<d := by omega
    have hKd : N-R<d := by omega
    simpa only [Nat.div_eq_of_lt hLd,Nat.div_eq_of_lt hKd,zero_add,mul_one] using hh
  have h := EXTruncated67702.actual_truncated_count hRN ht.1 ht.2 hF hAP hfour hlarge hends
    hJ hempty hcap
  have hRNr : (R : ℝ)≤N := by exact_mod_cast hRN
  have hw0 : 0≤w := by dsimp only [w];positivity
  have heta : 0<WidthCap k := by
    exact div_pos (by exact_mod_cast hp.2.1) (by exact_mod_cast hp.1)
  have heta1 : WidthCap k≤1 := by
    apply (div_le_one₀ (by exact_mod_cast hp.1)).mpr
    exact_mod_cast hp.2.2.le
  have hDN : D≤N := by dsimp only [D];omega
  have hMN : M≤N := ht.2.trans hDN
  have hMr : (M : ℝ)≤WidthCap k*N := by
    have hh := Nat.cast_div_le (α:=ℝ) (m:=Numerator k*N) (n:=Denominator k)
    push_cast at hh
    dsimp only [M,Truncate,WidthCap]
    simpa only [div_mul_eq_mul_div] using hh
  have hbound : (M : ℝ)+1≤WidthCap k*((N : ℝ)+1)+(1-WidthCap k) := by
    linarith only [hMr]
  have herr : w*(1-WidthCap k)/(WidthCap k*((N : ℝ)+1))≤1-WidthCap k := by
    apply (div_le_iff₀ (show 0<WidthCap k*((N : ℝ)+1) by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr heta1)
    dsimp only [w] at hh ⊢
    nlinarith only [hh,mul_nonneg heta.le (sub_nonneg.mpr heta1)]
  have hh := EXHarmonic67702.weighted_harmonic_tail hMN heta hw0 hbound herr
  have hl := mul_le_mul_of_nonneg_left (EXLog67702.width_log_lower k) hw0
  have hDr : (3 : ℝ)*D≤(N : ℝ)-1 := by
    have hd : 3*D≤N-1 := by dsimp only [D];omega
    have hr : (3 : ℝ)*D≤((N-1 : ℕ) : ℝ) := by exact_mod_cast hd
    rw [Nat.cast_sub (by omega : 1≤N),Nat.cast_one] at hr
    exact hr
  have hhole := hole_count_integer hN k
  have hholeR : ((4*Gamma k-3*Denominator k : ℕ) : ℝ)*N≤
      12*(Denominator k : ℝ)*(Hole N k).card+9*(Denominator k : ℝ) := by exact_mod_cast hhole
  change (F.card : ℝ)≤(129/200 : ℝ)*L*((N : ℝ)-R)+w*(Harmonic M-1)+(D : ℝ)-1-(Hole N k).card at h
  change _≤(129/200 : ℝ)*L*((N : ℝ)-R)+w*(Harmonic N-EXLog67702.Beta k)+(29/100 : ℝ)*N+1
  fin_cases k <;>
    norm_num [WidthCap,Numerator,Denominator,Gamma,EXLog67702.Beta] at h hh hl hholeR ⊢ <;>
    nlinarith only [h,hh,hl,hDr,hholeR,Nat.cast_nonneg (α:=ℝ) N]

#print axioms width_nat
#print axioms actual_cap_width
end
end JSP233.EXCap67702
