module

public import Erdos272.Counting.N20258.LengthTailBound20258
public import Erdos272.Capacity.N20258.ProgressionJoint20258

@[expose] public section
namespace JSP233.LongShadow20258
open StarCompletion IntrinsicTriples208 APClasses88404 SieveConstants88404
open ProgressionLengths20258 ProgressionPartition20258 ProgressionJoint20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

private theorem off_grid {n : ℕ} (lo : 1200 ≤ n) (hi : n < 2^15) :
    (offTail n 41 Steps : ℝ)+(1/4+squares)*(n : ℝ)^2 ≤
      (329/800 : ℝ)*(n : ℝ)^2-(89/10 : ℝ)*n+6887 := by
  have range (d : ℕ) (hd : d ∈ Steps) : 1 ≤ d ∧ d ≤ 13 := by
    rcases Finset.mem_insert.mp hd with rfl | hp
    · decide
    · have := selected_range hp
      omega
  have inside : Steps ⊆ Finset.Icc 1 n := by
    intro d hd
    obtain ⟨low,top⟩ := range d hd
    exact Finset.mem_Icc.mpr ⟨low,by omega⟩
  have each (d : ℕ) (hd : d ∈ Steps) :
      (n : ℝ)^2/(4*(d : ℝ)^2) ≤ (tail (n/d) 41 : ℝ)+861 := by
    obtain ⟨dp,du⟩ := range d hd
    have fits : 82 ≤ n/d := (Nat.le_div_iff_mul_le dp).mpr (by omega)
    exact LengthTailBound20258.grid_lower dp (by omega : 41 ≤ (n/d+2)/2)
  have saved := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib] at saved
  have count : (∑ _d ∈ Steps, (861 : ℝ))=6027 := by norm_num [Steps,Selected]
  have coeff : (∑ d ∈ Steps, (n : ℝ)^2/(4*(d : ℝ)^2))=(1/4+squares)*(n : ℝ)^2 := by
    norm_num [Steps,Selected,squares]
    ring
  rw [count,coeff] at saved
  have part : offTail n 41 Steps+(∑ d ∈ Steps, tail (n/d) 41)=offTail n 41 ∅ := by
    simpa only [offTail,Finset.sdiff_empty] using Finset.sum_sdiff (f := fun d => tail (n/d) 41) inside
  have pr : (offTail n 41 Steps : ℝ)+(∑ d ∈ Steps, (tail (n/d) 41 : ℝ))=offTail n 41 ∅ := by
    exact_mod_cast part
  linarith only [saved,pr,LengthTailBound20258.forty_one hi]

private theorem at_scale (n : ℝ) (hn : 1 ≤ n) :
    response n (1/(5*n)) ≤ (squares+250001/1000000)*n^2+(29/10)*n+5 := by
  have hp : 0 < n := by linarith
  let a : ℝ := Alpha 1
  have av : a=32767248/39364325 := alpha_one
  have rv : reciprocal=40361/30030 := by norm_num [reciprocal,Selected]
  have ea : 0 < a := by rw [av]; norm_num
  have form : response n (1/(5*n)) =
      (squares+a/5+25/(432*a^2))*n^2+
      (1+reciprocal+(6/5)*(606450017/1803601800))*n+
      1+((6*(13565611/18036018)+reciprocal)/5)+(6*(2403389/5010005))/(5*n) := by
    unfold response error
    change _ = (squares+Alpha 1/5+25/(432*(Alpha 1)^2))*_+_+_+_+_
    field_simp [hp.ne',show Alpha 1 ≠ 0 from ea.ne']
    ring
  have quadratic : a/5+25/(432*a^2) ≤ 250001/1000000 := by rw [av]; norm_num
  have linear : 1+reciprocal+(6/5 : ℝ)*(606450017/1803601800) ≤ 29/10 := by rw [rv]; norm_num
  have bounded : (6*(2403389/5010005) : ℝ)/(5*n) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith only [hn]
  have term : 1+((6*(13565611/18036018)+reciprocal)/5)+1 ≤ (5 : ℝ) := by rw [rv]; norm_num
  nlinarith only [form,bounded,term,mul_le_mul_of_nonneg_right quadratic (sq_nonneg n),
    mul_le_mul_of_nonneg_right linear hp.le]

/-- One joint count for all grounds in the window. Each of the seven
classes is deducted from the long-length tail before its shadow is priced. -/
theorem actual {N : ℕ} {F : Finset (Finset ℤ)} (lo : 1201 ≤ N) (hi : N ≤ 2^15)
    (legal : Legal (Ground N) F) (long : ∀ S ∈ F, IsAP S → 42 ≤ S.card) :
    ((F.filter IsAP).card : ℝ)+6*(1/(5*((N : ℝ)-1)))*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
      (411251/1000000 : ℝ)*((N : ℝ)-1)^2-6*((N : ℝ)-1)+7000 := by
  let n : ℝ := (N : ℝ)-1
  have hn : 1 ≤ n := by
    have lower : (1201 : ℝ) ≤ N := by exact_mod_cast lo
    dsimp only [n]
    linarith only [lower]
  have hp : 0 < n := by linarith
  have scale : 3*(1/(5*n))*n ≤ 1 := by
    have eq : 3*(1/(5*n))*n = 3/5 := by field_simp
    rw [eq]; norm_num
  have paid := ProgressionJoint20258.actual_joint (by omega : 14 ≤ N)
    (by positivity : 0 < 1/(5*n)) scale legal (k := 41)
    (fun d _ S hs => long S (APClasses88404.subset F d hs) (is_ap hs))
  have tail := off_grid (show 1200 ≤ N-1 by omega) (show N-1 < 2^15 by omega)
  rw [Nat.cast_sub (by omega : 1 ≤ N),Nat.cast_one] at tail
  change _+(1/4+squares)*n^2 ≤ (329/800 : ℝ)*n^2-(89/10 : ℝ)*n+6887 at tail
  change _ ≤ _+response n (1/(5*n)) at paid
  change _ ≤ (411251/1000000 : ℝ)*n^2-6*n+7000
  nlinarith only [paid,tail,at_scale n hn]

#print axioms actual
end
end JSP233.LongShadow20258
