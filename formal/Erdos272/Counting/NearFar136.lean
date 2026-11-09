module

public import Erdos272.Counting.FiniteNear136
public import Erdos272.Counting.NearFar134
public import Erdos272.Resources.FarWeighted136

@[expose] public section
namespace JSP233.NearFar136
open StarCompletion APGeometry NearAP36 NearWhole112
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Nu (K:ℕ) : ℝ := FiniteNear136.NuNumerator/K
def G (N K:ℕ) : ℝ := 4*(N:ℝ)/(3*(FarCut134.Mass K:ℝ)*FarCut134.Cutoff K)
def Eta (N:ℕ) : ℝ := 798/N

theorem actual_whole_normalized {N K:ℕ} {F:Finset (Finset ℤ)}
    (hF:Legal (Ground N) F) (hK:600≤K) (hN:63≤N) (hhi:N≤74320000)
    (hbad:∀S∈F,¬IsAP S) (hupper:∀S∈F,11*S.card≤N) (hlow:∀S∈F,3*K≤S.card) :
    (F.card:ℝ)/(N:ℝ)^2≤Nu K+G N K+Eta N := by
  let H:=F.filter (fun S=>¬HasNearAPCore K S)
  have hsub:H⊆F:=Finset.filter_subset _ _
  have hHL:Legal (Ground N) H:=⟨fun S hS=>hF.1 S (hsub hS),
    fun S hS T hT he=>hF.2 S (hsub hS) T (hsub hT) he⟩
  have hfar:=FarWeighted136.actual_far_normalized111 hHL (by omega:0<K) (by omega:0<N)
    (fun S hS=>hlow S (hsub hS)) (fun S hS=>(Finset.mem_filter.mp hS).2)
  have hwhole:=FiniteNear136.actual_sparse_whole_normalized hF hK hN hhi hbad hupper hlow
  change (H.card:ℝ)/(N:ℝ)^2≤G N K at hfar
  change (F.card:ℝ)/(N:ℝ)^2≤Nu K+Eta N+(H.card:ℝ)/(N:ℝ)^2 at hwhole
  linarith only [hfar,hwhole]

theorem actual_tail_normalized {N K:ℕ} {F:Finset (Finset ℤ)}
    (hF:Legal (Ground N) F) (hK:600≤K) (hN:63≤N) (hhi:N≤74320000)
    (hbad:∀S∈F,¬IsAP S) (hupper:∀S∈F,11*S.card≤N) :
    ((Tail F K).card:ℝ)/(N:ℝ)^2≤Nu K+G N K+Eta N := by
  have hsub:Tail F K⊆F:=Finset.filter_subset _ _
  have hTL:Legal (Ground N) (Tail F K):=⟨fun S hS=>hF.1 S (hsub hS),
    fun S hS T hT he=>hF.2 S (hsub hS) T (hsub hT) he⟩
  exact actual_whole_normalized hTL hK hN hhi (fun S hS=>hbad S (hsub hS))
    (fun S hS=>hupper S (hsub hS)) (fun S hS=>(Finset.mem_filter.mp hS).2)

theorem nu_scale (K h:ℕ) : Nu (Scale K h)=Nu K/(2:ℝ)^h := by
  simp only [Nu,Scale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem g_scale_le {N K:ℕ} (hK:0<K) (h:ℕ) :
    G N (Scale K h)≤G N K/(2:ℝ)^(3*h) :=
  by
    have he (n k:ℕ):G n k=(2/3:ℝ)*NearFar134.G n k:=by
      dsimp only [G,NearFar134.G]
      ring
    have hh:=mul_le_mul_of_nonneg_left (NearFar134.g_scale_le (N:=N) hK h)
      (by norm_num:0≤(2/3:ℝ))
    rw [he,he]
    simpa only [mul_div_assoc] using hh

theorem actual_scaled_tail_normalized {N K:ℕ} {F:Finset (Finset ℤ)}
    (hF:Legal (Ground N) F) (hK:600≤K) (hN:63≤N) (hhi:N≤74320000)
    (hbad:∀S∈F,¬IsAP S) (hupper:∀S∈F,11*S.card≤N) (h:ℕ) :
    ((Tail F (Scale K h)).card:ℝ)/(N:ℝ)^2≤
      Nu K/(2:ℝ)^h+G N K/(2:ℝ)^(3*h)+Eta N := by
  have hk:600≤Scale K h:=hK.trans (Nat.le_mul_of_pos_left K (by positivity))
  have hh:=actual_tail_normalized hF hk hN hhi hbad hupper
  rw [nu_scale] at hh
  have hg:=g_scale_le (N:=N) (by omega:0<K) h
  linarith only [hh,hg]

#print axioms actual_whole_normalized
#print axioms actual_tail_normalized
#print axioms nu_scale
#print axioms g_scale_le
#print axioms actual_scaled_tail_normalized
end
end JSP233.NearFar136
