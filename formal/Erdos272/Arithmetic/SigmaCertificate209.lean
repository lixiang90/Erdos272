module

public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SigmaBaseActual209
public import Erdos272.Arithmetic.SigmaValue209
public import Erdos272.Arithmetic.SigmaWChecked209
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace JSP233.SigmaCertificate209
set_option maxHeartbeats 0
open FactorFullData209

theorem factor_sound_all (n : Nat) (hn : 2≤n) (hnH : n≤1670000) :
    (factor n=0 → n.Prime) ∧
    (factor n≠0 → (factor n).Prime ∧ factor n∣n) := by
  by_cases hhigh : 32753<n
  · exact FactorFullCertificate209.factor_sound n hhigh hnH
  · exact LowFactorSound209.sound n hn (by omega)

theorem sigma_correct (n : Nat) (hn : n≤1670000) :
    SigmaValue209.value n=SigmaSieve209.sigmaOne n :=
  SigmaValue209.correct SigmaBaseActual209.correct FactorFullCertificate209.factor_sound n hn

theorem actual_good (s : Nat) (hs : 31≤s) (hsN : s≤1670000) :
    SigmaPrefix209.Good s (SigmaPrefix209.W s) := by
  have hh := SigmaWChecked209.good s hs hsN
  have heq := SigmaPrefix209.weighted_congr (s:=s)
    (fun n hn => sigma_correct n (hn.trans hsN))
  rw [heq] at hh
  exact hh

theorem actual_bound (s : Nat) (hs : 31≤s) (hsN : s≤1670000) :
    (SigmaPrefix209.W s : Real)≤
      (1644934067/1000000000 : Real)*(s:Real)^3/6-
      (s:Real)^2/4+(14/5:Real)*s :=
  SigmaPrefix209.actual_bound
    (fun n hn => sigma_correct n (hn.trans hsN)) (SigmaWChecked209.good s hs hsN)

#print axioms factor_sound_all
#print axioms sigma_correct
#print axioms actual_good
#print axioms actual_bound
end JSP233.SigmaCertificate209
