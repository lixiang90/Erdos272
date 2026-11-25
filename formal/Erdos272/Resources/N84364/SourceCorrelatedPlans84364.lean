module

public import Erdos272.Resources.N86412.SourceCorrelated86412
public import Erdos272.Resources.N84364.SourceOld84364
public import Erdos272.Resources.N84364.SourceStrictRunContracts84364
public import Erdos272.Arithmetic.N84364.SourceQueryData84364
public import Erdos272.Arithmetic.N84364.SourceDynamicData84364

@[expose] public section

namespace JSP233.SourceCorrelatedPlans84364
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def standard00 : CertifiedContract :=
  SourceCorrelated86412.standard (SourceQueryData84364.query 0)
    (SourceQueryData84364.conditions (by decide)) (SourceOld84364.old 1)
    (by decide) (by decide) (by decide)

def standard01 : CertifiedContract :=
  SourceCorrelated86412.standard (SourceQueryData84364.query 1)
    (SourceQueryData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def standard02 : CertifiedContract :=
  SourceCorrelated86412.standard (SourceQueryData84364.query 2)
    (SourceQueryData84364.conditions (by decide)) (SourceOld84364.old 4)
    (by decide) (by decide) (by decide)

def standard03 : CertifiedContract :=
  SourceCorrelated86412.standard (SourceQueryData84364.query 3)
    (SourceQueryData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def standard04 : CertifiedContract :=
  SourceCorrelated86412.standard (SourceQueryData84364.query 4)
    (SourceQueryData84364.conditions (by decide)) (SourceOld84364.old 4)
    (by decide) (by decide) (by decide)

def standard (i : ℕ) : CertifiedContract :=
  match i with
  | 0 => standard00
  | 1 => standard01
  | 2 => standard02
  | 3 => standard03
  | 4 => standard04
  | _ => standard00

def dynamic00 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 0)
    (SourceDynamicData84364.conditions (by decide)) (SourceStrictRunContracts84364.run 0 (by decide))
    (by decide) (by decide) (by decide)

def dynamic01 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 1)
    (SourceDynamicData84364.conditions (by decide)) (SourceStrictRunContracts84364.run 1 (by decide))
    (by decide) (by decide) (by decide)

def dynamic02 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 2)
    (SourceDynamicData84364.conditions (by decide)) (SourceStrictRunContracts84364.run 2 (by decide))
    (by decide) (by decide) (by decide)

def dynamic03 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 3)
    (SourceDynamicData84364.conditions (by decide)) (SourceStrictRunContracts84364.run 3 (by decide))
    (by decide) (by decide) (by decide)

def dynamic04 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 4)
    (SourceDynamicData84364.conditions (by decide)) (SourceStrictRunContracts84364.run 4 (by decide))
    (by decide) (by decide) (by decide)

def dynamic05 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 5)
    (SourceDynamicData84364.conditions (by decide)) (SourceStrictRunContracts84364.run 5 (by decide))
    (by decide) (by decide) (by decide)

def dynamic06 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 6)
    (SourceDynamicData84364.conditions (by decide)) (SourceStrictRunContracts84364.run 6 (by decide))
    (by decide) (by decide) (by decide)

def dynamic07 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 7)
    (SourceDynamicData84364.conditions (by decide)) (SourceStrictRunContracts84364.run 7 (by decide))
    (by decide) (by decide) (by decide)

def dynamic08 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 8)
    (SourceDynamicData84364.conditions (by decide)) (SourceStrictRunContracts84364.run 8 (by decide))
    (by decide) (by decide) (by decide)

def dynamic09 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 9)
    (SourceDynamicData84364.conditions (by decide)) (SourceStrictRunContracts84364.run 9 (by decide))
    (by decide) (by decide) (by decide)

def dynamic10 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 10)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def dynamic11 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 11)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def dynamic12 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 12)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def dynamic13 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 13)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def dynamic14 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 14)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def dynamic15 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 15)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def dynamic16 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 16)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def dynamic17 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 17)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def dynamic18 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 18)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def dynamic19 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 19)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 2)
    (by decide) (by decide) (by decide)

def dynamic20 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 20)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 9)
    (by decide) (by decide) (by decide)

def dynamic21 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 21)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 4)
    (by decide) (by decide) (by decide)

def dynamic22 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 22)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 4)
    (by decide) (by decide) (by decide)

def dynamic23 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 23)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 4)
    (by decide) (by decide) (by decide)

def dynamic24 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 24)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 4)
    (by decide) (by decide) (by decide)

def dynamic25 : CertifiedContract :=
  SourceCorrelated86412.dynamic (SourceDynamicData84364.query 25)
    (SourceDynamicData84364.conditions (by decide)) (SourceOld84364.old 4)
    (by decide) (by decide) (by decide)

def dynamic (i : ℕ) : CertifiedContract :=
  match i with
  | 0 => dynamic00
  | 1 => dynamic01
  | 2 => dynamic02
  | 3 => dynamic03
  | 4 => dynamic04
  | 5 => dynamic05
  | 6 => dynamic06
  | 7 => dynamic07
  | 8 => dynamic08
  | 9 => dynamic09
  | 10 => dynamic10
  | 11 => dynamic11
  | 12 => dynamic12
  | 13 => dynamic13
  | 14 => dynamic14
  | 15 => dynamic15
  | 16 => dynamic16
  | 17 => dynamic17
  | 18 => dynamic18
  | 19 => dynamic19
  | 20 => dynamic20
  | 21 => dynamic21
  | 22 => dynamic22
  | 23 => dynamic23
  | 24 => dynamic24
  | 25 => dynamic25
  | _ => dynamic00

end
end JSP233.SourceCorrelatedPlans84364
