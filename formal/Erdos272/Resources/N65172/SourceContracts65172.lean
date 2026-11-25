module

public import Erdos272.Arithmetic.N65172.CorrelatedChecks65172
public import Erdos272.Arithmetic.N65172.RunChecks65172
public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N65968.SourceContracts65968
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Arithmetic.N65172.UniformChecks65172

@[expose] public section

namespace JSP233.SourceContracts65172
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def node000 : CertifiedContract := SourceContracts65968.node000

def node001 : CertifiedContract := SourceContracts65968.node003

def node002 : CertifiedContract := SourceContracts65968.node009

def node003 : CertifiedContract := SourceContracts65968.node016

def node004 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks65172.plan004 CorrelatedChecks65172.checked004
  node003 (by decide) (by decide) (by decide)

def node005 : CertifiedContract := SourceContracts65968.node019

def node006 : CertifiedContract := SourceContracts65968.node021

def node007 : CertifiedContract := CorrelatedChord82427.chord
  CorrelatedChecks65172.plan007 CorrelatedChecks65172.checked007
  node006 (by decide) (by decide) (by decide)

def node008 : CertifiedContract := SourceContracts65968.node022

def node009 : CertifiedContract := SourceContracts65968.node023

def node010 : CertifiedContract := SourceContracts65968.node025

def node011 : CertifiedContract := SourceContracts65968.node027

def node012 : CertifiedContract := SourceContracts65968.node031

def node013 : CertifiedContract := SourceContracts65968.node035

def node014 : CertifiedContract := SourceContracts65968.node037

def node015 : CertifiedContract := SourceContracts65968.node039

def node016 : CertifiedContract := SourceContracts65968.node042

def node017 : CertifiedContract := SourceContracts65968.node044

def node018 : CertifiedContract := SourceContracts65968.node048

def node019 : CertifiedContract := SourceContracts65968.node052

def node020 : CertifiedContract := SourceContracts65968.node054

def node021 : CertifiedContract := SourceContracts65968.node056

def node022 : CertifiedContract := SourceContracts65968.node058

def node023 : CertifiedContract := SourceContracts65968.node060

def node024 : CertifiedContract := SourceContracts65968.node062

def node025 : CertifiedContract := SourceContracts65968.node064

def node026 : CertifiedContract := SourceContracts65968.node066

def node027 : CertifiedContract := SourceContracts65968.node067

def node028 : CertifiedContract := SourceContracts65968.node071

def node029 : CertifiedContract := SourceContracts65968.node072

def node030 : CertifiedContract := SourceContracts65968.node074

def node031 : CertifiedContract := SourceContracts65968.node076

def node032 : CertifiedContract := SourceContracts65968.node077

def node033 : CertifiedContract := SourceContracts65968.node082

def node034 : CertifiedContract := SourceContracts65968.node083

def node035 : CertifiedContract := SourceContracts65968.node084

def node036 : CertifiedContract := ⟨⟨203,1,12428⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks65172.checked036
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node037 : CertifiedContract := ⟨⟨204,1,12492⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks65172.checked037
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node038 : CertifiedContract := ⟨⟨205,1,12650⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks65172.checked038
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node039 : CertifiedContract := ⟨⟨206,1,12752⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks65172.checked039
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node040 : CertifiedContract := ⟨⟨207,1,12882⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks65172.checked040
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node041 : CertifiedContract := ⟨⟨208,1,12978⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks65172.checked041
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node042 : CertifiedContract := SourceContracts65968.node097

def node043 : CertifiedContract := SourceContracts65968.node101

def node044 : CertifiedContract := ⟨⟨240,1,17304⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks65172.checked044
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node045 : CertifiedContract := ⟨⟨241,1,17542⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks65172.checked045
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node046 : CertifiedContract := ⟨⟨242,1,17652⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks65172.checked046
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node047 : CertifiedContract := ⟨⟨243,1,17812⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks65172.checked047
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node048 : CertifiedContract := ⟨⟨244,1,17932⟩,
  UniformBridge84364.uniform_paid (by decide) (by decide)
    UniformChecks65172.checked048
    (fun S hS hnot => StrictPool86412.actual_U_le_pool S hS hnot)⟩

def node049 : CertifiedContract := SourceContracts65968.node108

def node050 : CertifiedContract := SourceContracts65968.node111

def node051 : CertifiedContract := SourceContracts65968.node112

def node052 : CertifiedContract := SourceContracts65968.node113

def node053 : CertifiedContract := SourceContracts65968.node114

def node054 : CertifiedContract := SourceContracts65968.node116

def node055 : CertifiedContract := SourceContracts65968.node120

def node056 : CertifiedContract := SourceContracts65968.node123

def node057 : CertifiedContract := SourceContracts65968.node124

def node058 : CertifiedContract := SourceContracts65968.node128

def node059 : CertifiedContract := SourceContracts65968.node131

def node060 : CertifiedContract := SourceContracts65968.node133

def node061 : CertifiedContract := SourceContracts65968.node137

def node062 : CertifiedContract := SourceContracts65968.node142

def node063 : CertifiedContract := SourceContracts65968.node144

def node064 : CertifiedContract := SourceContracts65968.node146

def node065 : CertifiedContract := SourceContracts65968.node147

def node066 : CertifiedContract := SourceContracts65968.node149

def node067 : CertifiedContract := SourceContracts65968.node150

def node068 : CertifiedContract := SourceContracts65968.node155

end
end JSP233.SourceContracts65172
