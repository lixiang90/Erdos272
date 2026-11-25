module

public import Erdos272.Geometry.N82427.PhaseHighSound82427
public import Erdos272.Geometry.N82427.PhaseHighFacts82427
public import Erdos272.Counting.N82427.ClassFast82427
public import Erdos272.Arithmetic.N82427.RowLightChecks82427G00
public import Erdos272.Arithmetic.N82427.RowLightChecks82427G01
public import Erdos272.Arithmetic.N82427.RowLightChecks82427G02
public import Erdos272.Arithmetic.N82427.RowLightChecks82427G03
public import Erdos272.Arithmetic.N82427.RowLightChecks82427G04
public import Erdos272.Arithmetic.N82427.RowLightChecks82427G05
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G00
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G01
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G02
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G03
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G04
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G05
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G06
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G07
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G08
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G09
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G10
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G11
public import Erdos272.Arithmetic.N82427.RowLightCertificates82427G12

@[expose] public section

namespace JSP233.RowLightSlope82427
open PhaseSlope82427 PhaseRampSlope82427 ActualCleanupEval208 ClassCount158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem facts {k : ℕ} (hk : k < 88) (b : CrossBandCredit208.Band) :
    BandFacts (row k).high (CleanupRows82427.data k).steps (At (row k) (length hk) b) (terms k b) ∧
    RampFacts (row k).high (CleanupRows82427.data k).steps (At (row k) (length hk) b) (ramps k b) := by
  interval_cases k
  · exact RowLightChecks82427G00.facts00 b
  · exact RowLightChecks82427G00.facts01 b
  · exact RowLightChecks82427G00.facts02 b
  · exact RowLightChecks82427G00.facts03 b
  · exact RowLightChecks82427G00.facts04 b
  · exact RowLightChecks82427G00.facts05 b
  · exact RowLightChecks82427G00.facts06 b
  · exact RowLightChecks82427G00.facts07 b
  · exact RowLightChecks82427G00.facts08 b
  · exact RowLightChecks82427G00.facts09 b
  · exact RowLightChecks82427G00.facts10 b
  · exact RowLightChecks82427G00.facts11 b
  · exact RowLightChecks82427G00.facts12 b
  · exact RowLightChecks82427G00.facts13 b
  · exact RowLightChecks82427G00.facts14 b
  · exact RowLightChecks82427G00.facts15 b
  · exact RowLightChecks82427G01.facts16 b
  · exact RowLightChecks82427G01.facts17 b
  · exact RowLightChecks82427G01.facts18 b
  · exact RowLightChecks82427G01.facts19 b
  · exact RowLightChecks82427G01.facts20 b
  · exact RowLightChecks82427G01.facts21 b
  · exact RowLightChecks82427G01.facts22 b
  · exact RowLightChecks82427G01.facts23 b
  · exact RowLightChecks82427G01.facts24 b
  · exact RowLightChecks82427G01.facts25 b
  · exact RowLightChecks82427G01.facts26 b
  · exact RowLightChecks82427G01.facts27 b
  · exact RowLightChecks82427G01.facts28 b
  · exact RowLightChecks82427G01.facts29 b
  · exact RowLightChecks82427G01.facts30 b
  · exact RowLightChecks82427G01.facts31 b
  · exact RowLightChecks82427G02.facts32 b
  · exact RowLightChecks82427G02.facts33 b
  · exact RowLightChecks82427G02.facts34 b
  · exact RowLightChecks82427G02.facts35 b
  · exact RowLightChecks82427G02.facts36 b
  · exact RowLightChecks82427G02.facts37 b
  · exact RowLightChecks82427G02.facts38 b
  · exact RowLightChecks82427G02.facts39 b
  · exact RowLightChecks82427G02.facts40 b
  · exact RowLightChecks82427G02.facts41 b
  · exact RowLightChecks82427G02.facts42 b
  · exact RowLightChecks82427G02.facts43 b
  · exact RowLightChecks82427G02.facts44 b
  · exact RowLightChecks82427G02.facts45 b
  · exact RowLightChecks82427G02.facts46 b
  · exact RowLightChecks82427G02.facts47 b
  · exact RowLightChecks82427G03.facts48 b
  · exact RowLightChecks82427G03.facts49 b
  · exact RowLightChecks82427G03.facts50 b
  · exact RowLightChecks82427G03.facts51 b
  · exact RowLightChecks82427G03.facts52 b
  · exact RowLightChecks82427G03.facts53 b
  · exact RowLightChecks82427G03.facts54 b
  · exact RowLightChecks82427G03.facts55 b
  · exact RowLightChecks82427G03.facts56 b
  · exact RowLightChecks82427G03.facts57 b
  · exact RowLightChecks82427G03.facts58 b
  · exact RowLightChecks82427G03.facts59 b
  · exact RowLightChecks82427G03.facts60 b
  · exact RowLightChecks82427G03.facts61 b
  · exact RowLightChecks82427G03.facts62 b
  · exact RowLightChecks82427G03.facts63 b
  · exact RowLightChecks82427G04.facts64 b
  · exact RowLightChecks82427G04.facts65 b
  · exact RowLightChecks82427G04.facts66 b
  · exact RowLightChecks82427G04.facts67 b
  · exact RowLightChecks82427G04.facts68 b
  · exact RowLightChecks82427G04.facts69 b
  · exact RowLightChecks82427G04.facts70 b
  · exact RowLightChecks82427G04.facts71 b
  · exact RowLightChecks82427G04.facts72 b
  · exact RowLightChecks82427G04.facts73 b
  · exact RowLightChecks82427G04.facts74 b
  · exact RowLightChecks82427G04.facts75 b
  · exact RowLightChecks82427G04.facts76 b
  · exact RowLightChecks82427G04.facts77 b
  · exact RowLightChecks82427G04.facts78 b
  · exact RowLightChecks82427G04.facts79 b
  · exact RowLightChecks82427G05.facts80 b
  · exact RowLightChecks82427G05.facts81 b
  · exact RowLightChecks82427G05.facts82 b
  · exact RowLightChecks82427G05.facts83 b
  · exact RowLightChecks82427G05.facts84 b
  · exact RowLightChecks82427G05.facts85 b
  · exact RowLightChecks82427G05.facts86 b
  · exact RowLightChecks82427G05.facts87 b
#print axioms facts

theorem classes {k : ℕ} (hk : k < 88) (b : CrossBandCredit208.Band) (t : Term) (ht : t ∈ terms k b) :
    Certificate t.p ((row k).low/(t.q*(t.q+1))) t.count := by
  have hc : t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p ((row k).low/(t.q*(t.q+1))) t.count=true := by
    interval_cases k
    · exact RowLightCertificates82427G00.classes00 b t ht
    · exact RowLightCertificates82427G00.classes01 b t ht
    · exact RowLightCertificates82427G00.classes02 b t ht
    · exact RowLightCertificates82427G00.classes03 b t ht
    · exact RowLightCertificates82427G01.classes04 b t ht
    · exact RowLightCertificates82427G01.classes05 b t ht
    · exact RowLightCertificates82427G01.classes06 b t ht
    · exact RowLightCertificates82427G01.classes07 b t ht
    · exact RowLightCertificates82427G02.classes08 b t ht
    · exact RowLightCertificates82427G02.classes09 b t ht
    · exact RowLightCertificates82427G02.classes10 b t ht
    · exact RowLightCertificates82427G02.classes11 b t ht
    · exact RowLightCertificates82427G03.classes12 b t ht
    · exact RowLightCertificates82427G03.classes13 b t ht
    · exact RowLightCertificates82427G03.classes14 b t ht
    · exact RowLightCertificates82427G03.classes15 b t ht
    · exact RowLightCertificates82427G03.classes16 b t ht
    · exact RowLightCertificates82427G03.classes17 b t ht
    · exact RowLightCertificates82427G03.classes18 b t ht
    · exact RowLightCertificates82427G03.classes19 b t ht
    · exact RowLightCertificates82427G04.classes20 b t ht
    · exact RowLightCertificates82427G04.classes21 b t ht
    · exact RowLightCertificates82427G04.classes22 b t ht
    · exact RowLightCertificates82427G04.classes23 b t ht
    · exact RowLightCertificates82427G04.classes24 b t ht
    · exact RowLightCertificates82427G04.classes25 b t ht
    · exact RowLightCertificates82427G04.classes26 b t ht
    · exact RowLightCertificates82427G04.classes27 b t ht
    · exact RowLightCertificates82427G05.classes28 b t ht
    · exact RowLightCertificates82427G05.classes29 b t ht
    · exact RowLightCertificates82427G05.classes30 b t ht
    · exact RowLightCertificates82427G05.classes31 b t ht
    · exact RowLightCertificates82427G05.classes32 b t ht
    · exact RowLightCertificates82427G05.classes33 b t ht
    · exact RowLightCertificates82427G05.classes34 b t ht
    · exact RowLightCertificates82427G05.classes35 b t ht
    · exact RowLightCertificates82427G06.classes36 b t ht
    · exact RowLightCertificates82427G06.classes37 b t ht
    · exact RowLightCertificates82427G06.classes38 b t ht
    · exact RowLightCertificates82427G06.classes39 b t ht
    · exact RowLightCertificates82427G06.classes40 b t ht
    · exact RowLightCertificates82427G06.classes41 b t ht
    · exact RowLightCertificates82427G06.classes42 b t ht
    · exact RowLightCertificates82427G06.classes43 b t ht
    · exact RowLightCertificates82427G07.classes44 b t ht
    · exact RowLightCertificates82427G07.classes45 b t ht
    · exact RowLightCertificates82427G07.classes46 b t ht
    · exact RowLightCertificates82427G07.classes47 b t ht
    · exact RowLightCertificates82427G07.classes48 b t ht
    · exact RowLightCertificates82427G07.classes49 b t ht
    · exact RowLightCertificates82427G07.classes50 b t ht
    · exact RowLightCertificates82427G07.classes51 b t ht
    · exact RowLightCertificates82427G08.classes52 b t ht
    · exact RowLightCertificates82427G08.classes53 b t ht
    · exact RowLightCertificates82427G08.classes54 b t ht
    · exact RowLightCertificates82427G08.classes55 b t ht
    · exact RowLightCertificates82427G08.classes56 b t ht
    · exact RowLightCertificates82427G08.classes57 b t ht
    · exact RowLightCertificates82427G08.classes58 b t ht
    · exact RowLightCertificates82427G08.classes59 b t ht
    · exact RowLightCertificates82427G09.classes60 b t ht
    · exact RowLightCertificates82427G09.classes61 b t ht
    · exact RowLightCertificates82427G09.classes62 b t ht
    · exact RowLightCertificates82427G09.classes63 b t ht
    · exact RowLightCertificates82427G09.classes64 b t ht
    · exact RowLightCertificates82427G09.classes65 b t ht
    · exact RowLightCertificates82427G09.classes66 b t ht
    · exact RowLightCertificates82427G09.classes67 b t ht
    · exact RowLightCertificates82427G10.classes68 b t ht
    · exact RowLightCertificates82427G10.classes69 b t ht
    · exact RowLightCertificates82427G10.classes70 b t ht
    · exact RowLightCertificates82427G10.classes71 b t ht
    · exact RowLightCertificates82427G10.classes72 b t ht
    · exact RowLightCertificates82427G10.classes73 b t ht
    · exact RowLightCertificates82427G10.classes74 b t ht
    · exact RowLightCertificates82427G10.classes75 b t ht
    · exact RowLightCertificates82427G11.classes76 b t ht
    · exact RowLightCertificates82427G11.classes77 b t ht
    · exact RowLightCertificates82427G11.classes78 b t ht
    · exact RowLightCertificates82427G11.classes79 b t ht
    · exact RowLightCertificates82427G11.classes80 b t ht
    · exact RowLightCertificates82427G11.classes81 b t ht
    · exact RowLightCertificates82427G11.classes82 b t ht
    · exact RowLightCertificates82427G11.classes83 b t ht
    · exact RowLightCertificates82427G12.classes84 b t ht
    · exact RowLightCertificates82427G12.classes85 b t ht
    · exact RowLightCertificates82427G12.classes86 b t ht
    · exact RowLightCertificates82427G12.classes87 b t ht
  exact ClassFast82427.sound hc.1 hc.2
#print axioms classes

theorem ramp_certificates {k : ℕ} (hk : k < 88) (b : CrossBandCredit208.Band) (t : RampTerm) (ht : t ∈ ramps k b) :
    Certificate t.p (RampLength (row k).low (At (row k) (length hk) b) t.p) t.count := by
  have hc : t.p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ ClassFastNumeric82427.check t.p (RampLength (row k).low (At (row k) (length hk) b) t.p) t.count=true := by
    interval_cases k
    · exact RowLightCertificates82427G00.ramps00 b t ht
    · exact RowLightCertificates82427G00.ramps01 b t ht
    · exact RowLightCertificates82427G00.ramps02 b t ht
    · exact RowLightCertificates82427G00.ramps03 b t ht
    · exact RowLightCertificates82427G01.ramps04 b t ht
    · exact RowLightCertificates82427G01.ramps05 b t ht
    · exact RowLightCertificates82427G01.ramps06 b t ht
    · exact RowLightCertificates82427G01.ramps07 b t ht
    · exact RowLightCertificates82427G02.ramps08 b t ht
    · exact RowLightCertificates82427G02.ramps09 b t ht
    · exact RowLightCertificates82427G02.ramps10 b t ht
    · exact RowLightCertificates82427G02.ramps11 b t ht
    · exact RowLightCertificates82427G03.ramps12 b t ht
    · exact RowLightCertificates82427G03.ramps13 b t ht
    · exact RowLightCertificates82427G03.ramps14 b t ht
    · exact RowLightCertificates82427G03.ramps15 b t ht
    · exact RowLightCertificates82427G03.ramps16 b t ht
    · exact RowLightCertificates82427G03.ramps17 b t ht
    · exact RowLightCertificates82427G03.ramps18 b t ht
    · exact RowLightCertificates82427G03.ramps19 b t ht
    · exact RowLightCertificates82427G04.ramps20 b t ht
    · exact RowLightCertificates82427G04.ramps21 b t ht
    · exact RowLightCertificates82427G04.ramps22 b t ht
    · exact RowLightCertificates82427G04.ramps23 b t ht
    · exact RowLightCertificates82427G04.ramps24 b t ht
    · exact RowLightCertificates82427G04.ramps25 b t ht
    · exact RowLightCertificates82427G04.ramps26 b t ht
    · exact RowLightCertificates82427G04.ramps27 b t ht
    · exact RowLightCertificates82427G05.ramps28 b t ht
    · exact RowLightCertificates82427G05.ramps29 b t ht
    · exact RowLightCertificates82427G05.ramps30 b t ht
    · exact RowLightCertificates82427G05.ramps31 b t ht
    · exact RowLightCertificates82427G05.ramps32 b t ht
    · exact RowLightCertificates82427G05.ramps33 b t ht
    · exact RowLightCertificates82427G05.ramps34 b t ht
    · exact RowLightCertificates82427G05.ramps35 b t ht
    · exact RowLightCertificates82427G06.ramps36 b t ht
    · exact RowLightCertificates82427G06.ramps37 b t ht
    · exact RowLightCertificates82427G06.ramps38 b t ht
    · exact RowLightCertificates82427G06.ramps39 b t ht
    · exact RowLightCertificates82427G06.ramps40 b t ht
    · exact RowLightCertificates82427G06.ramps41 b t ht
    · exact RowLightCertificates82427G06.ramps42 b t ht
    · exact RowLightCertificates82427G06.ramps43 b t ht
    · exact RowLightCertificates82427G07.ramps44 b t ht
    · exact RowLightCertificates82427G07.ramps45 b t ht
    · exact RowLightCertificates82427G07.ramps46 b t ht
    · exact RowLightCertificates82427G07.ramps47 b t ht
    · exact RowLightCertificates82427G07.ramps48 b t ht
    · exact RowLightCertificates82427G07.ramps49 b t ht
    · exact RowLightCertificates82427G07.ramps50 b t ht
    · exact RowLightCertificates82427G07.ramps51 b t ht
    · exact RowLightCertificates82427G08.ramps52 b t ht
    · exact RowLightCertificates82427G08.ramps53 b t ht
    · exact RowLightCertificates82427G08.ramps54 b t ht
    · exact RowLightCertificates82427G08.ramps55 b t ht
    · exact RowLightCertificates82427G08.ramps56 b t ht
    · exact RowLightCertificates82427G08.ramps57 b t ht
    · exact RowLightCertificates82427G08.ramps58 b t ht
    · exact RowLightCertificates82427G08.ramps59 b t ht
    · exact RowLightCertificates82427G09.ramps60 b t ht
    · exact RowLightCertificates82427G09.ramps61 b t ht
    · exact RowLightCertificates82427G09.ramps62 b t ht
    · exact RowLightCertificates82427G09.ramps63 b t ht
    · exact RowLightCertificates82427G09.ramps64 b t ht
    · exact RowLightCertificates82427G09.ramps65 b t ht
    · exact RowLightCertificates82427G09.ramps66 b t ht
    · exact RowLightCertificates82427G09.ramps67 b t ht
    · exact RowLightCertificates82427G10.ramps68 b t ht
    · exact RowLightCertificates82427G10.ramps69 b t ht
    · exact RowLightCertificates82427G10.ramps70 b t ht
    · exact RowLightCertificates82427G10.ramps71 b t ht
    · exact RowLightCertificates82427G10.ramps72 b t ht
    · exact RowLightCertificates82427G10.ramps73 b t ht
    · exact RowLightCertificates82427G10.ramps74 b t ht
    · exact RowLightCertificates82427G10.ramps75 b t ht
    · exact RowLightCertificates82427G11.ramps76 b t ht
    · exact RowLightCertificates82427G11.ramps77 b t ht
    · exact RowLightCertificates82427G11.ramps78 b t ht
    · exact RowLightCertificates82427G11.ramps79 b t ht
    · exact RowLightCertificates82427G11.ramps80 b t ht
    · exact RowLightCertificates82427G11.ramps81 b t ht
    · exact RowLightCertificates82427G11.ramps82 b t ht
    · exact RowLightCertificates82427G11.ramps83 b t ht
    · exact RowLightCertificates82427G12.ramps84 b t ht
    · exact RowLightCertificates82427G12.ramps85 b t ht
    · exact RowLightCertificates82427G12.ramps86 b t ht
    · exact RowLightCertificates82427G12.ramps87 b t ht
  exact ClassFast82427.sound hc.1 hc.2
#print axioms ramp_certificates

theorem slope_eq {k : ℕ} (hk : k < 88) :
    PhaseRampSlope82427.RowSlope (row k) (length hk) (terms k) (ramps k)=slope k := by
  interval_cases k
  · exact RowLightChecks82427G00.slope00
  · exact RowLightChecks82427G00.slope01
  · exact RowLightChecks82427G00.slope02
  · exact RowLightChecks82427G00.slope03
  · exact RowLightChecks82427G00.slope04
  · exact RowLightChecks82427G00.slope05
  · exact RowLightChecks82427G00.slope06
  · exact RowLightChecks82427G00.slope07
  · exact RowLightChecks82427G00.slope08
  · exact RowLightChecks82427G00.slope09
  · exact RowLightChecks82427G00.slope10
  · exact RowLightChecks82427G00.slope11
  · exact RowLightChecks82427G00.slope12
  · exact RowLightChecks82427G00.slope13
  · exact RowLightChecks82427G00.slope14
  · exact RowLightChecks82427G00.slope15
  · exact RowLightChecks82427G01.slope16
  · exact RowLightChecks82427G01.slope17
  · exact RowLightChecks82427G01.slope18
  · exact RowLightChecks82427G01.slope19
  · exact RowLightChecks82427G01.slope20
  · exact RowLightChecks82427G01.slope21
  · exact RowLightChecks82427G01.slope22
  · exact RowLightChecks82427G01.slope23
  · exact RowLightChecks82427G01.slope24
  · exact RowLightChecks82427G01.slope25
  · exact RowLightChecks82427G01.slope26
  · exact RowLightChecks82427G01.slope27
  · exact RowLightChecks82427G01.slope28
  · exact RowLightChecks82427G01.slope29
  · exact RowLightChecks82427G01.slope30
  · exact RowLightChecks82427G01.slope31
  · exact RowLightChecks82427G02.slope32
  · exact RowLightChecks82427G02.slope33
  · exact RowLightChecks82427G02.slope34
  · exact RowLightChecks82427G02.slope35
  · exact RowLightChecks82427G02.slope36
  · exact RowLightChecks82427G02.slope37
  · exact RowLightChecks82427G02.slope38
  · exact RowLightChecks82427G02.slope39
  · exact RowLightChecks82427G02.slope40
  · exact RowLightChecks82427G02.slope41
  · exact RowLightChecks82427G02.slope42
  · exact RowLightChecks82427G02.slope43
  · exact RowLightChecks82427G02.slope44
  · exact RowLightChecks82427G02.slope45
  · exact RowLightChecks82427G02.slope46
  · exact RowLightChecks82427G02.slope47
  · exact RowLightChecks82427G03.slope48
  · exact RowLightChecks82427G03.slope49
  · exact RowLightChecks82427G03.slope50
  · exact RowLightChecks82427G03.slope51
  · exact RowLightChecks82427G03.slope52
  · exact RowLightChecks82427G03.slope53
  · exact RowLightChecks82427G03.slope54
  · exact RowLightChecks82427G03.slope55
  · exact RowLightChecks82427G03.slope56
  · exact RowLightChecks82427G03.slope57
  · exact RowLightChecks82427G03.slope58
  · exact RowLightChecks82427G03.slope59
  · exact RowLightChecks82427G03.slope60
  · exact RowLightChecks82427G03.slope61
  · exact RowLightChecks82427G03.slope62
  · exact RowLightChecks82427G03.slope63
  · exact RowLightChecks82427G04.slope64
  · exact RowLightChecks82427G04.slope65
  · exact RowLightChecks82427G04.slope66
  · exact RowLightChecks82427G04.slope67
  · exact RowLightChecks82427G04.slope68
  · exact RowLightChecks82427G04.slope69
  · exact RowLightChecks82427G04.slope70
  · exact RowLightChecks82427G04.slope71
  · exact RowLightChecks82427G04.slope72
  · exact RowLightChecks82427G04.slope73
  · exact RowLightChecks82427G04.slope74
  · exact RowLightChecks82427G04.slope75
  · exact RowLightChecks82427G04.slope76
  · exact RowLightChecks82427G04.slope77
  · exact RowLightChecks82427G04.slope78
  · exact RowLightChecks82427G04.slope79
  · exact RowLightChecks82427G05.slope80
  · exact RowLightChecks82427G05.slope81
  · exact RowLightChecks82427G05.slope82
  · exact RowLightChecks82427G05.slope83
  · exact RowLightChecks82427G05.slope84
  · exact RowLightChecks82427G05.slope85
  · exact RowLightChecks82427G05.slope86
  · exact RowLightChecks82427G05.slope87
#print axioms slope_eq

theorem cap_eq {k : ℕ} (hk : k < 88) : (PhaseNumeric82427.data k).cap=cap k := by
  interval_cases k <;> rfl
#print axioms cap_eq

theorem slope_bound {k N : ℕ} (hk : k < 88) (hlo : (CleanupRows82427.data k).row.low ≤ N)
    (hhi : N ≤ (CleanupRows82427.data k).row.high)
    (_hchecked : CleanupEval208.ChunkFacts (CleanupMachineSound208.toRow (CleanupRows82427.data k).row)
      1 (CleanupRows82427.data k).steps (CleanupMachineSound208.toTotals (CleanupRows82427.data k).total)) :
    PhaseSlope82427.RowLight (row k) (length hk) (CleanupRows82427.data k).steps N+
      slope k*((CleanupRows82427.data k).row.high-N) ≤ cap k := by
  have ha := PhaseRampSlope82427.row_affine (terms:=terms k) (ramps:=ramps k) hlo hhi
    (fun b => (facts hk b).1) (fun b => (facts hk b).2) (classes hk) (ramp_certificates hk)
  rw [slope_eq hk] at ha
  have hh := PhaseHighFacts82427.bound hk
  rw [←PhaseHighSound82427.high_value hk,cap_eq hk] at hh
  exact ha.trans hh
#print axioms slope_bound
end
end JSP233.RowLightSlope82427
